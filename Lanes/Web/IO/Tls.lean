/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std.Async
public import Lanes.Lib.Net.Ip

/-!
A TLS client session, from OpenSSL (`native/tls.c`). It does no IO: what arrives from the server
is handed to `feed`, and what `take` gives is sent to it, so it sits under any socket. The
server's certificate is always verified, and so is the name it is for, except by
`Session.startChain`, which PostgreSQL's `require` asks for. It may offer ALPN protocols, and
gives the server's certificate for channel binding. TLS 1.2 or 1.3.
-/

@[expose] public section

namespace Lanes.Tls

/-- The certificates a server's must chain to. -/
inductive Trust where
  /-- The operating system's: the file `SSL_CERT_FILE` names, if it is set, or else the first of
  `systemFiles` there is. -/
  | system
  /-- Those in a PEM file, and no others. -/
  | file (path : System.FilePath)
  deriving DecidableEq, Repr, Hashable

/-- Where systems keep their trusted certificates, as Go's `crypto/x509` looks for them: Debian,
Ubuntu and Alpine; Fedora and RHEL; OpenSUSE; OpenELEC; CentOS and RHEL 7 and Amazon Linux. Then
Homebrew's bundle on macOS, before `/etc/ssl/cert.pem`, which macOS and the BSDs have but which
macOS does not keep up to date with its keychain: on GitHub's macOS runners it lacks the root
example.com chains to. The OpenSSL that Lean ships was built to look in none of them. -/
def systemFiles : List System.FilePath :=
  ["/etc/ssl/certs/ca-certificates.crt", "/etc/pki/tls/certs/ca-bundle.crt",
    "/etc/ssl/ca-bundle.pem", "/etc/pki/tls/cacert.pem",
    "/etc/pki/ca-trust/extracted/pem/tls-ca-bundle.pem",
    "/opt/homebrew/etc/ca-certificates/cert.pem", "/usr/local/etc/ca-certificates/cert.pem",
    "/etc/ssl/cert.pem"]

/-- The file of trusted certificates `trust` names. -/
def Trust.path : Trust → IO System.FilePath
  | .file path => pure path
  | .system => do
    if let some named ← IO.getEnv "SSL_CERT_FILE" then
      unless named.isEmpty do return named
    for path in systemFiles do
      if ← path.pathExists then return path
    throw (.userError "tls: no file of trusted certificates in any of the usual places")

opaque SessionImpl : NonemptyType

def Session : Type := SessionImpl.type

instance : Nonempty Session := SessionImpl.property

@[extern "lanes_tls_new"]
private opaque new (trust host : @& String) (ip check : Bool) (alpn : @& ByteArray) : IO Session

/-- ALPN protocols as TLS sends them, each after its length in a byte; none if one is empty or
longer than 255 bytes. -/
def alpnWire (protocols : List String) : Option ByteArray :=
  protocols.foldlM (init := ByteArray.empty) fun acc p =>
    let bytes := p.toUTF8
    if bytes.size = 0 ∨ 255 < bytes.size then none else some (acc.push bytes.size.toUInt8 ++ bytes)

/-- Whether `host` is an IPv4 or IPv6 address: its certificate is checked for the address, and it
is sent as no SNI, which RFC 6066 allows only for a name. -/
def isAddress (host : String) : Bool :=
  (Ip.parse host).isSome

@[no_expose]
private def begin (trust : Trust) (host : String) (check : Bool) (alpn : List String) : IO Session := do
  let some protocols := alpnWire alpn | throw (.userError "tls: an ALPN protocol is empty or too long")
  new (← trust.path).toString host (isAddress host) check protocols

/-- A session with the server `host`, a name or an IP address, whose certificate must chain to
`trust` and be for `host`, offering the ALPN protocols `alpn`. A name is also sent as SNI. -/
@[no_expose]
def Session.start (trust : Trust) (host : String) (alpn : List String := []) : IO Session :=
  begin trust host true alpn

/-- A session whose certificate must chain to `trust`, for whatever name: what PostgreSQL calls
`require` (and libpq `verify-ca`). Anyone with a certificate from an authority of `trust` can
answer, so `trust` should hold only the server's own authority. A name is sent as SNI. -/
@[no_expose]
def Session.startChain (trust : Trust) (host : String) (alpn : List String := []) : IO Session :=
  begin trust host false alpn

/-- The server's certificate, as DER; empty before the handshake. -/
@[extern "lanes_tls_peer"]
opaque Session.peer (s : @& Session) : IO ByteArray

/-- The ALPN protocol the server chose; empty if none. -/
@[extern "lanes_tls_alpn"]
opaque Session.alpn (s : @& Session) : IO ByteArray

/-- Bytes that arrived from the server. -/
@[extern "lanes_tls_feed"]
opaque Session.feed (s : @& Session) (bytes : @& ByteArray) : IO Unit

/-- Every byte to send to the server that has not been taken. -/
@[extern "lanes_tls_take"]
opaque Session.take (s : @& Session) : IO ByteArray

/-- Whether the handshake is done; it is not while it waits for bytes. It throws, with OpenSSL's
reason, when the server cannot be trusted or the handshake fails. -/
@[extern "lanes_tls_handshake"]
opaque Session.handshake (s : @& Session) : IO Bool

/-- Bytes to send, after the handshake. -/
@[extern "lanes_tls_write"]
opaque Session.write (s : @& Session) (bytes : @& ByteArray) : IO Unit

/-- At most `max` bytes the server sent, decrypted: none while more must arrive. -/
@[extern "lanes_tls_read"]
opaque Session.read (s : @& Session) (max : UInt32) : IO ByteArray

/-- Whether the server said it closes (`close_notify`), so that what it sent is all of it. The
end of the connection without it may be an attacker's. -/
@[extern "lanes_tls_closed"]
opaque Session.closed (s : @& Session) : IO Bool

/-- Say this side closes, in what `take` gives next. -/
@[extern "lanes_tls_shutdown"]
opaque Session.shutdown (s : @& Session) : IO Unit

/-- Everything that can be decrypted now. -/
def Session.readAll (s : Session) : IO ByteArray := do
  let mut all := ByteArray.empty
  repeat
    let piece ← s.read 16384
    if piece.isEmpty then break
    all := all ++ piece
  return all

end Lanes.Tls
