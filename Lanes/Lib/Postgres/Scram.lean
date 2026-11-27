/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Lib.Crypto.Pbkdf2
public import Lanes.Lib.Crypto.Md5
public import Lanes.Lib.Encoding.Base64

/-!
What a client computes to authenticate to PostgreSQL: the MD5 digest it answers `md5` with, and
SCRAM-SHA-256 (RFC 5802, RFC 7677) without channel binding, as pure functions of the password,
the client's nonce and what the server sent.

The nonce is drawn by the IO that runs the connection and passed in, so that these stay
functions. The client does not trust the server before the server has proved it knows the
password: `Scram.respond` gives, with the client's last message, the signature the server must
answer with, and `Scram.verify` compares the two with libsodium's comparison. Tested against RFC
7677's example and against libpq's messages recorded from a real server (`Tests/Postgres.lean`).
-/

@[expose] public section

namespace Lanes.Postgres

/-- `md5` followed by the hex of `md5 (hex (md5 (password ++ user)) ++ salt)`, as PostgreSQL
asks for it. -/
def md5Answer (user password : String) (salt : ByteArray) : String :=
  let inner := Bytes.hex (Md5.hash (password ++ user).toUTF8)
  "md5" ++ Bytes.hex (Md5.hash (inner.toUTF8 ++ salt))

namespace Scram

def mechanism : String := "SCRAM-SHA-256"

/-- A name in a SCRAM message, with `=` and `,` escaped. PostgreSQL ignores it and uses the
user of the start-up message, so libpq sends it empty. -/
def saslName (s : String) : String :=
  String.join (s.toList.map fun c => if c = '=' then "=3D" else if c = ',' then "=2C" else c.toString)

def firstBare (user nonce : String) : String := "n=" ++ saslName user ++ ",r=" ++ nonce

/-- The client's first message: no channel binding (`n,,`), then the bare part. -/
def first (user nonce : String) : String := "n,," ++ firstBare user nonce

/-- What the server's first message says. -/
structure ServerFirst where
  nonce : String
  salt : ByteArray
  iterations : Nat

def field (key : Char) (s : String) : Option String :=
  match s.toList with
  | k :: '=' :: rest => if k = key then some (String.ofList rest) else none
  | _ => none

/-- `r=…,s=…,i=…`, possibly followed by extensions, which are ignored; a mandatory extension
(`m=`) first is refused, as RFC 5802 says. -/
def parseServerFirst (s : String) : Option ServerFirst := do
  match s.splitOn "," with
  | r :: salt :: i :: _ =>
    let nonce ← field 'r' r
    let salt ← field 's' salt >>= Base64.decode .std
    let iterations ← field 'i' i >>= String.toNat?
    pure { nonce, salt, iterations }
  | _ => none

inductive Refusal where
  /-- The server's nonce does not extend the client's, or is the client's alone. -/
  | nonce
  /-- No iterations, or more than the configuration allows. -/
  | iterations
  /-- The server's first message is not one. -/
  | malformed
  deriving DecidableEq, Repr

/-- What the client answers to the server's first message `serverFirst`: its last message, and
the signature the server's last must carry. At most `iterations_max` iterations are computed, so
that a server cannot make the client work without bound (rule 2.6). -/
def respond (user password clientNonce serverFirst : String) (iterations_max : Nat) :
    Except Refusal (String × ByteArray) :=
  match parseServerFirst serverFirst with
  | none => .error .malformed
  | some sf =>
    if !(clientNonce.isPrefixOf sf.nonce) || sf.nonce.length ≤ clientNonce.length then
      .error .nonce
    else if sf.iterations = 0 || iterations_max < sf.iterations then .error .iterations
    else
      let salted := Pbkdf2.derive password.toUTF8 sf.salt sf.iterations 32
      let clientKey := hmac salted "Client Key".toUTF8
      let storedKey := Sha256.hash clientKey
      let withoutProof := "c=biws,r=" ++ sf.nonce
      let auth := firstBare user clientNonce ++ "," ++ serverFirst ++ "," ++ withoutProof
      let proof := Pbkdf2.xor clientKey (hmac storedKey auth.toUTF8)
      let serverKey := hmac salted "Server Key".toUTF8
      .ok (withoutProof ++ ",p=" ++ Base64.encode .std proof, hmac serverKey auth.toUTF8)

/-- Whether the server's last message `v=…` carries the signature expected. An error `e=…` or
anything else does not. -/
def verify (expected : ByteArray) (serverFinal : String) : Bool :=
  match (field 'v' serverFinal).bind (Base64.decode .std) with
  | some signature => Bytes.same expected signature
  | none => false

theorem respond_nonce {user password clientNonce serverFirst : String} {iterations_max : Nat}
    {sf : ServerFirst} (h : parseServerFirst serverFirst = some sf)
    (hn : clientNonce.isPrefixOf sf.nonce = false) :
    respond user password clientNonce serverFirst iterations_max = .error .nonce := by
  simp [respond, h, hn]

theorem respond_iterations {user password clientNonce serverFirst : String} {iterations_max : Nat}
    {sf : ServerFirst} (h : parseServerFirst serverFirst = some sf)
    (hn : clientNonce.isPrefixOf sf.nonce = true) (hl : clientNonce.length < sf.nonce.length)
    (hi : iterations_max < sf.iterations) :
    respond user password clientNonce serverFirst iterations_max = .error .iterations := by
  simp [respond, h, hn, show ¬ sf.nonce.length ≤ clientNonce.length by omega, hi]

end Scram

end Lanes.Postgres
