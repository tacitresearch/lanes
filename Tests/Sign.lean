/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Signature

/-!
Signatures made by OpenSSL with a private key (`native/sign.c`, `Lanes/Lib/Crypto/Sign.lean`).
The keys are published ones, never made up: RFC 9500 §2.1's RSA key of 2048 bits, as Go 1.24
keeps it in `crypto/rsa/example_test.go`, and RFC 6979 A.2.5's P-256 key, written as PEM from
its secret; both are in `oracles/botocore/keys/`, labelled `TESTING KEY` as Go labels them so
that no scanner takes them for secrets. RFC 6979's signatures of "sample" and "test" with SHA-256,
as Go's `crypto/ecdsa` tests carry them, are made exactly. The RSA signatures check under the
public half, by the binding and the Lean reference. With the `openssl` command: RSA signatures
are byte for byte those `openssl dgst -sha1 -sign` and `-sha256 -sign` make, ECDSA signatures
check under `openssl dgst -verify`, the public key's PEM is `openssl pkey -pubout`'s, and keys
that are encrypted, too small, on another curve or of another kind are refused.
-/

namespace Tests.Sign

open Lanes

def testing (pem : String) : ByteArray := (pem.replace "TESTING KEY" "PRIVATE KEY").toUTF8

def rsaPem : ByteArray := testing (include_str "../oracles/botocore/keys/rsa2048.pem")

def p256Pem : ByteArray := testing (include_str "../oracles/botocore/keys/p256.pem")

def hex (s : String) : ByteArray := (Bytes.unhex? s.toLower).getD .empty

/-- RFC 6979 A.2.5: the public point of the key, and `r ‖ s` of "sample" and "test" with SHA-256. -/
def ux : String := "60FED4BA255A9D31C961EB74C6356D68C049B8923B61FA6CE669622E60F29FB6"
def uy : String := "7903FE1008B8BC99A41AE9E95628BC64F2F1B20C2D7E9F5177A3C294D4462299"
def sample : String := "EFD48B2AACB6A8FD1140DD9CD45E81D69D2C877B56AAF991C34D0EA84EAF3716\
  F7CB1C942D657C41D436C7A1B6E29F65F3E900DBB9AFF4064DC4AB2F843ACDA8"
def test : String := "F1ABB023518351CD71D881567B1EA663ED3EFCF6C5132B354F28D3B0B7D38367\
  019F4113742A2B14BD25926B49C649155F267E60D3814B4C0CC84250E46F0083"

def rsa : Option SigningKey := (SigningKey.ofPem rsaPem).toOption
def p256 : Option SigningKey := (SigningKey.ofPem p256Pem).toOption

/-- The signature of `msg` by `key` is RFC 6979's `r ‖ s`, in DER, and checks. -/
def rfc6979 (key : SigningKey) (msg rs : String) : Bool :=
  key.sign .sha256 msg.toUTF8 == key.publicKey.derSignature (hex rs)
    && key.publicKey.verifies msg.toUTF8 (hex rs)

def tests : List (String × Bool) :=
  [ ("sign: RFC 9500's RSA key and RFC 6979's P-256 key are read, the latter with its public point",
      (rsa.any fun k => k.publicKey matches .rsa ..)
        && p256.any fun k => k.publicKey.spki == (PublicKey.p256 (hex ux) (hex uy)).spki),
    ("sign: ECDSA with SHA-256 makes RFC 6979's signatures of \"sample\" and \"test\"",
      p256.any fun k => rfc6979 k "sample" sample && rfc6979 k "test" test),
    ("sign: RSA with SHA-256 checks under the public half, by the binding and the Lean reference",
      rsa.any fun k => match k.publicKey, k.sign .sha256 "a policy".toUTF8 with
        | .rsa n e, some sig => k.publicKey.verifies "a policy".toUTF8 sig
            && Rsa.verifyReference n e "a policy".toUTF8 sig
            && !Rsa.verifyReference n e "a policy!".toUTF8 sig
        | _, _ => false),
    ("sign: one key signs one message one way, and SHA-1 otherwise than SHA-256",
      [rsa, p256].all fun k => k.any fun k =>
        k.sign .sha1 "m".toUTF8 == k.sign .sha1 "m".toUTF8
          && k.sign .sha1 "m".toUTF8 != k.sign .sha256 "m".toUTF8
          && k.sign .sha1 "m".toUTF8 != k.sign .sha1 "n".toUTF8),
    ("sign: what is not a private key in PEM is refused, saying nothing of what it was",
      ["", "-----BEGIN PRIVATE KEY-----\nAAAA\n-----END PRIVATE KEY-----\n",
        String.fromUTF8! (rsaPem.extract 0 400)].all fun s =>
        SigningKey.ofPem s.toUTF8 matches .error "signing key: not a private key in PEM, or encrypted"),
    ("sign: a key shows as <signing key>", rsa.any fun k => reprStr k == "<signing key>"),
    ("sign: a public key's DER reads back as the key; cut short or retagged it does not",
      [rsa, p256].all fun k => k.any fun k =>
        let der := k.publicKey.spki
        (PublicKey.ofSpki? der).any (·.spki == der)
          && (PublicKey.ofSpki? (der.extract 0 (der.size - 1))).isNone
          && (PublicKey.ofSpki? (der.set! 0 0x31)).isNone
          && (PublicKey.ofSpki? (der.push 0)).isNone),
    ("sign: Der.read? reads each length tlv writes, and what follows",
      [0, 1, 127, 128, 255, 256, 65535, 70000].all fun n =>
        Der.read? (Der.tlv 4 (List.replicate n 7) ++ [9]) == some (4, List.replicate n 7, [9])) ]

def file (dir : System.FilePath) (name : String) : IO ByteArray := IO.FS.readBinFile (dir / name)

def refused (dir : System.FilePath) (args : Array String) : IO Bool := do
  Tests.Tls.run dir args
  return (SigningKey.ofPem (← file dir "k.pem")) matches .error _

def live : IO (List (String × Bool)) := do
  unless ← Tests.Tls.hasOpenssl do
    IO.println "sign: skipped the comparison with openssl, there is no openssl command"
    return []
  let (some rsa, some p256) := (rsa, p256) | return [("sign: the test keys are read", false)]
  let dir : System.FilePath := s!"{(← IO.getEnv "TMPDIR").getD "/tmp"}/lanes-sign-{← IO.monoNanosNow}"
  IO.FS.createDirAll dir
  try
    IO.FS.writeBinFile (dir / "rsa.pem") rsaPem
    IO.FS.writeBinFile (dir / "p256.pem") p256Pem
    let mut same := true
    let mut checks := true
    for i in [0:12] do
      let msg := ("{\"Statement\":[" ++ toString i ++ "]}").toUTF8 ++ (← randomBytes (i * 29).toUSize)
      IO.FS.writeBinFile (dir / "msg") msg
      for (hash, flag) in [(HashAlgorithm.sha1, "-sha1"), (.sha256, "-sha256")] do
        let theirs ← Tests.Signature.run dir #["dgst", flag, "-sign", "rsa.pem", "-out", "out", "msg"]
        same := same && rsa.sign hash msg == some theirs
        let some ours := p256.sign hash msg | checks := false
        IO.FS.writeBinFile (dir / "sig") ours
        IO.FS.writeFile (dir / "pub.pem") p256.publicKey.pem
        let verify := #["dgst", flag, "-verify", "pub.pem", "-signature", "sig", "msg"]
        let out ← IO.Process.output { cmd := "openssl", args := verify, cwd := some dir }
        checks := checks && out.exitCode == 0
    let pubs ← [("rsa.pem", rsa), ("p256.pem", p256)].mapM fun (name, k) => do
      Tests.Tls.run dir #["pkey", "-in", name, "-pubout", "-out", "out"]
      return String.fromUTF8? (← file dir "out") == some k.publicKey.pem
    let refusals ← [#["genrsa", "-aes256", "-passout", "pass:x", "-out", "k.pem", "2048"],
      #["genrsa", "-out", "k.pem", "1024"],
      #["ecparam", "-name", "secp384r1", "-genkey", "-noout", "-out", "k.pem"],
      #["ecparam", "-name", "secp256k1", "-genkey", "-noout", "-out", "k.pem"],
      #["genpkey", "-algorithm", "ed25519", "-out", "k.pem"]].mapM (refused dir)
    return [("sign: RSA signs with SHA-1 and SHA-256 byte for byte as openssl dgst -sign does", same),
      ("sign: ECDSA signatures with SHA-1 and SHA-256 check under openssl dgst -verify", checks),
      ("sign: the public key's PEM is what openssl pkey -pubout writes", pubs.all id),
      ("sign: an encrypted key, RSA of 1024 bits, P-384, secp256k1 and Ed25519 are refused",
        refusals.all id)]
  finally
    IO.FS.removeDirAll dir

end Tests.Sign
