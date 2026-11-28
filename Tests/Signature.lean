/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Tests.Tls

/-!
Signatures checked by OpenSSL (`native/verify.c`) and the keys and tokens around them
(`Lanes/Lib/Crypto/PublicKey.lean`, `Lanes/Web/Auth/Jose.lean`). The published vectors: RFC 7515
Appendix A.2 (RS256) and A.3 (ES256), and RFC 7520 §4.1 (RS256 with a `kid`), taken as the test
suite of jwcrypto 1.6.2 carries them; A.1 (HS256), A.5 (`none`) and RFC 8037 A.4 (EdDSA) are
refused by name. Each RSA case is also checked by `Rsa.verifyReference`, the Lean reference, and
the two must agree on every signature changed in one byte. With the `openssl` command, keys made
for the test: the DER we write for a key is the DER `openssl` writes for it, and what `openssl`
signs checks, under RSA of 2048 and 3072 bits and P-256.
-/

namespace Tests.Signature

open Lanes Lanes.Jose

def b64 (s : String) : ByteArray := (Base64.decode .rawUrl s).getD .empty

def payloadA1 : String :=
  "eyJpc3MiOiJqb2UiLA0KICJleHAiOjEzMDA4MTkzODAsDQogImh0dHA6Ly9leGFtcGxlLmNvbS9pc19yb290Ijp0cnVlfQ"

/-- RFC 7515 A.2's key. -/
def keyA2 : String :=
  "{\"kty\":\"RSA\",\"e\":\"AQAB\",\"n\":\"ofgWCuLjybRlzo0tZWJjNiuSfb4p4fAkd_wWJcyQoTbji9k0l8W26mPddx\
  HmfHQp-Vaw-4qPCJrcS2mJPMEzP1Pt0Bm4d4QlL-yRT-SFd2lZS-pCgNMsD1W_YpRPEwOWvG6b32690r2jZ47soMZo9wGz\
  jb_7OMg0LOL-bSf63kpaSHSXndS5z5rexMdbBYUsLA9e-KXBdQOS-UTo7WTBEMa2R2CapHg665xsmtdVMTBQY4uDZlxvb3\
  qCo5ZwKh9kG4LT6_I5IhlJH7aGhyxXFvUK-DWNmoudF8NAco9_h9iaGNj8q2ethFkMLs91kzk2PAcDTW9gb54h4FRWyuX\
  poQ\"}"

def tokenA2 : String :=
  "eyJhbGciOiJSUzI1NiJ9." ++ payloadA1 ++ ".cC4hiUPoj9Eetdgtv3hF80EGrhuB__dzERat0XF9g2VtQgr9PJb\
  u3XOiZj5RZmh7AAuHIm4Bh-0Qc_lF5YKt_O8W2Fp5jujGbds9uJdbF9CUAr7t1dnZcAcQjbKBYNX4BAynRFdiuB--f_nZLg\
  rnbyTyWzO75vRK5h6xBArLIARNPvkSjtQBMHlb1L07Qe7K0GarZRmB_eSN9383LcOLn6_dO--xi12jzDwusC-eOkHWEsqtF\
  ZESc6BfI7noOPqvhJ1phCnvWh6IeYI2w9QOYEUipUTI8np6LbgGY9Fs98rqVt5AXLIhWkWywlVmtVrBp0igcN_IoypGlUPQ\
  Ge77Rw"

/-- RFC 7515 A.3's key. -/
def keyA3 : String :=
  "{\"kty\":\"EC\",\"crv\":\"P-256\",\"x\":\"f83OJ3D2xF1Bg8vub9tLe1gHMzV76e8Tus9uPHvRVEU\",\
  \"y\":\"x_FEzRu9m36HLN_tue659LNpXW6pCyStikYjKIWI5a0\"}"

def tokenA3 : String :=
  "eyJhbGciOiJFUzI1NiJ9." ++ payloadA1
    ++ ".DtEhU3ljbEg8L38VWAfUAqOyKAM6-Xx-F4GawxaepmXFCgfTjDxw5djxLa8ISlSApmWQxfKTUJqPP3-Kg6NU1Q"

/-- RFC 7520 §3.3's key, of `kid` `bilbo.baggins@hobbiton.example`. -/
def key7520 : String :=
  "{\"kty\":\"RSA\",\"kid\":\"bilbo.baggins@hobbiton.example\",\"use\":\"sig\",\"e\":\"AQAB\",\
  \"n\":\"n4EPtAOCc9AlkeQHPzHStgAbgs7bTZLwUBZdR8_KuKPEHLd4rHVTeT-O-XV2jRojdNhxJWTDvNd7nqQ0VEiZQHz\
  _AJmSCpMaJMRBSFKrKb2wqVwGU_NsYOYL-QtiWN2lbzcEe6XC0dApr5ydQLrHqkHHig3RBordaZ6Aj-oBHqFEHYpPe7Tpe-\
  OfVfHd1E6cS6M1FZcD1NNLYD5lFHpPI9bTwJlsde3uhGqC0ZCuEHg8lhzwOHrtIQbS0FVbb9k3-tVTU4fg_3L_vniUFAKwu\
  CLqKnS2BYwdq_mzSnbLY7h_qixoR7jig3__kRhuaxwUkRz5iaiQkqgc5gHdrNP5zw\"}"

/-- RFC 7520 §4.1.3. -/
def token7520 : String :=
  "eyJhbGciOiJSUzI1NiIsImtpZCI6ImJpbGJvLmJhZ2dpbnNAaG9iYml0b24uZXhhbXBsZSJ9.SXTigJlzIGEgZGFuZ2V\
  yb3VzIGJ1c2luZXNzLCBGcm9kbywgZ29pbmcgb3V0IHlvdXIgZG9vci4gWW91IHN0ZXAgb250byB0aGUgcm9hZCwgYW5k\
  IGlmIHlvdSBkb24ndCBrZWVwIHlvdXIgZmVldCwgdGhlcmXigJlzIG5vIGtub3dpbmcgd2hlcmUgeW91IG1pZ2h0IGJlI\
  HN3ZXB0IG9mZiB0by4.MRjdkly7_-oTPTS3AXP41iQIGKa80A0ZmTuV5MEaHoxnW2e5CZ5NlKtainoFmKZopdHM1O2U4mw\
  zJdQx996ivp83xuglII7PNDi84wnB-BDkoBwA78185hX-Es4JIwmDLJK3lfWRa-XtL0RnltuYv746iYTh_qHRD68BNt1uS\
  NCrUCTJDt5aAE6x8wW1Kt9eRo4QPocSadnHXFxnt8Is9UzpERV0ePPQdLuW3IS_de3xyIrDaLGdjluPxUAhb6L2aXic1U1\
  2podGU0KLUQSE_oI-ZnmKJ3F4uOZDnd6QZWJushZ41Axf_fcIe8u9ipH84ogoree7vjbU5y18kDquDg"

/-- RFC 7515 A.1 (HS256), A.5 (`none`) and RFC 8037 A.4 (EdDSA). -/
def tokenA1 : String :=
  "eyJ0eXAiOiJKV1QiLA0KICJhbGciOiJIUzI1NiJ9." ++ payloadA1
    ++ ".dBjftJeZ4CVP-mB92K27uhbUJU1p1r_wW1gFWFOEjXk"

def tokenA5 : String := "eyJhbGciOiJub25lIn0." ++ payloadA1 ++ "."

def token8037 : String :=
  "eyJhbGciOiJFZERTQSJ9.RXhhbXBsZSBvZiBFZDI1NTE5IHNpZ25pbmc.hgyY0il_MGCjP0JzlnLWG1PPOt7-09PGcvMg\
  3AIbQR6dWbhijcNR4ki4iylGjg5BhVsPt9g7sVvpAr_MuM0KAg"

def jwk (text : String) : Option Jwk :=
  (Json.parse text).toOption.bind Jwk.read?

def keys (texts : List String) : List Jwk := texts.filterMap jwk

def refusal (r : Except Refusal Compact) : Option Refusal :=
  match r with
  | .ok _ => none
  | .error e => some e

/-- The signature with byte `i` changed. -/
def flip (sig : ByteArray) (i : Nat) : ByteArray := sig.set! i (sig.get! i ^^^ 0x01)

/-- The binding and the reference agree on the signature and on it changed at each of `at`. -/
def agree (key : Jwk) (token : String) (at_ : List Nat) : Bool :=
  match key.key, Compact.read token with
  | .rsa n e, .ok c =>
    let both (sig : ByteArray) := (key.key.verifies c.signed sig, Rsa.verifyReference n e c.signed sig)
    both c.signature == (true, true)
      && at_.all fun i => both (flip c.signature i) == (false, false)
      && both (flip c.signature 0) == (false, false)
      && (key.key.verifies (c.signed.push 0) c.signature, Rsa.verifyReference n e (c.signed.push 0) c.signature)
        == (false, false)
  | _, _ => false

def tests : List (String × Bool) :=
  let a2 := keys [keyA2]
  let a3 := keys [keyA3]
  let k7520 := keys [key7520]
  [ ("signature: RFC 7515 A.2, RS256, checks", (verify a2 tokenA2).toBool),
    ("signature: RFC 7515 A.3, ES256, checks", (verify a3 tokenA3).toBool),
    ("signature: RFC 7520 §4.1, RS256 under the key its kid names, checks",
      match verify k7520 token7520 with
      | .ok c => c.kid == some "bilbo.baggins@hobbiton.example"
      | .error _ => false),
    ("signature: a key of another type or kid does not check it",
      refusal (verify a3 tokenA2) == some .unknownKey
        && refusal (verify a2 tokenA3) == some .unknownKey
        && refusal (verify (keys [keyA2.replace "{" "{\"kid\":\"other\","]) token7520)
          == some .unknownKey),
    ("signature: another RSA key does not check it",
      refusal (verify (keys [key7520.replace "\"kid\":\"bilbo.baggins@hobbiton.example\"," ""])
        tokenA2) == some .signature),
    ("signature: HS256, none and EdDSA are refused by name",
      refusal (verify (a2 ++ a3) tokenA1) == some (.alg "HS256")
        && refusal (verify (a2 ++ a3) tokenA5) == some (.alg "none")
        && refusal (verify (a2 ++ a3) token8037) == some (.alg "EdDSA")),
    ("signature: the binding and the Lean reference agree, on the vectors and changed in a byte",
      match a2, k7520 with
      | [a], [b] => agree a tokenA2 [1, 17, 100, 200, 255] && agree b token7520 [2, 50, 128, 254]
      | _, _ => false),
    ("signature: an ES256 signature changed in a byte, or of the wrong size, does not check",
      match a3, Compact.read tokenA3 with
      | [k], .ok c =>
        [0, 31, 32, 63].all (fun i => !k.key.verifies c.signed (flip c.signature i))
          && !k.key.verifies c.signed (c.signature.push 0)
          && !k.key.verifies c.signed (c.signature.extract 0 63)
      | _, _ => false),
    ("signature: keys that are not for signing, too small or off P-256 are not read",
      (jwk (keyA2.replace "{" "{\"use\":\"enc\",")).isNone
        && (jwk (keyA2.replace "{" "{\"alg\":\"HS256\",")).isNone
        && (jwk (keyA2.replace "{" "{\"alg\":\"RS256\",")).isSome
        && (jwk (keyA3.replace "P-256" "P-384")).isNone
        && (jwk "{\"kty\":\"oct\",\"k\":\"AyM1SysPpbyDfgZld3umj1qzKObwVMkoqQ-EstJQLr_T-1qS0gZH75\
          aKtMN3Yj0iPS4hcgUuTwjAzZr1Z9CAow\"}").isNone
        && (jwk "{\"kty\":\"RSA\",\"e\":\"AQAB\",\"n\":\"AQAB\"}").isNone
        && (jwk (keyA3.replace "\"x\":\"f83O" "\"x\":\"AAf83O")).isNone),
    ("signature: an RSA modulus is valid from 2048 bits to 8192 bits, counted in bits, not bytes",
      let rsa (n : Nat) : PublicKey := .rsa (Bytes.ofNat ((Der.digits n).length) n) ⟨#[1, 0, 1]⟩
      !(rsa (2 ^ 2040 + 1)).valid && !(rsa (2 ^ 2047 - 1)).valid && (rsa (2 ^ 2047 + 1)).valid
        && (rsa (2 ^ 8192 - 1)).valid && !(rsa (2 ^ 8192 + 1)).valid
        && !(PublicKey.rsa (Bytes.ofNat 257 (2 ^ 2040 + 1)) ⟨#[1, 0, 1]⟩).valid),
    ("signature: a token that is not three parts of base64url is malformed",
      [ "", "a.b", "a.b.c.d", tokenA2 ++ "=", "!" ++ tokenA2,
        "e30." ++ payloadA1 ++ ".", "W10." ++ payloadA1 ++ "." ].all
        (fun t => refusal (verify a2 t) == some .malformed)),
    ("signature: a JWK Set is read for its keys of signatures, and what is no set is refused",
      (readKeys ("{\"keys\":[" ++ keyA2 ++ "," ++ keyA3 ++ ",{\"kty\":\"oct\",\"k\":\"AA\"}]}")).toOption.map
          (·.length) == some 2
        && (readKeys "{\"keys\":{}}" matches .error .malformed)
        && (readKeys "[]" matches .error .malformed) && (readKeys "" matches .error .malformed)),
    ("signature: a signature is handed over only at its key's size, and ECDSA's as DER",
      let rsa := PublicKey.rsa (Bytes.ofNat 256 (2 ^ 2047)) ⟨#[1, 0, 1]⟩
      let ec := PublicKey.p256 (ByteArray.mk (Array.replicate 32 1)) (ByteArray.mk (Array.replicate 32 2))
      let sig := ByteArray.mk (Array.replicate 64 0x80)
      (rsa.derSignature (Bytes.ofNat 256 5)).isSome && (rsa.derSignature (Bytes.ofNat 255 5)).isNone
        && (ec.derSignature sig).any (fun d => d.size == 72 && d.get! 0 == 0x30 && d.get! 2 == 0x02
          && d.get! 3 == 33 && d.get! 4 == 0)
        && (ec.derSignature (sig.push 0)).isNone),
    ("signature: a header with crit is refused",
      refusal (verify a2 ("eyJhbGciOiJSUzI1NiIsImNyaXQiOlsiZXhwIl19." ++ payloadA1 ++ ".AA"))
        == some .critical),
    ("signature: the modular power is the power", Rsa.powMod 7 65537 1000003 == 7 ^ 65537 % 1000003
      && Rsa.powMod 2 0 1 == 0) ]

/-- What `openssl` writes to the file `out` when told `args`. -/
def run (dir : System.FilePath) (args : Array String) : IO ByteArray := do
  Tests.Tls.run dir args
  IO.FS.readBinFile (dir / "out")

/-- `n` from the hex `openssl rsa -modulus` prints after `Modulus=`. -/
def modulus (text : String) : ByteArray :=
  (Bytes.unhex? ((text.trimAscii.toString.drop 8).toString.toLower)).getD .empty

/-- `r ‖ s` from a DER ECDSA signature: a sequence of two integers, each in 32 bytes. -/
def raw (der : ByteArray) : Option ByteArray := do
  let int (at_ : Nat) : Option (ByteArray × Nat) := do
    guard (der.get! at_ == 0x02)
    let size := (der.get! (at_ + 1)).toNat
    let digits := der.extract (at_ + 2) (at_ + 2 + size)
    let digits := if digits.size == 33 then digits.extract 1 33 else digits
    guard (digits.size ≤ 32)
    return (ByteArray.mk (Array.replicate (32 - digits.size) 0) ++ digits, at_ + 2 + size)
  guard (der.get! 0 == 0x30)
  let (r, next) ← int 2
  let (s, _) ← int next
  return r ++ s

def live : IO (List (String × Bool)) := do
  unless ← Tests.Tls.hasOpenssl do
    IO.eprintln "signature: skipped the keys made by openssl, there is no openssl command"
    return []
  let dir : System.FilePath :=
    s!"{(← IO.getEnv "TMPDIR").getD "/tmp"}/lanes-signature-{← IO.monoNanosNow}"
  IO.FS.createDirAll dir
  try
    let mut results := []
    for bits in [2048, 3072] do
      Tests.Tls.run dir #["genrsa", "-out", "key.pem", toString bits]
      let printed ← IO.Process.run
        { cmd := "openssl", args := #["rsa", "-in", "key.pem", "-noout", "-modulus"], cwd := dir }
      let n := modulus printed
      let key := PublicKey.rsa n ⟨#[1, 0, 1]⟩
      let spki ← run dir #["rsa", "-in", "key.pem", "-pubout", "-outform", "DER", "-out", "out"]
      let mut checks := key.valid && key.spki == spki
      for i in [0:20] do
        let msg := s!"message {i} of {bits} bits".toUTF8 ++ (← randomBytes (i * 37).toUSize)
        IO.FS.writeBinFile (dir / "msg") msg
        let sig ← run dir #["dgst", "-sha256", "-sign", "key.pem", "-out", "out", "msg"]
        checks := checks && key.verifies msg sig && Rsa.verifyReference n ⟨#[1, 0, 1]⟩ msg sig
          && !key.verifies (msg.push 1) sig && !Rsa.verifyReference n ⟨#[1, 0, 1]⟩ (msg.push 1) sig
      results := results ++ [(s!"signature: RSA of {bits} bits made by openssl: its DER is ours, \
        and what it signs checks, by the binding and the reference", checks)]
    Tests.Tls.run dir #["ecparam", "-name", "prime256v1", "-genkey", "-noout", "-out", "ec.pem"]
    let spki ← run dir #["ec", "-in", "ec.pem", "-pubout", "-outform", "DER", "-out", "out"]
    let point := spki.extract (spki.size - 64) spki.size
    let key := PublicKey.p256 (point.extract 0 32) (point.extract 32 64)
    let mut checks := key.valid && key.spki == spki
    for i in [0:20] do
      let msg := s!"message {i}".toUTF8 ++ (← randomBytes (i * 41).toUSize)
      IO.FS.writeBinFile (dir / "msg") msg
      let der ← run dir #["dgst", "-sha256", "-sign", "ec.pem", "-out", "out", "msg"]
      checks := checks && (raw der).any fun sig =>
        key.verifies msg sig && !key.verifies (msg.push 1) sig && !key.verifies msg (flip sig 5)
    return results ++ [("signature: P-256 made by openssl: its DER is ours, and what it signs checks",
      checks)]
  finally
    IO.FS.removeDirAll dir

end Tests.Signature
