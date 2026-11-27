/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Oracle.Basic

/-!
`Lanes.Jose.verify` against jwcrypto's on generated tokens, signed and then often tampered with:
a part changed, a header's algorithm or key id changed under the old signature, another key's
signature, `none`, HS256 under a secret of the set, keys the set marks for another use. The
tokens are signed here, by RSASSA-PKCS1-v1_5 (`Rsa.powMod`) and ECDSA on P-256 written for the
test, under keys made for it with Python's `cryptography`. A case is the set and the token, as
JSON; the answer is the payload of an accepted token.
-/

namespace Tests.Oracle.Jose

open Lanes Lanes.Jose

/-! ## Signing, for the test -/

namespace P256

def p : Nat := 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff
def n : Nat := 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551
def gx : Nat := 0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296
def gy : Nat := 0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5

/-- A point in Jacobian coordinates: `(x / z², y / z³)`, the point at infinity when `z = 0`. -/
structure Jac where
  x : Nat
  y : Nat
  z : Nat

def sub (a b : Nat) : Nat := (a + p - b % p) % p

/-- Doubling on a curve with `a = -3` (dbl-2001-b). -/
def dbl (q : Jac) : Jac :=
  if q.z == 0 then q else
  let delta := q.z * q.z % p
  let gamma := q.y * q.y % p
  let beta := q.x * gamma % p
  let alpha := 3 * sub q.x delta * ((q.x + delta) % p) % p
  let x := sub (alpha * alpha % p) (8 * beta % p)
  let z := sub (sub ((q.y + q.z) * (q.y + q.z) % p) gamma) delta
  let y := sub (alpha * sub (4 * beta % p) x % p) (8 * (gamma * gamma % p) % p)
  ⟨x, y, z⟩

/-- Addition (add-2007-bl). -/
def add (a b : Jac) : Jac :=
  if a.z == 0 then b else if b.z == 0 then a else
  let z1z1 := a.z * a.z % p
  let z2z2 := b.z * b.z % p
  let u1 := a.x * z2z2 % p
  let u2 := b.x * z1z1 % p
  let s1 := a.y * b.z % p * z2z2 % p
  let s2 := b.y * a.z % p * z1z1 % p
  if u1 == u2 then (if s1 == s2 then dbl a else ⟨0, 1, 0⟩) else
  let h := sub u2 u1
  let i := 4 * h * h % p
  let j := h * i % p
  let r := 2 * sub s2 s1 % p
  let v := u1 * i % p
  let x := sub (sub (r * r % p) j) (2 * v % p)
  let y := sub (r * sub v x % p) (2 * s1 * j % p)
  let z := sub (sub ((a.z + b.z) * (a.z + b.z) % p) z1z1) z2z2 * h % p
  ⟨x, y, z⟩

def mul (k : Nat) (q : Jac) : Jac :=
  (Nat.toDigits 2 k).foldl (fun acc bit => if bit == '1' then add (dbl acc) q else dbl acc) ⟨0, 1, 0⟩

def affine (q : Jac) : Nat × Nat :=
  let zi := Rsa.powMod q.z (p - 2) p
  (q.x * (zi * zi % p) % p, q.y * (zi * zi % p) % p * zi % p)

def publicPoint (d : Nat) : Nat × Nat := affine (mul d ⟨gx, gy, 1⟩)

/-- ECDSA with SHA-256 under `d`, with the nonce `k`: `r ‖ s`, as JWS writes it. -/
def sign (d k : Nat) (msg : ByteArray) : ByteArray :=
  let z := Bytes.toNat (Sha256.hash msg)
  let r := (affine (mul k ⟨gx, gy, 1⟩)).1 % n
  let s := Rsa.powMod k (n - 2) n * ((z + r * d) % n) % n
  Bytes.ofNat 32 r ++ Bytes.ofNat 32 s

end P256

/-- RSASSA-PKCS1-v1_5 with SHA-256 under the modulus `n` and private exponent `d`. -/
def rsaSign (n d : Nat) (msg : ByteArray) : ByteArray :=
  let k := (Der.digits n).length
  Bytes.ofNat k (Rsa.powMod (Bytes.toNat (Rsa.encode msg k)) d n)

/-- Keys made for this test. -/
def rsa2048n : Nat := 0xc7ef61c43e6e05eb12217689fdce3cf09609f3e82d8045f1266ed42e98256f3d97b0f5cc844973eea363685bf071ed54ac0f63fc3db1d9de6b445ba58cfff494744a9bf964cc258bc5ee8149bcff345481123c04fd2b464ff77da928a6453ba78d642eb2dc276accd1fa08cf32dcb6b36d591ca28df85108c1284041d9b67488bdb74be3d158845490079cc66fb09950bbb6a04748ae182c0976f9b1394eac462d748241aee7554d63a0fe47198d1c8dbde872323f88d03efd3bdee47f178cfeab5781fc8bbcbb04eeb78796c660950bb67a64c90a20262b23bbae3beade1bc5439065c70491f11da3d48cb83090d48bcb605de65fce79b3fa5b26555e04427f
def rsa2048d : Nat := 0x1e3bedabbf18e4f7a56087c904b9a65fc919c832d2e88df43d12156c74d95bf72bb138d5c4f61820d26a7deeaf635430ca15a9ba30f10aa575e93dc05f5f7560579bb858310d329bbdbc455dc87c87924464ba15a70d2253b62c04cb420127b930999b74b486123013eda8efc1a32a3c2c76854e667e39f6a4c20f90f1e109a97c45299550f97563957cb14e4c1711bf0ea2e37e917ee6e205f706ce924872a2c0bac17452d11f975e0d2bf885441d38784ba262e5b2a2b68a25914cdf4beaf19235e32518ec6e30e3f6e09610e09790864585a004a443a1b35bf2241dbc135bb682394e6d18f70b17b4d3f75f5118e16c8fd123fcba5338e6cc558b958cee1
def rsa1024n : Nat := 0xb24bfe08bf3555535c1e8ada3858c642ba694bfebcfe636bdd404d368903a72eb089143c5422f1811eea22e094c80b51c9b9770396eaecb2937ea65d20210dfc80026029cb4251280a8fc6dc8f198c296a6ae7e46e6cac6d5ea7b654df073e385b017df41b4111457ddef94286df89e5bbc94425c4803465820be17764263a5f
def rsa1024d : Nat := 0x3463c1f45e02d4dc96afdecafa4d938c1dec3cc9504d4b77715ea89182b71113d609a1698cab6bdd2df14c68432f78ac02a33d864f7d1e29e6cf0b2148048e700ab73203c8688730de95b7cdb6c25759661a213579500d2277ffeaeb41d36ef5f42545adbcfccf276f7df2cbbfbea8dfdb1d7bdd97cc36a6980a57116c5b5189
def ec1d : Nat := 0x4af86a0aa16bcfede1378277558db40b082b98712677adb7ba36763ab5f39adf
def ec1Point : Nat × Nat :=
  (0xf2007d9774f5552e9ecc33125ad6a29fc9413dc5c5647f864919e9413f0adae4,
    0x25263e03bfe74701eb13d3ffab38e95200566f98b87c692665e20ede8d37232d)
def ec2d : Nat := 0xfe2b17cbdcd003f43cd16863e4618100f071ffe8faac5f2332bd3e2325458169
def ec2Point : Nat × Nat :=
  (0xd8051a5a58b3cd6a5e053efce4e920c19a43ad201e1631251622642eb098e247,
    0xa9cc3b6094516e88975d8b676732aa25a3c686356911fbb5cd9d1bee1fc15209)
def hmacSecret : ByteArray := "a secret of the set".toUTF8

def b64 (b : ByteArray) : String := Base64.encode .rawUrl b

/-! ## Key sets -/

inductive Key where
  | rsa2048 | rsa1024 | ec1 | ec2 | oct
  deriving DecidableEq, Inhabited

def Key.kid : Key → String
  | .rsa2048 => "r1" | .rsa1024 => "r0" | .ec1 => "e1" | .ec2 => "e2" | .oct => "h1"

def Key.members : Key → List (String × Json)
  | .rsa2048 => [("kty", "RSA"), ("n", b64 (Bytes.ofNat 256 rsa2048n)), ("e", "AQAB")]
  | .rsa1024 => [("kty", "RSA"), ("n", b64 (Bytes.ofNat 128 rsa1024n)), ("e", "AQAB")]
  | .ec1 => [("kty", "EC"), ("crv", "P-256"), ("x", b64 (Bytes.ofNat 32 ec1Point.1)), ("y", b64 (Bytes.ofNat 32 ec1Point.2))]
  | .ec2 => [("kty", "EC"), ("crv", "P-256"), ("x", b64 (Bytes.ofNat 32 ec2Point.1)), ("y", b64 (Bytes.ofNat 32 ec2Point.2))]
  | .oct => [("kty", "oct"), ("k", b64 hmacSecret)]

/-- A key of a set: which, its `kid` if it has one, and its `use` and `alg` if the set says. -/
structure Entry where
  key : Key
  kid : Option String
  use : Option String := none
  alg : Option String := none

def Entry.json (e : Entry) : Json :=
  Json.mkObj (e.key.members ++ (e.kid.map (("kid", Json.str ·))).toList
    ++ (e.use.map (("use", Json.str ·))).toList ++ (e.alg.map (("alg", Json.str ·))).toList)

def setText (entries : List Entry) : String :=
  (Json.mkObj [("keys", .arr (entries.map Entry.json).toArray)]).compress

/-! ## Tokens -/

/-- The signature `alg` makes with `key` over `signed`; `nonce` is ECDSA's. -/
def signature (alg : String) (key : Key) (nonce : Nat) (signed : ByteArray) : ByteArray :=
  match alg, key with
  | "RS256", .rsa2048 => rsaSign rsa2048n rsa2048d signed
  | "RS256", .rsa1024 => rsaSign rsa1024n rsa1024d signed
  | "ES256", .ec1 => P256.sign ec1d nonce signed
  | "ES256", .ec2 => P256.sign ec2d nonce signed
  | "HS256", _ => hmac hmacSecret signed
  | _, _ => .empty

def compact (header payload : String) (sig : ByteArray) : String :=
  b64 header.toUTF8 ++ "." ++ b64 payload.toUTF8 ++ "." ++ b64 sig

def payloads : List String :=
  ["{\"sub\":\"1\",\"iss\":\"https://accounts.example\"}", "", "not JSON", "{\"a\":\"é\"}", "[]"]

def headerFor (alg : String) (kid : Option String) (extra : List (String × Json)) : String :=
  (Json.mkObj ([("alg", Json.str alg)] ++ (kid.map (("kid", Json.str ·))).toList ++ extra)).compress

def alphabet : List Char :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_".toList

/-- One character of the token changed, kept within base64url or not. -/
def flipChar (token : String) : Gen String := do
  let cs := token.toList
  let at_ ← Gen.below cs.length
  let c ← if ← Gen.chance 90 then Gen.pick alphabet else Gen.pick ['=', '+', '/', '.', ' ', '$']
  return String.ofList (cs.set at_ c)

def genEntries : Gen (List Entry) := do
  let keys := [Key.rsa2048, .ec1, .ec2, .rsa1024, .oct]
  let chosen ← keys.filterM fun _ => Gen.chance 70
  chosen.mapM fun k => do
    let kid ← if ← Gen.chance 85 then pure (some k.kid) else pure none
    let use ← if ← Gen.chance 10 then some <$> Gen.pick ["sig", "enc"] else pure none
    let alg ← if ← Gen.chance 10 then some <$> Gen.pick ["RS256", "ES256", "PS256", "HS256"] else pure none
    return { key := k, kid, use, alg }

def genToken : Gen (Key × String) := do
  let (alg, key) ← Gen.pick [("RS256", Key.rsa2048), ("ES256", .ec1), ("ES256", .ec2), ("RS256", .rsa1024),
    ("RS256", .rsa2048), ("ES256", .ec1), ("HS256", .oct), ("none", .oct)]
  let kid ← match ← Gen.below 10 with
    | 0 => pure none
    | 1 => pure (some "nobody")
    | 2 => some <$> Gen.pick ["r1", "e1", "e2", "r0", "h1"]
    | _ => pure (some key.kid)
  let extra ← match ← Gen.below 20 with
    | 0 => pure [("crit", Json.arr #["exp"]), ("exp", Json.num 1)]
    | 1 => pure [("typ", Json.str "JWT")]
    | 2 => pure [("b64", Json.bool false), ("crit", Json.arr #["b64"])]
    | _ => pure []
  let header := headerFor alg kid extra
  let payload ← Gen.pick payloads
  let signed := (b64 header.toUTF8 ++ "." ++ b64 payload.toUTF8).toUTF8
  let sig := signature alg key ((← Gen.below 1000000000) + 1) signed
  let token := compact header payload sig
  let token ← match ← Gen.below 15 with
    | 0 | 1 => flipChar token
    | 2 =>
      -- The header changed under the old signature.
      let other ← Gen.pick ["RS256", "ES256", "HS256", "none", "PS256"]
      pure (compact (headerFor other kid extra) payload sig)
    | 3 => do pure (compact header (← Gen.pick payloads) sig)
    | 4 => pure (compact header payload (sig.extract 0 (sig.size - 1)))
    | 5 => do pure (token ++ (← Gen.pick ["=", ".", ".x", "=="]))
    | _ => pure token
  return (key, token)

def caseJson (keys token : String) : Json := Json.mkObj [("keys", Json.str keys), ("token", Json.str token)]

def case : Gen Case := do
  let (key, token) ← genToken
  let entries ← genEntries
  let entries ← if ← Gen.chance 85 then
      pure (if entries.any (·.key == key) then entries else entries ++ [{ key, kid := some key.kid }])
    else pure entries
  let keys := setText entries
  let keys ← if ← Gen.chance 3 then Gen.pick ["{}", "{\"keys\":[{\"kty\":\"RSA\",\"n\":\"!\",\"e\":\"AQAB\"}]}",
    "not JSON"] else pure keys
  return ⟨"verify", (caseJson keys token).compress.toUTF8⟩

def allKeys : String :=
  setText ([Key.rsa2048, .ec1, .ec2, .rsa1024, .oct].map fun k => { key := k, kid := some k.kid })

def edges : List Case :=
  let rs := "{\"alg\":\"RS256\",\"kid\":\"r1\"}"
  let es := "{\"alg\":\"ES256\",\"kid\":\"e1\"}"
  let signed (h p : String) := (b64 h.toUTF8 ++ "." ++ b64 p.toUTF8).toUTF8
  let p := "{\"sub\":\"1\"}"
  [ caseJson allKeys (compact rs p (rsaSign rsa2048n rsa2048d (signed rs p))),
    caseJson allKeys (compact es p (P256.sign ec1d 12345 (signed es p))),
    caseJson allKeys (compact es p (P256.sign ec2d 12345 (signed es p))),
    caseJson allKeys (compact "{\"alg\":\"none\"}" p .empty),
    caseJson allKeys (compact "{\"alg\":\"HS256\",\"kid\":\"h1\"}" p
      (hmac hmacSecret (signed "{\"alg\":\"HS256\",\"kid\":\"h1\"}" p))) ].map
    fun j => ⟨"verify", j.compress.toUTF8⟩

/-- The signer written for the test is checked against the keys: the public points of the two
P-256 keys are `d·G`, and RSA's exponents invert each other. -/
def tests : List (String × Bool) :=
  [ ("oracle jose: the test's P-256 arithmetic gives the keys' public points",
      P256.publicPoint ec1d == ec1Point && P256.publicPoint ec2d == ec2Point),
    ("oracle jose: the test's RSA keys sign what their public halves verify",
      let m := "message".toUTF8
      Rsa.verifyReference (Bytes.ofNat 256 rsa2048n) ⟨#[1, 0, 1]⟩ m (rsaSign rsa2048n rsa2048d m)) ]

/-! ## Ours -/

def str? (j : Json) (name : String) : Option String :=
  match j.getObjVal? name with
  | .ok (.str s) => some s
  | _ => none

def parts? (c : Case) : Option (String × String) := do
  let j ← (Json.parse (← String.fromUTF8? c.input)).toOption
  return (← str? j "keys", ← str? j "token")

def answer (c : Case) : Answer := do
  let (keys, token) ← parts? c
  let ks ← (readKeys keys).toOption
  let compact ← (verify ks token).toOption
  return Json.mkObj [("payload", Bytes.hex compact.payload)]

/-! ## Where ours departs from jwcrypto -/

def entries? (c : Case) : List Json :=
  match parts? c with
  | some (keys, _) => match Json.parse keys with
    | .ok j => match j.getObjVal? "keys" with
      | .ok (.arr ks) => ks.toList
      | _ => []
    | .error _ => []
  | none => []

/-- Every part of the token is base64url without padding, as RFC 7515 §2 writes it, and with
no bits left over set. -/
def strictParts (c : Case) : Bool :=
  match parts? c with
  | some (_, token) => (token.splitOn ".").all fun part => (Base64.decode .rawUrl part).isSome
  | none => true

/-- The token's header, if it is a JSON object. -/
def header? (c : Case) : Option Json := do
  let (_, token) ← parts? c
  let h ← Base64.decode .rawUrl ((token.splitOn ".").headD "")
  (Json.parse (← String.fromUTF8? h)).toOption

/-- Whether the token could have been checked by the 1024-bit key: RS256 under its `kid`, or
under none. -/
def smallKey (c : Case) : Bool :=
  (entries? c).any (fun k => str? k "n" == some (b64 (Bytes.ofNat 128 rsa1024n)))
    && (header? c).any fun h => str? h "alg" == some "RS256" && (str? h "kid").all (· == "r0")

/-- A key of the set names an algorithm other than the token's. -/
def otherAlg (c : Case) : Bool :=
  let alg := (header? c).bind (str? · "alg")
  (entries? c).any fun k => (str? k "alg").any (some · != alg)

def package : Package where
  name := "jose"
  reference := .python "jwcrypto"
  edges := edges
  case := case
  answer := answer
  shrinks := false
  recorded := 250
  known c go :=
    if (answer c).isNone && go.isSome && !strictParts c then
      some "jwcrypto reads base64url with padding or stray characters; ours reads it unpadded and strict"
    else if (answer c).isNone && go.isSome && (header? c).any (·.getObjVal? "crit" |>.isOk) then
      some "jwcrypto understands RFC 7797's `b64` in `crit`; ours understands no extension"
    else if (answer c).isNone && go.isSome && smallKey c then
      some "ours refuses an RSA key of fewer than 2048 bits (RFC 7518 §3.3)"
    else if (answer c).isNone && go.isSome && otherAlg c then
      some "ours uses a key only for the algorithm its set names for it (RFC 7517 §4.4); jwcrypto for any"
    else if (answer c).isNone && go.isSome && (entries? c).any (fun k => str? k "use" == some "enc") then
      some "ours does not check a signature under a key its set marks for encryption"
    else none

end Tests.Oracle.Jose
