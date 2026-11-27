/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Lib.Crypto.Sodium

/-!
Public keys that check signatures: RSA, and ECDSA on P-256. A key is written as the DER
`SubjectPublicKeyInfo` OpenSSL reads (RFC 5280 §4.1.2.7, RFC 3279 §2.3.1, RFC 5480 §2), and an
ECDSA signature, which JWS writes as `r ‖ s`, as the DER `ECDSA-Sig-Value` (RFC 3279 §2.2.3),
so that the binding (`Lanes/Lib/Crypto/Verify.lean`) only hands them over.

Which keys are accepted is decided here: an RSA modulus of 2048 to 8192 bits with an odd
exponent above one, a P-256 point given in full. `Rsa.verifyReference` is RSASSA-PKCS1-v1_5
with SHA-256 (RFC 8017 §8.2.2) in Lean, the reference beside the binding (rule 2.7).
-/

@[expose] public section

namespace Lanes

/-- The number a big-endian byte string spells. -/
def Bytes.toNat (bytes : ByteArray) : Nat :=
  bytes.data.foldl (fun n b => n * 256 + b.toNat) 0

/-- `n` in `size` big-endian bytes: its low `size` bytes if it needs more. -/
def Bytes.ofNat (size n : Nat) : ByteArray :=
  ⟨((List.range size).reverse.map fun i => (n / 256 ^ i % 256).toUInt8).toArray⟩

theorem Bytes.size_ofNat (size n : Nat) : (Bytes.ofNat size n).size = size := by
  simp [Bytes.ofNat, ByteArray.size]

namespace Der

/-- The bytes of `n`, most significant first, none for zero. -/
def digits (n : Nat) : List UInt8 :=
  if n = 0 then [] else digits (n / 256) ++ [(n % 256).toUInt8]
termination_by n
decreasing_by omega

def length (n : Nat) : List UInt8 :=
  if n < 128 then [n.toUInt8] else (0x80 + (digits n).length).toUInt8 :: digits n

def tlv (tag : UInt8) (body : List UInt8) : List UInt8 :=
  tag :: length body.length ++ body

/-- An unsigned big-endian number as a DER INTEGER: its leading zero bytes dropped, and one put
back when the first left has its high bit set, which would make it negative. -/
def integer (bytes : List UInt8) : List UInt8 :=
  match bytes.dropWhile (· == 0) with
  | [] => tlv 0x02 [0]
  | d :: rest => tlv 0x02 (if d < 0x80 then d :: rest else 0 :: d :: rest)

def sequence (parts : List (List UInt8)) : List UInt8 := tlv 0x30 parts.flatten

def bitString (body : List UInt8) : List UInt8 := tlv 0x03 (0 :: body)

/-- `rsaEncryption`, 1.2.840.113549.1.1.1, with its NULL parameters. -/
def rsaAlgorithm : List UInt8 :=
  sequence [[0x06, 0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x01], [0x05, 0x00]]

/-- `id-ecPublicKey`, 1.2.840.10045.2.1, on the curve `prime256v1`, 1.2.840.10045.3.1.7. -/
def p256Algorithm : List UInt8 :=
  sequence [[0x06, 0x07, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x02, 0x01],
    [0x06, 0x08, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x03, 0x01, 0x07]]

end Der

inductive PublicKey where
  /-- RSA: the modulus and the public exponent, big-endian. -/
  | rsa (n e : ByteArray)
  /-- ECDSA on P-256: the point's coordinates, big-endian. -/
  | p256 (x y : ByteArray)

namespace PublicKey

/-- The bytes a signature has under an RSA modulus: those of the modulus. -/
def rsaSize (n : ByteArray) : Nat := (Der.digits (Bytes.toNat n)).length

/-- An RSA modulus of 2048 to 8192 bits and an odd exponent above one; or a point of P-256
given as two coordinates of 32 bytes each. That the point is on the curve is OpenSSL's check. -/
def valid : PublicKey → Bool
  | .rsa n e => 256 ≤ rsaSize n && rsaSize n ≤ 1024 && Bytes.toNat e % 2 == 1 && 1 < Bytes.toNat e
  | .p256 x y => x.size == 32 && y.size == 32

def spki : PublicKey → ByteArray
  | .rsa n e => ⟨(Der.sequence [Der.rsaAlgorithm,
      Der.bitString (Der.sequence [Der.integer n.data.toList, Der.integer e.data.toList])]).toArray⟩
  | .p256 x y => ⟨(Der.sequence [Der.p256Algorithm,
      Der.bitString (0x04 :: x.data.toList ++ y.data.toList)]).toArray⟩

/-- The signature as OpenSSL reads it, if it has the size the key's signatures have: under RSA
as it is, under P-256 its two halves as a DER sequence of two integers. -/
def derSignature (key : PublicKey) (sig : ByteArray) : Option ByteArray :=
  match key with
  | .rsa n _ => if sig.size == rsaSize n then some sig else none
  | .p256 .. =>
    if sig.size == 64 then
      some ⟨(Der.sequence [Der.integer (sig.extract 0 32).data.toList,
        Der.integer (sig.extract 32 64).data.toList]).toArray⟩
    else none

end PublicKey

namespace Rsa

/-- `b ^ e % m`, by squaring. -/
def powMod (b e m : Nat) : Nat :=
  if e = 0 then 1 % m
  else
    let half := powMod (b * b % m) (e / 2) m
    if e % 2 = 1 then b % m * half % m else half
termination_by e
decreasing_by omega

theorem powMod_eq (b e m : Nat) : powMod b e m = b ^ e % m := by
  induction e using Nat.strongRecOn generalizing b with
  | _ e ih =>
    unfold powMod
    split
    · subst_vars; simp
    · rename_i h
      have hlt : e / 2 < e := by omega
      rw [ih _ hlt]
      have he : e = 2 * (e / 2) + e % 2 := (Nat.div_add_mod e 2).symm
      have hsq : (b * b % m) ^ (e / 2) % m = b ^ (2 * (e / 2)) % m := by
        rw [Nat.pow_mod, Nat.mod_mod, ← Nat.pow_mod, pow_mul_comm', Nat.pow_mul]
      split
      · rw [hsq, ← Nat.mul_mod]
        conv => rhs; rw [he]
        rename_i hodd
        rw [hodd, Nat.pow_succ, Nat.mul_comm (b ^ _)]
      · rename_i heven
        rw [hsq]
        conv => rhs; rw [he]
        simp [show e % 2 = 0 by omega]
where
  pow_mul_comm' {a k : Nat} : (a * a) ^ k = a ^ (2 * k) := by
    rw [Nat.pow_mul, Nat.pow_two]

/-- The DER prefix of a SHA-256 `DigestInfo` (RFC 8017 §9.2, note 1). -/
def digestInfo : List UInt8 :=
  [0x30, 0x31, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01, 0x05,
    0x00, 0x04, 0x20]

/-- EMSA-PKCS1-v1_5 of `msg` with SHA-256 in `k` bytes (RFC 8017 §9.2). -/
def encode (msg : ByteArray) (k : Nat) : ByteArray :=
  ⟨([0x00, 0x01] ++ List.replicate (k - 54) 0xff ++ [0x00] ++ digestInfo
    ++ (Sha256.hash msg).data.toList).toArray⟩

/-- RSASSA-PKCS1-v1_5-VERIFY with SHA-256 (RFC 8017 §8.2.2): the signature has the modulus's
size `k`, is below the modulus, and raised to the exponent it is the encoding of `msg`, which
leaves at least eight bytes of padding. -/
def verifyReference (n e msg sig : ByteArray) : Bool :=
  let modulus := Bytes.toNat n
  let k := PublicKey.rsaSize n
  let s := Bytes.toNat sig
  62 ≤ k && sig.size == k && s < modulus
    && Bytes.ofNat k (powMod s (Bytes.toNat e) modulus) == encode msg k

end Rsa

end Lanes
