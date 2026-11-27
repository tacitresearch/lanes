/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std

/-!
SHA-512 and SHA-384 (FIPS 180-4) in pure Lean, for the hash of a server's certificate that
channel binding sends (`Lanes/Lib/Crypto/Certificate.lean`) when the certificate is signed with
one of them. What is hashed is public, so a timing side channel here gives nothing away; libsodium
has SHA-512 but not SHA-384, which is SHA-512 from other initial words, cut to 48 bytes.

Tested against the NIST examples and against `openssl dgst` (`Tests/Crypto.lean`,
`Tests/PostgresTls.lean`). That it is SHA-512 is not proved; that a digest is 64 or 48 bytes is.
-/

@[expose] public section

namespace Lanes.Sha512

def roundConstants : Vector UInt64 80 := #v[
  0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
  0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
  0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
  0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
  0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
  0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
  0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
  0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
  0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
  0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
  0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
  0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
  0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
  0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
  0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
  0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
  0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
  0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
  0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
  0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817]

abbrev State := Vector UInt64 8

def initial : State := #v[
  0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
  0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179]

def initial384 : State := #v[
  0xcbbb9d5dc1059ed8, 0x629a292a367cd507, 0x9159015a3070dd17, 0x152fecd8f70e5939,
  0x67332667ffc00b31, 0x8eb44a8768581511, 0xdb0c2e0d64f98fa7, 0x47b5481dbefa4fa4]

def rotr (x n : UInt64) : UInt64 :=
  (x >>> n) ||| (x <<< (64 - n))

def schedule (block : Vector UInt64 16) : Vector UInt64 80 := Id.run do
  let mut w : Vector UInt64 80 := Vector.replicate 80 0
  for h : t in [0:16] do
    have : t < 16 := h.upper
    w := w.set t block[t]
  for h : t in [16:80] do
    have : t < 80 := h.upper
    have : 16 ≤ t := h.lower
    let a := w[t - 15]
    let b := w[t - 2]
    let s0 := rotr a 1 ^^^ rotr a 8 ^^^ (a >>> 7)
    let s1 := rotr b 19 ^^^ rotr b 61 ^^^ (b >>> 6)
    w := w.set t (w[t - 16] + s0 + w[t - 7] + s1)
  return w

def compress (state : State) (block : Vector UInt64 16) : State := Id.run do
  let w := schedule block
  let mut a := state[0]
  let mut b := state[1]
  let mut c := state[2]
  let mut d := state[3]
  let mut e := state[4]
  let mut f := state[5]
  let mut g := state[6]
  let mut h := state[7]
  for hk : t in [0:80] do
    have : t < 80 := hk.upper
    let t1 := h + (rotr e 14 ^^^ rotr e 18 ^^^ rotr e 41) + ((e &&& f) ^^^ (~~~e &&& g))
      + roundConstants[t] + w[t]
    let t2 := (rotr a 28 ^^^ rotr a 34 ^^^ rotr a 39) + ((a &&& b) ^^^ (a &&& c) ^^^ (b &&& c))
    h := g
    g := f
    f := e
    e := d + t1
    d := c
    c := b
    b := a
    a := t1 + t2
  return #v[state[0] + a, state[1] + b, state[2] + c, state[3] + d, state[4] + e, state[5] + f,
    state[6] + g, state[7] + h]

def wordAt (bytes : ByteArray) (pos : Nat) (h : pos + 8 ≤ bytes.size) : UInt64 :=
  (bytes[pos].toUInt64 <<< 56) ||| (bytes[pos + 1].toUInt64 <<< 48)
    ||| (bytes[pos + 2].toUInt64 <<< 40) ||| (bytes[pos + 3].toUInt64 <<< 32)
    ||| (bytes[pos + 4].toUInt64 <<< 24) ||| (bytes[pos + 5].toUInt64 <<< 16)
    ||| (bytes[pos + 6].toUInt64 <<< 8) ||| bytes[pos + 7].toUInt64

def blockAt (bytes : ByteArray) (pos : Nat) (h : pos + 128 ≤ bytes.size) : Vector UInt64 16 :=
  Vector.ofFn fun (t : Fin 16) => wordAt bytes (pos + 8 * t) (by omega)

/-- The bytes `0x80`, zeros, and the length in bits in sixteen bytes, that make `size` bytes
whole blocks of 128. -/
def padding (size : Nat) : ByteArray :=
  let zeros := (239 - size % 128) % 128
  let bits := size * 8
  ⟨#[(0x80 : UInt8)] ++ Array.replicate zeros (0 : UInt8)
    ++ (List.range 16).reverse.toArray.map fun k => (bits >>> (8 * k)).toUInt8⟩

def absorb (state : State) (bytes : ByteArray) : State := Id.run do
  let mut s := state
  for h : k in [0:bytes.size / 128] do
    have : k < bytes.size / 128 := h.upper
    s := compress s (blockAt bytes (128 * k) (by omega))
  return s

def State.bytes (state : State) : ByteArray :=
  ⟨(state.toArray.map fun (w : UInt64) =>
    (List.range 8).reverse.toArray.map fun k => (w >>> (8 * k).toUInt64).toUInt8).flatten⟩

theorem size_bytes (state : State) : state.bytes.size = 64 := by
  rcases state with ⟨⟨l⟩, hl⟩
  simp only [List.size_toArray] at hl
  match l, hl with
  | [_, _, _, _, _, _, _, _], _ => simp [State.bytes, ByteArray.size]

def hash (msg : ByteArray) : ByteArray :=
  (absorb initial (msg ++ padding msg.size)).bytes

def hash384 (msg : ByteArray) : ByteArray :=
  (absorb initial384 (msg ++ padding msg.size)).bytes.extract 0 48

theorem size_hash (msg : ByteArray) : (hash msg).size = 64 :=
  size_bytes _

theorem size_hash384 (msg : ByteArray) : (hash384 msg).size = 48 := by
  simp [hash384, ByteArray.size_extract, size_bytes]

end Lanes.Sha512
