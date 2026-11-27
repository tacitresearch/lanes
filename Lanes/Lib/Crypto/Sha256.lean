/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std

/-!
SHA-256 (FIPS 180-4) in pure Lean. `digestFrom` continues a hash from a state that has already
taken whole blocks, which is what HMAC needs to hash its two padded keys once per key instead of
once per message (`Lanes.Hmac`).

This is the reference: programs use libsodium's (`Sha256.hash`, `Lanes/Lib/Crypto/Sodium.lean`), and
`Tests/Crypto.lean` checks the two agree. Tested against the NIST examples. That it is SHA-256 is
not proved; that a digest is 32 bytes is.
-/

@[expose] public section

namespace Lanes.Sha256

def roundConstants : Vector UInt32 64 := #v[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

abbrev State := Vector UInt32 8

def initial : State := #v[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

def rotr (x n : UInt32) : UInt32 :=
  (x >>> n) ||| (x <<< (32 - n))

def schedule (block : Vector UInt32 16) : Vector UInt32 64 := Id.run do
  let mut w : Vector UInt32 64 := Vector.replicate 64 0
  for h : t in [0:16] do
    have : t < 16 := h.upper
    w := w.set t block[t]
  for h : t in [16:64] do
    have : t < 64 := h.upper
    have : 16 ≤ t := h.lower
    let a := w[t - 15]
    let b := w[t - 2]
    let s0 := rotr a 7 ^^^ rotr a 18 ^^^ (a >>> 3)
    let s1 := rotr b 17 ^^^ rotr b 19 ^^^ (b >>> 10)
    w := w.set t (w[t - 16] + s0 + w[t - 7] + s1)
  return w

def compress (state : State) (block : Vector UInt32 16) : State := Id.run do
  let w := schedule block
  let mut a := state[0]
  let mut b := state[1]
  let mut c := state[2]
  let mut d := state[3]
  let mut e := state[4]
  let mut f := state[5]
  let mut g := state[6]
  let mut h := state[7]
  for hk : t in [0:64] do
    have : t < 64 := hk.upper
    let t1 := h + (rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25) + ((e &&& f) ^^^ (~~~e &&& g))
      + roundConstants[t] + w[t]
    let t2 := (rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22) + ((a &&& b) ^^^ (a &&& c) ^^^ (b &&& c))
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

def wordAt (bytes : ByteArray) (pos : Nat) (h : pos + 4 ≤ bytes.size) : UInt32 :=
  (bytes[pos].toUInt32 <<< 24) ||| (bytes[pos + 1].toUInt32 <<< 16)
    ||| (bytes[pos + 2].toUInt32 <<< 8) ||| bytes[pos + 3].toUInt32

def blockAt (bytes : ByteArray) (pos : Nat) (h : pos + 64 ≤ bytes.size) : Vector UInt32 16 :=
  Vector.ofFn fun (t : Fin 16) => wordAt bytes (pos + 4 * t) (by omega)

/-- The bytes `0x80`, zeros, and the length in bits, that make `size` bytes whole blocks. -/
def padding (size : Nat) : ByteArray :=
  let zeros := (119 - size % 64) % 64
  let bits := size * 8
  ⟨#[(0x80 : UInt8)] ++ Array.replicate zeros (0 : UInt8)
    ++ (List.range 8).reverse.toArray.map fun k => (bits >>> (8 * k)).toUInt8⟩

theorem size_padding (size : Nat) : (size + (padding size).size) % 64 = 0 := by
  simp [padding, ByteArray.size]
  omega

/-- Every whole block of `bytes`, from the first. -/
def absorb (state : State) (bytes : ByteArray) : State := Id.run do
  let mut s := state
  for h : k in [0:bytes.size / 64] do
    have : k < bytes.size / 64 := h.upper
    s := compress s (blockAt bytes (64 * k) (by omega))
  return s

/-- The hash of `done` bytes already absorbed into `state`, a whole number of blocks, followed by
`msg`. -/
def digestFrom (state : State) (done : Nat) (msg : ByteArray) : State :=
  absorb state (msg ++ padding (done + msg.size))

def State.bytes (state : State) : ByteArray :=
  ⟨(state.toArray.map fun (w : UInt32) =>
    #[(w >>> 24).toUInt8, (w >>> 16).toUInt8, (w >>> 8).toUInt8, w.toUInt8]).flatten⟩

theorem size_bytes (state : State) : state.bytes.size = 32 := by
  rcases state with ⟨⟨l⟩, hl⟩
  simp only [List.size_toArray] at hl
  match l, hl with
  | [_, _, _, _, _, _, _, _], _ => simp [State.bytes, ByteArray.size]

def reference (msg : ByteArray) : ByteArray :=
  (digestFrom initial 0 msg).bytes

theorem size_reference (msg : ByteArray) : (reference msg).size = 32 :=
  size_bytes _

end Lanes.Sha256
