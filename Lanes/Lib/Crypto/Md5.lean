/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std

/-!
MD5 (RFC 1321) in pure Lean, for PostgreSQL's `md5` authentication and nothing else: MD5 is
broken as a hash, and the password digest PostgreSQL asks for is what the server stores.

It is not bound: libsodium has no MD5, and the digest a client sends is of a password the server
already holds a digest of, so a timing side channel here gives nothing a recording of the
exchange does not. Tested against RFC 1321's examples and against libpq's answer recorded from a
real server (`Tests/Postgres.lean`). That it is MD5 is not proved; that a digest is 16 bytes is.
-/

@[expose] public section

namespace Lanes.Md5

def shifts : Vector UInt32 64 := #v[
  7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22,
  5, 9, 14, 20, 5, 9, 14, 20, 5, 9, 14, 20, 5, 9, 14, 20,
  4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23,
  6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21]

/-- `⌊2^32 |sin (i + 1)|⌋`. -/
def sines : Vector UInt32 64 := #v[
  0xd76aa478, 0xe8c7b756, 0x242070db, 0xc1bdceee, 0xf57c0faf, 0x4787c62a, 0xa8304613, 0xfd469501,
  0x698098d8, 0x8b44f7af, 0xffff5bb1, 0x895cd7be, 0x6b901122, 0xfd987193, 0xa679438e, 0x49b40821,
  0xf61e2562, 0xc040b340, 0x265e5a51, 0xe9b6c7aa, 0xd62f105d, 0x02441453, 0xd8a1e681, 0xe7d3fbc8,
  0x21e1cde6, 0xc33707d6, 0xf4d50d87, 0x455a14ed, 0xa9e3e905, 0xfcefa3f8, 0x676f02d9, 0x8d2a4c8a,
  0xfffa3942, 0x8771f681, 0x6d9d6122, 0xfde5380c, 0xa4beea44, 0x4bdecfa9, 0xf6bb4b60, 0xbebfbc70,
  0x289b7ec6, 0xeaa127fa, 0xd4ef3085, 0x04881d05, 0xd9d4d039, 0xe6db99e5, 0x1fa27cf8, 0xc4ac5665,
  0xf4292244, 0x432aff97, 0xab9423a7, 0xfc93a039, 0x655b59c3, 0x8f0ccc92, 0xffeff47d, 0x85845dd1,
  0x6fa87e4f, 0xfe2ce6e0, 0xa3014314, 0x4e0811a1, 0xf7537e82, 0xbd3af235, 0x2ad7d2bb, 0xeb86d391]

abbrev State := Vector UInt32 4

def initial : State := #v[0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476]

def rotl (x n : UInt32) : UInt32 :=
  (x <<< n) ||| (x >>> (32 - n))

/-- The round function of step `i` and the word of the block it takes. -/
def mix (i : Nat) (b c d : UInt32) : UInt32 × Nat :=
  if i < 16 then ((b &&& c) ||| (~~~b &&& d), i)
  else if i < 32 then ((d &&& b) ||| (~~~d &&& c), (5 * i + 1) % 16)
  else if i < 48 then (b ^^^ c ^^^ d, (3 * i + 5) % 16)
  else (c ^^^ (b ||| ~~~d), (7 * i) % 16)

def compress (state : State) (block : Vector UInt32 16) : State := Id.run do
  let mut a := state[0]
  let mut b := state[1]
  let mut c := state[2]
  let mut d := state[3]
  for hi : i in [0:64] do
    have : i < 64 := hi.upper
    let (f, g) := mix i b c d
    let f := f + a + sines[i] + block[g % 16]'(Nat.mod_lt _ (by decide))
    a := d
    d := c
    c := b
    b := b + rotl f shifts[i]
  return #v[state[0] + a, state[1] + b, state[2] + c, state[3] + d]

def wordAt (bytes : ByteArray) (pos : Nat) (h : pos + 4 ≤ bytes.size) : UInt32 :=
  bytes[pos].toUInt32 ||| (bytes[pos + 1].toUInt32 <<< 8)
    ||| (bytes[pos + 2].toUInt32 <<< 16) ||| (bytes[pos + 3].toUInt32 <<< 24)

def blockAt (bytes : ByteArray) (pos : Nat) (h : pos + 64 ≤ bytes.size) : Vector UInt32 16 :=
  Vector.ofFn fun (t : Fin 16) => wordAt bytes (pos + 4 * t) (by omega)

/-- The bytes `0x80`, zeros, and the length in bits, least significant byte first, that make
`size` bytes whole blocks. -/
def padding (size : Nat) : ByteArray :=
  let zeros := (119 - size % 64) % 64
  let bits := size * 8
  ⟨#[(0x80 : UInt8)] ++ Array.replicate zeros (0 : UInt8)
    ++ (List.range 8).toArray.map fun k => (bits >>> (8 * k)).toUInt8⟩

def absorb (state : State) (bytes : ByteArray) : State := Id.run do
  let mut s := state
  for h : k in [0:bytes.size / 64] do
    have : k < bytes.size / 64 := h.upper
    s := compress s (blockAt bytes (64 * k) (by omega))
  return s

def State.bytes (state : State) : ByteArray :=
  ⟨(state.toArray.map fun (w : UInt32) =>
    #[w.toUInt8, (w >>> 8).toUInt8, (w >>> 16).toUInt8, (w >>> 24).toUInt8]).flatten⟩

theorem size_bytes (state : State) : state.bytes.size = 16 := by
  rcases state with ⟨⟨l⟩, hl⟩
  simp only [List.size_toArray] at hl
  match l, hl with
  | [_, _, _, _], _ => simp [State.bytes, ByteArray.size]

def hash (msg : ByteArray) : ByteArray :=
  (absorb initial (msg ++ padding msg.size)).bytes

theorem size_hash (msg : ByteArray) : (hash msg).size = 16 :=
  size_bytes _

end Lanes.Md5
