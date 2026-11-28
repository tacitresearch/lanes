/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std

/-!
# Inflate

DEFLATE (RFC 1951) decoded: stored, fixed and dynamic blocks, decoded canonical Huffman code by
code as Mark Adler's `puff` does. A code must be complete, or be one code of one bit, as Go's
`compress/flate` and zlib accept; the output is bounded by `max`, and decoding stops with
`tooLarge` before it would pass it, so a small input cannot make a large output (a "zip bomb").
Every loop is bounded by the bits of the input, so `inflate` is total.

Proved (`Inflate.size_le`): what `inflate` returns is at most `max` bytes. Compared with Go's
`compress/flate` on streams our encoder, Go's and a generator of dynamic blocks write, and on
streams edited a byte at a time (`Tests/Oracle/Compress.lean`).
-/

@[expose] public section

namespace Lanes.Inflate

inductive Error where
  | truncated
  | invalid (what : String)
  | tooLarge
  deriving DecidableEq, Repr

/-- A canonical Huffman code: how many codes each length has, and the symbols in code order. -/
structure Code where
  count : Array Nat
  symbol : Array Nat

/-- The code of these lengths, if it is complete or one code of one bit; with no length at all,
an empty code, which fails when used. -/
def Code.build (lengths : Array Nat) : Option Code := Id.run do
  let mut count := Array.replicate 16 0
  for l in lengths do
    if l < 16 then count := count.modify l (· + 1)
  let max := (List.range 16).foldl (fun m l => if l ≠ 0 && count[l]! ≠ 0 then l else m) 0
  if max == 0 then return some { count := Array.replicate 16 0, symbol := #[] }
  let mut code := 0
  for l in [1:max + 1] do
    code := (code <<< 1) + count[l]!
  if code != 1 <<< max && !(code == 1 && max == 1) then return none
  let mut offs := Array.replicate 16 0
  for l in [1:15] do
    offs := offs.set! (l + 1) (offs[l]! + count[l]!)
  let mut symbol := Array.replicate lengths.size 0
  for s in [0:lengths.size] do
    let l := lengths[s]!
    if l ≠ 0 then
      symbol := symbol.set! offs[l]! s
      offs := offs.modify l (· + 1)
  return some { count := count.set! 0 0, symbol }

/-- The bit at `pos`, counting from the lowest bit of the first byte. -/
@[inline] def bitAt (data : ByteArray) (pos : Nat) : Nat :=
  if h : pos >>> 3 < data.size then (data[pos >>> 3].toNat >>> (pos &&& 7)) &&& 1 else 0

/-- `n` bits from `pos`, the first the lowest, and where they end. -/
def bits (data : ByteArray) (pos n : Nat) : Except Error (Nat × Nat) :=
  if pos + n ≤ data.size * 8 then .ok (go 0 0, pos + n) else .error .truncated
where
  go (i acc : Nat) : Nat :=
    if i < n then go (i + 1) (acc ||| (bitAt data (pos + i) <<< i)) else acc
  termination_by n - i

/-- A symbol of `c` from `pos`, a bit at a time, and where it ends. -/
def Code.decode (c : Code) (data : ByteArray) (pos : Nat) : Except Error (Nat × Nat) :=
  go 1 0 0 0 pos
where
  go (len code first index pos : Nat) : Except Error (Nat × Nat) :=
    if len < 16 then
      if pos < data.size * 8 then
        let code := code ||| bitAt data pos
        let count := c.count[len]!
        if code < first + count then
          match c.symbol[index + (code - first)]? with
          | some s => .ok (s, pos + 1)
          | none => .error (.invalid "code")
        else go (len + 1) (code <<< 1) ((first + count) <<< 1) (index + count) (pos + 1)
      else .error .truncated
    else .error (.invalid "code")
  termination_by 16 - len

def lengthBase : Array Nat :=
  #[3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115,
    131, 163, 195, 227, 258]

def lengthExtra : Array Nat :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0]

def distBase : Array Nat :=
  #[1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537,
    2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577]

def distExtra : Array Nat :=
  #[0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13,
    13]

def fixedLengths : Array Nat :=
  Array.replicate 144 8 ++ Array.replicate 112 9 ++ Array.replicate 24 7 ++ Array.replicate 8 8

def fixedLit : Code := (Code.build fixedLengths).getD { count := #[], symbol := #[] }

/-- The fixed distance code has 30 codes of five bits, so it is incomplete; it is built here
directly, which `Code.build` does not do for a code read from a stream. -/
def fixedDist : Code :=
  { count := (Array.replicate 16 0).set! 5 30, symbol := Array.range 30 }

/-- `len` bytes copied from `dist` back, one at a time, so that a copy may overlap what it
writes. -/
def copy (out : ByteArray) (dist : Nat) : Nat → ByteArray
  | 0 => out
  | n + 1 => copy (out.push (out[out.size - dist]?.getD 0)) dist n

/-- The symbols of a block until its end, with codes `lit` and `dist`; at most `fuel`. -/
def symbols (max : Nat) (data : ByteArray) (lit dist : Code) :
    (fuel : Nat) → (pos : Nat) → ByteArray → Except Error (ByteArray × Nat)
  | 0, _, _ => .error .truncated
  | fuel + 1, pos, out => do
    let (s, pos) ← lit.decode data pos
    if s < 256 then
      if out.size < max then symbols max data lit dist fuel pos (out.push s.toUInt8)
      else .error .tooLarge
    else if s == 256 then .ok (out, pos)
    else
      let i := s - 257
      if i < 29 then
        let (extra, pos) ← bits data pos lengthExtra[i]!
        let len := lengthBase[i]! + extra
        let (d, pos) ← dist.decode data pos
        if d < 30 then
          let (extra, pos) ← bits data pos distExtra[d]!
          let back := distBase[d]! + extra
          if back > out.size then .error (.invalid "distance too far back")
          else if out.size + len > max then .error .tooLarge
          else symbols max data lit dist fuel pos (copy out back len)
        else .error (.invalid "distance symbol")
      else .error (.invalid "length symbol")

/-- The order in which a dynamic block gives the lengths of the code of lengths. -/
def order : Array Nat := #[16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15]

/-- The lengths of a dynamic block's codes, `n` of them, read with the code of lengths. -/
def lengths (data : ByteArray) (lens : Code) (n : Nat) :
    (fuel : Nat) → (pos : Nat) → Array Nat → Except Error (Array Nat × Nat)
  | 0, _, _ => .error .truncated
  | fuel + 1, pos, acc =>
    if acc.size ≥ n then
      if acc.size == n then .ok (acc, pos) else .error (.invalid "too many lengths")
    else do
      let (s, pos) ← lens.decode data pos
      if s < 16 then lengths data lens n fuel pos (acc.push s)
      else
        let (value, extraBits, base) :=
          if s == 16 then (acc.back?.getD 16, 2, 3)
          else if s == 17 then (0, 3, 3)
          else (0, 7, 11)
        if value == 16 then .error (.invalid "repeat with no length before")
        else
          let (extra, pos) ← bits data pos extraBits
          lengths data lens n fuel pos (acc ++ Array.replicate (base + extra) value)

/-- A dynamic block's codes. -/
def dynamic (data : ByteArray) (pos fuel : Nat) : Except Error (Code × Code × Nat) := do
  let (nlen, pos) ← bits data pos 5
  let (ndist, pos) ← bits data pos 5
  let (ncode, pos) ← bits data pos 4
  let nlen := nlen + 257
  let ndist := ndist + 1
  if nlen > 286 || ndist > 30 then throw (.invalid "too many codes")
  let mut at_ := pos
  let mut codeLengths := Array.replicate 19 0
  for i in [0:ncode + 4] do
    let (l, p) ← bits data at_ 3
    codeLengths := codeLengths.set! order[i]! l
    at_ := p
  let some lens := Code.build codeLengths | throw (.invalid "code of lengths")
  let (all, pos) ← lengths data lens (nlen + ndist) fuel at_ #[]
  if all[256]?.getD 0 == 0 then throw (.invalid "no end of block")
  let some lit := Code.build (all.extract 0 nlen) | throw (.invalid "code of literals")
  let some dist := Code.build (all.extract nlen (nlen + ndist)) | throw (.invalid "code of distances")
  return (lit, dist, pos)

/-- A stored block from `pos`, after its three bits. -/
def stored (max : Nat) (data : ByteArray) (pos : Nat) (out : ByteArray) :
    Except Error (ByteArray × Nat) := do
  let byte := (pos + 7) / 8
  if byte + 4 > data.size then throw .truncated
  let len := data[byte]!.toNat ||| (data[byte + 1]!.toNat <<< 8)
  let nlen := data[byte + 2]!.toNat ||| (data[byte + 3]!.toNat <<< 8)
  if len + nlen != 0xffff then throw (.invalid "stored length")
  if byte + 4 + len > data.size then throw .truncated
  if out.size + len > max then throw .tooLarge
  return (out ++ data.extract (byte + 4) (byte + 4 + len), (byte + 4 + len) * 8)

/-- The blocks from `pos` until the last, at most `fuel` of them. -/
def blocks (max : Nat) (data : ByteArray) (bitsAll : Nat) :
    (fuel : Nat) → (pos : Nat) → ByteArray → Except Error (ByteArray × Nat)
  | 0, _, _ => .error .truncated
  | fuel + 1, pos, out => do
    let (last, pos) ← bits data pos 1
    let (kind, pos) ← bits data pos 2
    let (out, pos) ← match kind with
      | 0 => stored max data pos out
      | 1 => symbols max data fixedLit fixedDist bitsAll pos out
      | 2 => do
        let (lit, dist, pos) ← dynamic data pos bitsAll
        symbols max data lit dist bitsAll pos out
      | _ => throw (.invalid "block type")
    if last == 1 then return (out, pos) else blocks max data bitsAll fuel pos out

/-- The bytes of the DEFLATE stream at the start of `data`, at most `max` of them, and the byte
after its end. -/
def inflateFrom (max : Nat) (data : ByteArray) (start : Nat := 0) :
    Except Error (ByteArray × Nat) := do
  let all := data.size * 8 + 1
  let (out, pos) ← blocks max data all all (start * 8) .empty
  if out.size ≤ max then return (out, (pos + 7) / 8) else throw .tooLarge

/-- `out`, if it has at most `max` bytes: the last check of each decoder. -/
def within (max : Nat) (out : ByteArray) : Except Error ByteArray :=
  if out.size ≤ max then .ok out else .error .tooLarge

theorem size_le_of_within {max : Nat} {out out' : ByteArray} (h : within max out = .ok out') :
    out'.size ≤ max := by
  unfold within at h
  split at h
  · cases h; assumption
  · cases h

theorem size_le_of_bind {α : Type} {max : Nat} {r : Except Error α} {f : α → ByteArray}
    {out : ByteArray} (h : (r >>= fun a => within max (f a)) = .ok out) : out.size ≤ max := by
  cases r with
  | error e => cases h
  | ok a => exact size_le_of_within h

/-- The bytes of the DEFLATE stream at the start of `data`, at most `max` of them. What follows
the stream is ignored. -/
def inflate (max : Nat) (data : ByteArray) : Except Error ByteArray :=
  inflateFrom max data >>= fun r => within max r.1

/-- What `inflate` returns has at most `max` bytes. -/
theorem size_le {max : Nat} {data out : ByteArray} (h : inflate max data = .ok out) :
    out.size ≤ max :=
  size_le_of_bind h

end Lanes.Inflate
