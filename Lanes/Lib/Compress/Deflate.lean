/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Lib.Compress.Inflate

/-!
# Deflate

A DEFLATE (RFC 1951) encoder: one block with the fixed Huffman code, its matches found greedily
in a hash chain of at most `chain_max` places within the last 32 KiB, or stored blocks when
those are smaller. With no code of its own per block it writes text larger than zlib's fastest
level does, which is still a fraction of the text, enough for a response. `Inflate` reads back
what it writes (`Tests/Compress.lean`), and so does Go's `compress/flate`
(`Tests/Oracle/Compress.lean`). `canonical` and `block` write a block with any code, which the
oracle's generator of dynamic blocks uses.
-/

@[expose] public section

namespace Lanes.Deflate

/-- Bits written the first the lowest: whole bytes in `out`, fewer than eight in `acc`. -/
structure Writer where
  out : ByteArray := .empty
  acc : UInt64 := 0
  count : Nat := 0

def Writer.drain (out : ByteArray) (acc : UInt64) : Nat → ByteArray × UInt64
  | 0 => (out, acc)
  | n + 1 => Writer.drain (out.push acc.toUInt8) (acc >>> 8) n

/-- `value`, which has at most `n` bits, `n` at most 32. -/
@[inline] def Writer.put (w : Writer) (value n : Nat) : Writer :=
  let { out, acc, count } := w
  let acc := acc ||| (value.toUInt64 <<< count.toUInt64)
  let count := count + n
  let (out, acc) := Writer.drain out acc (count / 8)
  { out, acc, count := count % 8 }

/-- What is written, the last byte filled with zeros. -/
def Writer.finish (w : Writer) : ByteArray :=
  if w.count == 0 then w.out else w.out.push w.acc.toUInt8

/-- The lowest `n` bits of `code` in reverse order: Huffman codes are sent from their highest
bit. -/
def reverse (code n : Nat) : Nat :=
  (List.range n).foldl (fun r i => r ||| (((code >>> i) &&& 1) <<< (n - 1 - i))) 0

/-- The fixed code of a literal or length symbol, reversed, and its length. -/
def fixedLit (s : Nat) : Nat × Nat :=
  if s < 144 then (reverse (0x30 + s) 8, 8)
  else if s < 256 then (reverse (0x190 + s - 144) 9, 9)
  else if s < 280 then (reverse (s - 256) 7, 7)
  else (reverse (0xc0 + s - 280) 8, 8)

/-- A code to write with: each symbol's code, reversed, and its length. -/
structure Codes where
  lit : Array (Nat × Nat)
  dist : Array (Nat × Nat)

def fixedCodes : Codes where
  lit := (Array.range 288).map fixedLit
  dist := (Array.range 30).map fun d => (reverse d 5, 5)

/-- The canonical code of these lengths (RFC 1951 §3.2.2), each code reversed. -/
def canonical (lengths : Array Nat) : Array (Nat × Nat) := Id.run do
  let mut count := Array.replicate 16 0
  for l in lengths do
    if l ≠ 0 && l < 16 then count := count.modify l (· + 1)
  let mut next := Array.replicate 16 0
  let mut code := 0
  for l in [1:16] do
    code := (code + count[l - 1]!) <<< 1
    next := next.set! l code
  let mut codes := #[]
  for l in lengths do
    if l == 0 || l ≥ 16 then codes := codes.push (0, 0)
    else
      codes := codes.push (reverse next[l]! l, l)
      next := next.modify l (· + 1)
  return codes

/-- The index of a length's symbol, from 3 to 258, among the length symbols. -/
def lengthIndex (len : Nat) : Nat :=
  if len == 258 then 28
  else
    let x := len - 3
    if x < 8 then x else 4 * (Nat.log2 x - 1) + ((x >>> (Nat.log2 x - 2)) &&& 3)

/-- The symbol of a distance, from 1 to 32768. -/
def distIndex (dist : Nat) : Nat :=
  let x := dist - 1
  if x < 2 then x else 2 * Nat.log2 x + ((x >>> (Nat.log2 x - 1)) &&& 1)

def symbol (c : Codes) (w : Writer) (s : Nat) : Writer :=
  let (code, n) := c.lit[s]!
  w.put code n

def match_ (c : Codes) (w : Writer) (len dist : Nat) : Writer :=
  let i := lengthIndex len
  let w := symbol c w (257 + i)
  let w := w.put (len - Inflate.lengthBase[i]!) Inflate.lengthExtra[i]!
  let d := distIndex dist
  let (code, n) := c.dist[d]!
  let w := w.put code n
  w.put (dist - Inflate.distBase[d]!) Inflate.distExtra[d]!

def window : Nat := 32768

def hashBits : Nat := 15

def chain_max : Nat := 8

@[inline] def hash (data : ByteArray) (i : Nat) : Nat :=
  ((data[i]!.toNat <<< 10) ^^^ (data[i + 1]!.toNat <<< 5) ^^^ data[i + 2]!.toNat)
    &&& ((1 <<< hashBits) - 1)

/-- How many bytes from `a` and from `b` are equal, at most `n`. -/
def common (data : ByteArray) (a b : Nat) : (n : Nat) → Nat → Nat
  | 0, k => k
  | n + 1, k =>
    if b + k < data.size && data[a + k]! == data[b + k]! then common data a b n (k + 1) else k

/-- The places seen so far, by hash: the last place with each hash, and for each place the one
before it with the same hash, both one more than the place, `0` for none. -/
structure Chains where
  head : Array Nat := Array.replicate (1 <<< hashBits) 0
  prev : Array Nat := Array.replicate window 0

/-- Taken apart, so that each array is changed in place. -/
def Chains.insert (c : Chains) (data : ByteArray) (i : Nat) : Chains :=
  if i + 2 < data.size then
    let { head, prev } := c
    let h := hash data i
    let before := head[h]!
    { head := head.set! h (i + 1), prev := prev.set! (i % window) before }
  else c

/-- The places from `i`, `n` of them. -/
def Chains.insertAll (c : Chains) (data : ByteArray) (i : Nat) : Nat → Chains
  | 0 => c
  | n + 1 => (c.insert data i).insertAll data (i + 1) n

/-- The longest match for the place `i` among those in its chain, at most `steps` of them. -/
def Chains.best (c : Chains) (data : ByteArray) (i : Nat) : (steps : Nat) → (cand : Nat) →
    Nat × Nat → Nat × Nat
  | 0, _, best => best
  | steps + 1, cand, best =>
    if cand == 0 || i - (cand - 1) > window then best
    else
      let at_ := cand - 1
      let len := common data at_ i (min 258 (data.size - i)) 0
      let best := if len > best.1 then (len, i - at_) else best
      if len ≥ 258 then best else c.best data i steps c.prev[at_ % window]! best

/-- Each place from `i` written with `codes` as a literal or as the start of a match; with
`lz` off, every place as a literal. -/
def encode (codes : Codes) (lz : Bool) (data : ByteArray) :
    (fuel : Nat) → (i : Nat) → Chains → Writer → Writer
  | 0, _, _, w => w
  | fuel + 1, i, c, w =>
    if i < data.size then
      if lz && i + 2 < data.size then
        let cand := c.head[hash data i]!
        let (len, dist) := c.best data i chain_max cand (0, 0)
        if len ≥ 3 then
          let c := c.insertAll data i len
          encode codes lz data fuel (i + len) c (match_ codes w len dist)
        else encode codes lz data fuel (i + 1) (c.insert data i) (symbol codes w data[i]!.toNat)
      else encode codes lz data fuel (i + 1) c (symbol codes w data[i]!.toNat)
    else w

/-- The symbols of `data` and the end of the block, after what `w` holds. -/
def block (codes : Codes) (lz : Bool) (data : ByteArray) (w : Writer) : Writer :=
  symbol codes (encode codes lz data (data.size + 1) 0 {} w) 256

/-- One last block with the fixed code. -/
def fixed (data : ByteArray) : ByteArray :=
  (block fixedCodes true data (({} : Writer).put 0b011 3)).finish

/-- Stored blocks of at most 65535 bytes, the last marked so. -/
def stored (data : ByteArray) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  let mut start := 0
  for _ in [0:data.size / 65535 + 1] do
    let len := min 65535 (data.size - start)
    let last := start + len ≥ data.size
    out := out.push (if last then 1 else 0)
    out := out.push len.toUInt8 |>.push (len >>> 8).toUInt8
    out := out.push (0xffff - len).toUInt8 |>.push ((0xffff - len) >>> 8).toUInt8
    out := out ++ data.extract start (start + len)
    start := start + len
  return out

/-- A DEFLATE stream of `data`: the fixed code, or stored blocks when they are smaller. -/
def compress (data : ByteArray) : ByteArray :=
  let f := fixed data
  if f.size ≤ data.size + 5 * (data.size / 65535 + 1) then f else stored data

end Lanes.Deflate
