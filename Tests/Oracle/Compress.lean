/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Oracle.Basic

/-!
`Lanes.Inflate`, `Lanes.Gzip` and `Lanes.Zlib` against Go's `compress/flate`, `compress/gzip`
and `compress/zlib`: on streams our encoder writes, on dynamic blocks with codes made at random,
and on those edited a byte at a time or cut short. Our encoder's streams read back in Go show that
it writes DEFLATE as Go reads it.
-/

namespace Tests.Oracle.Compress

open Lanes

/-- Go's limit too. -/
def max : Nat := 1 <<< 20

def answer (c : Case) : Answer :=
  let hex (r : Except Inflate.Error ByteArray) : Answer :=
    match r with
    | .ok out => some (.str (Bytes.hex out))
    | .error _ => none
  match c.op with
  | "inflate" => hex (Inflate.inflate max c.input)
  | "gunzip" => hex (Gzip.decompress max c.input)
  | "zlib" => hex (Zlib.decompress max c.input)
  | _ => none

def words : List String :=
  ["the ", "lane ", "<div class=\"a\">", "</div>\n", "{\"id\":", "42", ",", "é", "zzzzzzzz", " "]

def dataGen : Gen ByteArray := do
  match ← Gen.below 4 with
  | 0 => Gen.bytes 200
  | 1 => return (String.join (← Gen.list (← Gen.below 300) (Gen.pick words))).toUTF8
  | 2 => return ⟨Array.replicate (← Gen.below 2000) ((← Gen.below 256).toUInt8)⟩
  | _ => return (String.join (← Gen.list (← Gen.below 40) (Gen.pick words))).toUTF8

/-- Leaves of a random binary tree, `n` of them, none deeper than `depth`: the lengths of a
complete prefix code. -/
def treeLengths (n depth : Nat) : Gen (List Nat) := do
  if n ≤ 1 then return List.replicate n 1
  let mut leaves : List Nat := [1, 1]
  for _ in [0:n - 2] do
    let i ← Gen.below leaves.length
    let i := if leaves[i]! < depth then i
      else (leaves.findIdx? (· < depth)).getD i
    let d := leaves[i]!
    leaves := ((leaves.eraseIdx i).insertIdx i (d + 1)).insertIdx i (d + 1)
  return leaves

def shuffle {α : Type} [Inhabited α] (l : List α) : Gen (List α) := do
  let mut rest := l
  let mut out := []
  for _ in [0:l.length] do
    let i ← Gen.below rest.length
    out := rest[i]! :: out
    rest := rest.eraseIdx i
  return out

/-- Lengths for the symbols of `used`, a complete code over them, and zero for the rest of `n`. -/
def codeOver (used : List Nat) (n depth : Nat) : Gen (Array Nat) := do
  let lengths ← shuffle (← treeLengths used.length depth)
  return (used.zip lengths).foldl (fun a (s, l) => a.set! s l) (Array.replicate n 0)

/-- Code length symbols for `lengths`, each with its extra bits and their count, with runs
written with 16, 17 and 18 when `runs`. -/
def runLengths (lengths : List Nat) (runs : Bool) : List (Nat × Nat × Nat) :=
  go lengths (lengths.length + 1)
where
  go : List Nat → Nat → List (Nat × Nat × Nat)
    | [], _ => []
    | _, 0 => []
    | l :: rest, fuel + 1 =>
      let same := (rest.takeWhile (· == l)).length
      if runs && l == 0 && same + 1 ≥ 11 then
        let k := min 138 (same + 1)
        (18, k - 11, 7) :: go (rest.drop (k - 1)) fuel
      else if runs && l == 0 && same + 1 ≥ 3 then
        let k := min 10 (same + 1)
        (17, k - 3, 3) :: go (rest.drop (k - 1)) fuel
      else if runs && l != 0 && same ≥ 3 then
        let k := min 6 same
        (l, 0, 0) :: (16, k - 3, 2) :: go (rest.drop k) fuel
      else (l, 0, 0) :: go rest fuel

/-- One dynamic block of `data` as literals, its codes made at random. -/
def dynamicBlock (data : ByteArray) (last : Bool) (w : Deflate.Writer) : Gen Deflate.Writer := do
  let literals := (data.data.toList.map (·.toNat)).eraseDups
  let extra ← Gen.list (← Gen.below 6) (Gen.below 286)
  let litUsed := (literals ++ [256] ++ extra).eraseDups
  let distUsed := (← Gen.list (← Gen.below 4) (Gen.below 30)).eraseDups
  let lit ← codeOver litUsed 286 15
  let dist ← codeOver distUsed 30 15
  let nlen := (litUsed.foldl Nat.max 256) + 1
  let ndist := (distUsed.foldl Nat.max 0) + 1
  let all := (lit.extract 0 nlen).toList ++ (dist.extract 0 ndist).toList
  let rle := runLengths all (← Gen.chance 70)
  let clens ← codeOver (rle.map (·.1)).eraseDups 19 7
  let ncode := (((List.range 19).filter fun i => clens[Inflate.order[i]!]! != 0).foldl Nat.max 3) + 1
  let ccodes := Deflate.canonical clens
  let mut w := w.put (if last then 1 else 0) 1
  w := w.put 2 2
  w := w.put (nlen - 257) 5
  w := w.put (ndist - 1) 5
  w := w.put (ncode - 4) 4
  for i in [0:ncode] do
    w := w.put clens[Inflate.order[i]!]! 3
  for (s, extraValue, extraBits) in rle do
    let (code, n) := ccodes[s]!
    w := w.put code n
    w := w.put extraValue extraBits
  return Deflate.block { lit := Deflate.canonical lit, dist := Deflate.canonical dist } false data w

def streamGen (data : ByteArray) : Gen ByteArray := do
  match ← Gen.below 4 with
  | 0 => return Deflate.compress data
  | 1 => return Deflate.stored data
  | 2 => return (← dynamicBlock data true {}).finish
  | _ =>
    let half := data.size / 2
    let w ← dynamicBlock (data.extract 0 half) false {}
    return (← dynamicBlock (data.extract half data.size) true w).finish

def byteMutate (b : ByteArray) : Gen ByteArray := do
  let at_ ← Gen.below (b.size + 1)
  let c := (← Gen.below 256).toUInt8
  let l := b.data.toList
  match ← Gen.below 4 with
  | 0 => return ⟨(l.eraseIdx at_).toArray⟩
  | 1 => return ⟨(l.insertIdx at_ c).toArray⟩
  | 2 => return ⟨(l.set at_ c).toArray⟩
  | _ => return b.extract 0 at_

def case : Gen Case := do
  let data ← dataGen
  let stream ← streamGen data
  let (op, body) ← match ← Gen.below 3 with
    | 0 => pure ("inflate", stream)
    | 1 => pure ("gunzip", Gzip.header ++ stream ++ le32 (Crc32.hash data) ++ le32 data.size.toUInt32)
    | _ => pure ("zlib", Zlib.header ++ stream ++ Zlib.be32 (Adler32.hash data))
  let body ← if ← Gen.chance 40 then byteMutate body else pure body
  return ⟨op, body⟩

/-- Python's `zlib.compress` and `gzip.compress`, at levels that write dynamic blocks. -/
def edges : List Case :=
  let h (op s : String) : Case := ⟨op, (Bytes.unhex? s).getD .empty⟩
  [ h "zlib" "78dacb48cdc9c957c8402701680308b1",
    h "inflate" "0300",
    h "inflate" "010000ffff",
    h "inflate" "",
    h "gunzip" "1f8b08000000000002ffcb48cdc9c957c8402701e3513d8d17000000",
    h "gunzip" "1f8b08200000000002ffcb48cdc9c957c8402701e3513d8d17000000",
    h "gunzip" ("1f8b08000000000002ffcb48cdc9c957c8402701e3513d8d17000000"
      ++ "1f8b08000000000002ffcb48cdc9c957c8402701e3513d8d17000000"),
    h "inflate" ("a5d43b0ec2301444d13eab784a8d046ff84632e959061fa3587288141b65fbb002286e33dded8e26"
      ++ "e464f77c2de5dca61ac7b6bf7cd75eeff11667dbd8f4b43a44cba9d4952da90eb64cf3a384754e7d137eb5"
      ++ "0e5a81760bda1d68f7a03d80f608da13683b6203c122b29cd07262cb092e27ba9cf072e2cb093027c24484"
      ++ "097d171126224c44988830116122c24484e98fb00f") ]

/-- RFC 1952 has a decoder refuse a header with a reserved flag set; Go reads it. -/
def reservedFlag (c : Case) : Bool :=
  c.op == "gunzip" && (c.input[3]?.getD 0) &&& 0xe0 != 0

def package : Package where
  name := "flate"
  edges := edges
  case := case
  answer := answer
  shrinks := false
  recorded := 300
  known c _ :=
    if reservedFlag c then some "a gzip header with a reserved flag: RFC 1952 refuses it, Go reads it"
    else none

end Tests.Oracle.Compress
