/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Lib.Encoding.Cbor.Encode

/-!
# Reading CBOR

`Cbor.decode cfg bytes` reads one item that is the whole of `bytes`, and refuses what is not
well-formed (RFC 8949 §3, Appendix F): input cut short, additional information 28 to 30, an
indefinite length on an integer, a tag or a simple value, a chunk of an indefinite-length string
that is not a definite string of its type, a break outside an indefinite-length item, a simple
value below 32 in two bytes, text that is not UTF-8, and bytes after the item.

Its limits (`Config`, rule 2.6) are checked as it reads, before it reads further: the whole input,
the nesting of arrays, maps and tags, and the bytes of a string or the entries of an array or a
map.

`Config.accept` says which encodings of a value it takes: any well-formed one, only the preferred
serialization (`encode`'s), or only the deterministic encoding (`encodeDeterministic`'s). The two
strict ones read, then write what they read and compare: an input is taken exactly when it is the
bytes the encoder writes for its value, which is what makes each value have one accepted
encoding.
-/

@[expose] public section

namespace Lanes.Cbor

/-- Which encodings of a value the decoder takes. -/
inductive Accept where
  /-- Any well-formed encoding: arguments longer than needed, indefinite lengths. -/
  | wellFormed
  /-- Only the preferred serialization (§4.1), as `encode` writes it. -/
  | preferred
  /-- Only the deterministic encoding (§4.2.1), as `encodeDeterministic` writes it. -/
  | deterministic
  deriving DecidableEq, Repr, Inhabited

structure Config where
  /-- The most levels of arrays, maps and tags, the item itself counted. -/
  maxDepth : Nat := 64
  /-- The most bytes in a string, or entries in an array or a map. -/
  maxLength : Nat := 2 ^ 24
  /-- The most bytes of input. -/
  maxSize : Nat := 2 ^ 26
  accept : Accept := .wellFormed
  deriving Repr, Inhabited

inductive Error where
  /-- The input ends inside an item. -/
  | truncated
  /-- Additional information 28, 29 or 30. -/
  | reserved
  /-- An indefinite length on an integer, a tag or a chunk. -/
  | indefinite
  /-- A chunk of an indefinite-length string that is not a string of the same type. -/
  | badChunk
  /-- A break where an item was expected. -/
  | unexpectedBreak
  /-- A simple value below 32 written in two bytes. -/
  | badSimple
  | invalidUtf8
  /-- Bytes after the item. -/
  | trailing
  | tooDeep
  | tooLong
  | tooLarge
  | notPreferred
  | notDeterministic
  deriving DecidableEq, Repr, Inhabited

/-- The number the `width` bytes at `pos` spell, most significant first. -/
def readArgument (bytes : ByteArray) (pos width : Nat) : Nat :=
  Digits.join 256 ((bytes.extract pos (pos + width)).data.toList.map UInt8.toNat)

/-- The head at `pos`: the major type, the additional information, the argument it gives, and
where the head ends. -/
def readHead (bytes : ByteArray) (pos : Nat) : Except Error (Nat × Nat × Nat × Nat) :=
  match bytes[pos]? with
  | none => .error .truncated
  | some b =>
    let major := b.toNat / 32
    let info := b.toNat % 32
    if info < 24 then .ok (major, info, info, pos + 1)
    else if info < 28 then
      let width := 2 ^ (info - 24)
      if pos + 1 + width ≤ bytes.size then
        .ok (major, info, readArgument bytes (pos + 1) width, pos + 1 + width)
      else .error .truncated
    else if info < 31 then .error .reserved
    else .ok (major, info, 0, pos + 1)

/-- The `n` bytes of a string at `pos`. -/
def readString (cfg : Config) (bytes : ByteArray) (n pos : Nat) : Except Error (ByteArray × Nat) :=
  if cfg.maxLength < n then .error .tooLong
  else if bytes.size < pos + n then .error .truncated
  else .ok (bytes.extract pos (pos + n), pos + n)

/-- The chunks of an indefinite-length string of major type `major` up to its break, after
`acc` (§3.2.3). Each chunk of text is UTF-8 on its own. `fuel` only bounds the loop: each chunk
takes a byte. -/
def readChunks (cfg : Config) (bytes : ByteArray) (major : Nat) :
    (fuel pos : Nat) → (acc : ByteArray) → Except Error (ByteArray × Nat)
  | 0, _, _ => .error .truncated
  | fuel + 1, pos, acc =>
    if bytes[pos]? = some 0xff then .ok (acc, pos + 1)
    else
      match readHead bytes pos with
      | .error e => .error e
      | .ok (m, info, n, next) =>
        if m ≠ major then .error .badChunk
        else if info = 31 then .error .indefinite
        else if cfg.maxLength < acc.size + n then .error .tooLong
        else
          match readString cfg bytes n next with
          | .error e => .error e
          | .ok (chunk, next) =>
            if major = 3 ∧ (String.fromUTF8? chunk).isNone then .error .invalidUtf8
            else readChunks cfg bytes major fuel next (acc ++ chunk)

/-- `count` items read by `read` one after the other, after `acc`, which is reversed. -/
def readMany {α : Type} (read : Nat → Except Error (α × Nat)) :
    (count pos : Nat) → (acc : List α) → Except Error (List α × Nat)
  | 0, pos, acc => .ok (acc.reverse, pos)
  | count + 1, pos, acc =>
    match read pos with
    | .error e => .error e
    | .ok (x, next) => readMany read count next (x :: acc)

/-- Items read by `read` up to a break, after the `count` in `acc`, which is reversed. -/
def readUntilBreak {α : Type} (cfg : Config) (bytes : ByteArray) (read : Nat → Except Error (α × Nat)) :
    (fuel pos count : Nat) → (acc : List α) → Except Error (List α × Nat)
  | 0, _, _, _ => .error .truncated
  | fuel + 1, pos, count, acc =>
    if bytes[pos]? = some 0xff then .ok (acc.reverse, pos + 1)
    else if cfg.maxLength ≤ count then .error .tooLong
    else
      match read pos with
      | .error e => .error e
      | .ok (x, next) => readUntilBreak cfg bytes read fuel next (count + 1) (x :: acc)

/-- The items of an array or the entries of a map: `n` of them, or up to a break. -/
def readItems {α : Type} (cfg : Config) (bytes : ByteArray) (read : Nat → Except Error (α × Nat))
    (info n pos : Nat) : Except Error (List α × Nat) :=
  if info = 31 then readUntilBreak cfg bytes read bytes.size pos 0 []
  else if cfg.maxLength < n then .error .tooLong
  else readMany read n pos []

def readPair {α : Type} (read : Nat → Except Error (α × Nat)) (pos : Nat) :
    Except Error ((α × α) × Nat) :=
  match read pos with
  | .error e => .error e
  | .ok (k, next) =>
    match read next with
    | .error e => .error e
    | .ok (v, next) => .ok ((k, v), next)

/-- An item of major type 7 (§3.3). -/
def special (info n : Nat) : Except Error Cbor :=
  if info = 20 then .ok (.bool false)
  else if info = 21 then .ok (.bool true)
  else if info = 22 then .ok .null
  else if info = 23 then .ok .undefined
  else if info = 25 then .ok (.float (ofHalf n.toUInt16))
  else if info = 26 then .ok (.float (ofSingle n.toUInt32))
  else if info = 27 then .ok (.float n.toUInt64)
  else if info = 31 then .error .unexpectedBreak
  else if h : n < 20 ∨ (32 ≤ n ∧ n < 256) then
    .ok (.simple ⟨n.toUInt8, by
      rcases h with h | h
      · exact .inl (UInt8.lt_iff_toNat_lt.mpr (by simp; omega))
      · exact .inr (UInt8.le_iff_toNat_le.mpr (by simp; omega))⟩)
  else .error .badSimple

def readText (b : ByteArray) : Except Error Cbor :=
  match String.fromUTF8? b with
  | some s => .ok (.text s)
  | none => .error .invalidUtf8

/-- The item at `pos`, within `depth` levels, and where it ends. -/
def item (cfg : Config) (bytes : ByteArray) : (depth pos : Nat) → Except Error (Cbor × Nat)
  | 0, _ => .error .tooDeep
  | depth + 1, pos =>
    match readHead bytes pos with
    | .error e => .error e
    | .ok (major, info, n, pos) =>
      match major with
      | 0 => if info = 31 then .error .indefinite else .ok (.uint n.toUInt64, pos)
      | 1 => if info = 31 then .error .indefinite else .ok (.nint n.toUInt64, pos)
      | 2 =>
        match (if info = 31 then readChunks cfg bytes 2 bytes.size pos .empty
          else readString cfg bytes n pos) with
        | .error e => .error e
        | .ok (b, pos) => .ok (.bytes b, pos)
      | 3 =>
        match (if info = 31 then readChunks cfg bytes 3 bytes.size pos .empty
          else readString cfg bytes n pos) with
        | .error e => .error e
        | .ok (b, pos) => (readText b).map (·, pos)
      | 4 =>
        match readItems cfg bytes (item cfg bytes depth) info n pos with
        | .error e => .error e
        | .ok (items, pos) => .ok (.array items, pos)
      | 5 =>
        match readItems cfg bytes (readPair (item cfg bytes depth)) info n pos with
        | .error e => .error e
        | .ok (entries, pos) => .ok (.map entries, pos)
      | 6 =>
        if info = 31 then .error .indefinite
        else
          match item cfg bytes depth pos with
          | .error e => .error e
          | .ok (v, pos) => .ok (.tag n.toUInt64 v, pos)
      | _ => (special info n).map (·, pos)

/-- The item that is the whole of `bytes`. -/
def decode (cfg : Config) (bytes : ByteArray) : Except Error Cbor :=
  if cfg.maxSize < bytes.size then .error .tooLarge
  else
    match item cfg bytes cfg.maxDepth 0 with
    | .error e => .error e
    | .ok (v, pos) =>
      if pos ≠ bytes.size then .error .trailing
      else
        match cfg.accept with
        | .wellFormed => .ok v
        | .preferred => if encode v = bytes then .ok v else .error .notPreferred
        | .deterministic =>
          if encodeDeterministic v = bytes then .ok v else .error .notDeterministic

end Lanes.Cbor
