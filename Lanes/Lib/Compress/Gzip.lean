/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Lib.Compress.Checksum
public import Lanes.Lib.Compress.Deflate

/-!
# gzip and zlib

The two wrappings of a DEFLATE stream that HTTP names: `gzip` (RFC 1952), a header, the stream,
its CRC-32 and its size; and `deflate`, which is zlib's (RFC 1950), two bytes, the stream and its
Adler-32. Reading checks the header, the checksum and the size, and is bounded by `max` as
`Inflate` is: what `Gzip.decompress` and `Zlib.decompress` return is at most `max` bytes
(`Gzip.size_le`, `Zlib.size_le`). A gzip body may hold several members, read one after another
as Go and zlib read them; anything else after the last is refused.
-/

@[expose] public section

namespace Lanes

open Inflate (Error)

def le32 (n : UInt32) : ByteArray :=
  ⟨#[n.toUInt8, (n >>> 8).toUInt8, (n >>> 16).toUInt8, (n >>> 24).toUInt8]⟩

/-- Four bytes from `i`, the first the lowest. -/
def readLe32 (data : ByteArray) (i : Nat) : Option UInt32 := do
  if i + 4 ≤ data.size then
    return data[i]!.toUInt32 ||| (data[i + 1]!.toUInt32 <<< 8) ||| (data[i + 2]!.toUInt32 <<< 16)
      ||| (data[i + 3]!.toUInt32 <<< 24)
  else none

namespace Gzip

/-- A header with no name, no time and no flags, from an unknown system. -/
def header : ByteArray := ⟨#[0x1f, 0x8b, 8, 0, 0, 0, 0, 0, 0, 255]⟩

def compress (data : ByteArray) : ByteArray :=
  header ++ Deflate.compress data ++ le32 (Crc32.hash data) ++ le32 data.size.toUInt32

/-- The byte after the zero that ends the text from `i`. -/
def afterZero (data : ByteArray) (i : Nat) : Option Nat :=
  go i (data.size - i + 1)
where
  go (j : Nat) : Nat → Option Nat
    | 0 => none
    | fuel + 1 => match data[j]? with
      | some 0 => some (j + 1)
      | some _ => go (j + 1) fuel
      | none => none

/-- Where the member's stream begins, after its header at `i`. -/
def skipHeader (data : ByteArray) (i : Nat) : Except Error Nat := do
  if i + 10 > data.size then throw .truncated
  if data[i]! != 0x1f || data[i + 1]! != 0x8b || data[i + 2]! != 8 then
    throw (.invalid "gzip header")
  let flags := data[i + 3]!.toNat
  if flags &&& 0xe0 != 0 then throw (.invalid "gzip flags")
  let mut at_ := i + 10
  if flags &&& 4 != 0 then
    if at_ + 2 > data.size then throw .truncated
    at_ := at_ + 2 + (data[at_]!.toNat ||| (data[at_ + 1]!.toNat <<< 8))
  if flags &&& 8 != 0 then
    let some j := afterZero data at_ | throw .truncated
    at_ := j
  if flags &&& 16 != 0 then
    let some j := afterZero data at_ | throw .truncated
    at_ := j
  if flags &&& 2 != 0 then
    if at_ + 2 > data.size then throw .truncated
    let crc := (Crc32.hash (data.extract i at_)).toNat &&& 0xffff
    if crc != (data[at_]!.toNat ||| (data[at_ + 1]!.toNat <<< 8)) then
      throw (.invalid "gzip header checksum")
    at_ := at_ + 2
  if at_ > data.size then throw .truncated
  return at_

/-- The members from `i` to the end, at most `fuel` of them. -/
def members (max : Nat) (data : ByteArray) : (fuel : Nat) → (i : Nat) → ByteArray →
    Except Error ByteArray
  | 0, _, _ => .error .truncated
  | fuel + 1, i, out => do
    let start ← skipHeader data i
    let (bytes, next) ← Inflate.inflateFrom (max - out.size) data start
    let some crc := readLe32 data next | throw .truncated
    let some size := readLe32 data (next + 4) | throw .truncated
    if crc != Crc32.hash bytes then throw (.invalid "gzip checksum")
    if size != bytes.size.toUInt32 then throw (.invalid "gzip size")
    let out := out ++ bytes
    if next + 8 == data.size then return out else members max data fuel (next + 8) out

/-- The bytes a gzip body holds, at most `max` of them. -/
def decompress (max : Nat) (data : ByteArray) : Except Error ByteArray :=
  members max data (data.size / 18 + 1) 0 .empty >>= fun out => Inflate.within max out

/-- What `decompress` returns has at most `max` bytes. -/
theorem size_le {max : Nat} {data out : ByteArray} (h : decompress max data = .ok out) :
    out.size ≤ max :=
  Inflate.size_le_of_bind (f := id) h

end Gzip

namespace Zlib

/-- Two bytes: DEFLATE with a window of 32 KiB, no dictionary, and the check bits. -/
def header : ByteArray := ⟨#[0x78, 0x9c]⟩

def be32 (n : UInt32) : ByteArray :=
  ⟨#[(n >>> 24).toUInt8, (n >>> 16).toUInt8, (n >>> 8).toUInt8, n.toUInt8]⟩

def compress (data : ByteArray) : ByteArray :=
  header ++ Deflate.compress data ++ be32 (Adler32.hash data)

/-- The bytes of a zlib stream, its header and checksum checked. -/
def read (max : Nat) (data : ByteArray) : Except Error ByteArray := do
  if data.size < 2 then throw .truncated
  let cmf := data[0]!.toNat
  let flg := data[1]!.toNat
  if cmf &&& 0x0f != 8 || cmf >>> 4 > 7 || (cmf * 256 + flg) % 31 != 0 then
    throw (.invalid "zlib header")
  if flg &&& 0x20 != 0 then throw (.invalid "zlib dictionary")
  let (out, next) ← Inflate.inflateFrom max data 2
  if next + 4 > data.size then throw .truncated
  let sum := (data[next]!.toUInt32 <<< 24) ||| (data[next + 1]!.toUInt32 <<< 16)
    ||| (data[next + 2]!.toUInt32 <<< 8) ||| data[next + 3]!.toUInt32
  if sum != Adler32.hash out then throw (.invalid "zlib checksum")
  return out

/-- The bytes a zlib stream holds, at most `max` of them. What follows the stream is ignored, as
Go and zlib ignore it. -/
def decompress (max : Nat) (data : ByteArray) : Except Error ByteArray :=
  read max data >>= fun out => Inflate.within max out

/-- What `decompress` returns has at most `max` bytes. -/
theorem size_le {max : Nat} {data out : ByteArray} (h : decompress max data = .ok out) :
    out.size ≤ max :=
  Inflate.size_le_of_bind (f := id) h

end Zlib

end Lanes
