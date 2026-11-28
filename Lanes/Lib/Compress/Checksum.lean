/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std

/-!
# CRC-32 and Adler-32

The checksums of gzip (CRC-32, ISO 3309, RFC 1952 §8) and zlib (Adler-32, RFC 1950 §9). CRC-32 is
computed a byte at a time from a table of 256 entries, which is the bitwise definition
(`Crc32.bitwise`) applied to each byte; the two are compared on every byte and on test vectors
(`Tests/Compress.lean`).
-/

@[expose] public section

namespace Lanes

namespace Crc32

/-- The reflected polynomial of CRC-32. -/
def poly : UInt32 := 0xEDB88320

/-- Eight rounds of the bitwise definition on one value. -/
def rounds (c : UInt32) : UInt32 :=
  (List.range 8).foldl (fun c _ => if c &&& 1 == 1 then poly ^^^ (c >>> 1) else c >>> 1) c

def table : Array UInt32 :=
  (Array.range 256).map fun n => rounds n.toUInt32

/-- The CRC-32 of `data` continued from `crc`, the CRC-32 of what came before. -/
def update (crc : UInt32) (data : ByteArray) : UInt32 :=
  ~~~(data.foldl (fun c b => table[((c ^^^ b.toUInt32) &&& 0xff).toNat]! ^^^ (c >>> 8)) (~~~crc))

def hash (data : ByteArray) : UInt32 :=
  update 0 data

/-- The definition, a bit at a time, for tests. -/
def bitwise (data : ByteArray) : UInt32 :=
  ~~~(data.foldl (fun c b => rounds (c ^^^ b.toUInt32)) 0xFFFFFFFF)

end Crc32

namespace Adler32

def base : UInt32 := 65521

/-- The Adler-32 of `data`. Each sum is taken modulo 65521 every 5552 bytes, the most that can be
added before a sum passes 2³². -/
def hash (data : ByteArray) : UInt32 :=
  let (a, b, _) := data.foldl (init := ((1 : UInt32), (0 : UInt32), (0 : Nat))) fun (a, b, n) x =>
    let a := a + x.toUInt32
    let b := b + a
    if n + 1 == 5552 then (a % base, b % base, 0) else (a, b, n + 1)
  ((b % base) <<< 16) ||| (a % base)

end Adler32

end Lanes
