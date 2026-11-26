/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
Tests of the journal's framing: the bytes of a frame, the round trip, a file cut at every
length, a damaged byte at every position, and bytes after good frames. The theorems in
`Lanes/Data/Frame.lean` say the same of every file; these run the compiled code.
-/

namespace Tests.Frame

open Lanes

def bytes (values : List Nat) : ByteArray :=
  ⟨(values.map Nat.toUInt8).toArray⟩

def everyByte : ByteArray :=
  bytes (List.range 256)

def payloads : List ByteArray :=
  ["first".toUTF8, .empty, everyByte, .empty, "last".toUTF8]

def three : List ByteArray :=
  ["one".toUTF8, everyByte, "three".toUTF8]

def flip (file : ByteArray) (i : Nat) : ByteArray :=
  file.set! i (file[i]! ^^^ 1)

/-- The index of the frame of `three` that byte `i` of its file belongs to. -/
def frameOf (i : Nat) : Nat :=
  ((List.range 3).filter fun k => (Frame.encode (three.take (k + 1))).size ≤ i).length

def payloadByte (i : Nat) : Bool :=
  8 ≤ i - (Frame.encode (three.take (frameOf i))).size

def stopsAtDamagedFrame (i : Nat) : Bool :=
  Frame.decode (flip (Frame.encode three) i) == three.take (frameOf i)

def positions : List Nat :=
  List.range (Frame.encode three).size

def junk : List ByteArray :=
  [ bytes [0], bytes [0, 0, 0, 0, 0, 0, 0], bytes [0, 0, 0, 0, 0, 0, 0, 0],
    bytes [255, 255, 255, 255, 255, 255, 255, 255, 255],
    (Frame.one everyByte).extract 0 200, (Frame.one everyByte).extract 1 264, everyByte ]

def many : List ByteArray :=
  (List.range 20000).map fun i => bytes ((List.range 100).map (· + i))

def tests : List (String × Bool) := [
  ("frame: the checksum is FNV-1a on its test vectors",
    Frame.checksum .empty == 0x811c9dc5 && Frame.checksum "a".toUTF8 == 0xe40c292c
      && Frame.checksum "foobar".toUTF8 == 0xbf9cf968),
  ("frame: a frame is length, checksum, payload",
    Frame.one "a".toUTF8 == bytes [0, 0, 0, 1, 0xe4, 0x0c, 0x29, 0x2c, 0x61]
      && Frame.one .empty == bytes [0, 0, 0, 0, 0x81, 0x1c, 0x9d, 0xc5]
      && (Frame.one everyByte).extract 0 4 == bytes [0, 0, 1, 0]),
  ("frame: payloads round trip, empty and every byte value included",
    Frame.decode (Frame.encode payloads) == payloads && Frame.decode (Frame.encode []) == []
      && Frame.decode (Frame.one .empty) == [.empty]),
  ("frame: appending frames appends records",
    Frame.encode (payloads ++ three) == Frame.encode payloads ++ Frame.encode three
      && Frame.decode (Frame.encode payloads ++ Frame.encode three) == payloads ++ three),
  ("frame: a file cut at any length decodes to the frames that are whole",
    (List.range ((Frame.encode three).size + 2)).all fun n =>
      let decoded := Frame.decode ((Frame.encode three).extract 0 n)
      decoded.isPrefixOf three && decoded == three.take (Frame.whole three n)
        && decoded.length == frameOf n),
  ("frame: every cut is seen, from no frame to all three",
    (List.range 4).all fun k => (positions ++ [positions.length]).any fun n =>
      (Frame.decode ((Frame.encode three).extract 0 n)).length == k),
  ("frame: a flipped payload byte stops decoding at that frame",
    (positions.filter payloadByte).length == 264
      && (positions.filter payloadByte).all stopsAtDamagedFrame),
  ("frame: a flipped length or checksum byte stops decoding at that frame",
    (positions.filter (!payloadByte ·)).length == 24
      && (positions.filter (!payloadByte ·)).all stopsAtDamagedFrame),
  ("frame: a frame with another checksum is not decoded, nor what follows it",
    Frame.decode (Frame.encode payloads ++ Frame.stamped 0 everyByte ++ Frame.encode three)
      == payloads),
  ("frame: bytes after good frames leave them as they are",
    junk.all fun rest => payloads.isPrefixOf (Frame.decode (Frame.encode payloads ++ rest))),
  ("frame: bytes that are no frame decode to nothing",
    junk.all fun rest => Frame.decode rest == []),
  ("frame: twenty thousand frames round trip",
    Frame.decode (Frame.encode many) == many),
  ("frame: a payload fits when its length does",
    Frame.fits .empty && Frame.fits everyByte && payloads.all Frame.fits)
]

end Tests.Frame
