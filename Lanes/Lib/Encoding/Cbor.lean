/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Lib.Encoding.Cbor.Basic
public import Lanes.Lib.Encoding.Cbor.Encode
public import Lanes.Lib.Encoding.Cbor.Decode
public import Lanes.Lib.Encoding.Cbor.Classes
public import Lanes.Lib.Encoding.Cbor.Derive

/-!
# CBOR

CBOR (RFC 8949), the standard binary encoding of Lanes: the value type (`Lanes.Cbor`), the
preferred and the deterministic encodings (`Cbor.encode`, `Cbor.encodeDeterministic`), a decoder
with limits (`Cbor.decode`), the `ToCbor` and `FromCbor` classes, and what `lanes_data` derives
them from (`Cbor.Codec`). Its theorems are in `Lanes/Lib/Encoding/Cbor/Sound.lean`.

`import Lanes` does not import it: a program that does not import this module neither builds nor
links it.
-/
