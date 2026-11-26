/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Data.ByteArray
public import Lanes.Data.List.Basic
public import Lanes.Data.List.Erase
public import Lanes.Data.List.Fold
public import Lanes.Data.List.Prefix
public import Lanes.Data.Utf8

/-!
Facts about lists, strings and byte arrays that proofs about systems share, one file per topic:
`List/Erase` (`erase` under `map`, `filter`, `filterMap` and `countP`), `List/Prefix` (`take`,
`drop`, prefixes, `afterFirst`), `List/Fold` (`foldlM` into `Option`), `List/Basic` (the rest),
`Utf8` (strings as bytes) and `ByteArray`. A new fact goes at the end of the file of its topic.
-/
