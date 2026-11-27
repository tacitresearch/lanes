/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Lib.Encoding.Json.Basic
public import Lanes.Lib.Encoding.Json.Parser
public import Lanes.Lib.Encoding.Json.Printer
public import Lanes.Lib.Encoding.Json.Classes
public import Lanes.Lib.Encoding.Json.Grammar

/-!
# JSON

A JSON library that imports only `Std`, for runtime modules and adapters: the value type
(`Lanes.Json`), a parser (`Json.parse`), printers (`Json.compress`, `Json.pretty`) and the
`ToJson` and `FromJson` classes. It is a port of `Lean.Data.Json`, with total functions throughout.
-/
