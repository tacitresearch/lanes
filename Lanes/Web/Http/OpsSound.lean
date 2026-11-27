/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Lib.Encoding.Json.ParserSound
public import Lanes.Web.Http.Ops

/-!
A line of the access log is the JSON text of its record, from what the JSON parser is proved to
read back (`Json.parse_compress`). Its own module, so that the server does not import the
parser's proofs.
-/

@[expose] public section

namespace Lanes.Http.Ops

/-- A line of the access log is the JSON text of its record: the parser reads it back. -/
theorem Access.parse_line (a : Access) :
    Json.parse a.line 1 a.json.digits = .ok a.json.normalize :=
  Json.parse_compress a.json (by simp [Access.json, Json.depth]) (Nat.le_refl _)

end Lanes.Http.Ops
