/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Lib.LogSound
public import Lanes.Web.Http.Ops

/-!
A line of the access log is one line, the JSON text of its record, from what is proved of every
log line (`Log.render_oneLine`, `Log.parse_render`). Its own module, so that the server does not
import the parser's proofs.
-/

@[expose] public section

namespace Lanes.Http.Ops

/-- A line of the access log is the JSON text of its record: the parser reads it back. -/
theorem Access.parse_line (a : Access) :
    Json.parse a.line 1 a.json.digits = .ok a.json.normalize :=
  Log.parse_render a.record
    (by simp [Access.record, Log.Record.json, Json.depth]) (Nat.le_refl _)

/-- A line of the access log is one line. -/
theorem Access.oneLine (a : Access) : '\n' ∉ a.line.toList :=
  (Log.render_oneLine a.record).1

end Lanes.Http.Ops
