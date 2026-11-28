/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Lib.Encoding.Json.ParserSound
public import Lanes.Lib.Log

/-!
What a rendered log line is: one line, since it holds no control character
(`Log.render_printable`), and the JSON text of its record, which the JSON parser reads back
(`Log.parse_render`). Escaping is what makes both hold whatever a message or an attribute holds:
a newline, a quote or a control character in a string is written escaped.
-/

@[expose] public section

namespace Lanes.Log

/-- A line holds no control character, whatever its record holds. -/
theorem render_printable (r : Record) : ∀ c ∈ (render r).toList, Json.Printable c :=
  Json.compress_printable r.json

/-- A record is one line: no newline and no carriage return. -/
theorem render_oneLine (r : Record) : '\n' ∉ (render r).toList ∧ '\r' ∉ (render r).toList :=
  ⟨fun h => absurd (render_printable r _ h) (by decide),
   fun h => absurd (render_printable r _ h) (by decide)⟩

/-- A line is the JSON text of its record: the parser reads it back as the record's object, for
any record whose attributes nest within the parser's limits. -/
theorem parse_render (r : Record) {maxDepth maxDigits : Nat} (hd : r.json.depth ≤ maxDepth)
    (hm : r.json.digits ≤ maxDigits) :
    Json.parse (render r) maxDepth maxDigits = .ok r.json.normalize :=
  Json.parse_compress r.json hd hm

end Lanes.Log
