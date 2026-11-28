/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Lib.Encoding.Json.Printer
public import Lanes.Lib.Time.Format

/-!
# Structured logs

A record is a time, a level, a message, attributes and the request it is about; `render` writes
it as one line of JSON, with the fields in the order Go's `slog.JSONHandler` writes them: `time`,
`level`, `msg`, the attributes in order, then `request_id` when there is one. Rendering is pure;
`Lanes/Runtime/IO/Log.lean` writes lines. A line holds no control character, so no newline
(`Log.render_printable`), and the JSON parser reads it back as the record's value
(`Log.parse_render`), both in `Lanes/Lib/LogSound.lean`: whatever a message or an attribute holds,
a line is one line and one JSON object.

This module is in the lowest package (`LanesCli/Layers.lean`), with the JSON printer and the
time format it uses, so that the runtime logs through it.
-/

@[expose] public section

namespace Lanes.Log

inductive Level where
  | debug | info | warn | error
  deriving DecidableEq, Repr, Hashable, Inhabited

namespace Level

/-- As `slog` writes it. -/
def name : Level → String
  | .debug => "DEBUG"
  | .info => "INFO"
  | .warn => "WARN"
  | .error => "ERROR"

def rank : Level → Nat
  | .debug => 0
  | .info => 1
  | .warn => 2
  | .error => 3

/-- Whether a record at `l` is written by a logger at `least`. -/
def atLeast (l least : Level) : Bool :=
  least.rank ≤ l.rank

end Level

structure Record where
  /-- Milliseconds since the epoch, by the wall clock. -/
  time_ms : Nat
  level : Level
  msg : String
  attrs : List (String × Json) := []
  requestId : Option String := none
  deriving DecidableEq, Repr

/-- RFC 3339 in UTC, with milliseconds when there are any. -/
def time (time_ms : Nat) : String :=
  let dateTime := Civil.DateTime.ofUnix (time_ms / 1000 : Nat)
  let nanos : Fin 1000000000 := ⟨time_ms % 1000 * 1000000, by omega⟩
  (TimeFormat.printRfc3339? { dateTime, nanos, offset := ⟨0, by decide⟩ }).getD ""

def Record.json (r : Record) : Json :=
  .obj (#[("time", .str (time r.time_ms)), ("level", .str r.level.name), ("msg", .str r.msg)]
    ++ r.attrs.toArray ++ (r.requestId.map fun id => ("request_id", Json.str id)).toList.toArray)

def render (r : Record) : String :=
  r.json.compress

/-- Where lines go: nowhere, to standard error, or to a function. -/
inductive Sink where
  | off
  | stderr
  | call (write : String → IO Unit)

def Sink.isOn : Sink → Bool
  | .off => false
  | _ => true

end Lanes.Log
