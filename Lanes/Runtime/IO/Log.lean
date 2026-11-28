/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std.Time
public import Lanes.Lib.Log

/-!
The IO of logs: a line written to its sink, and a logger that stamps a record with the wall
clock and writes it if its level is high enough. What a line holds is `Log.render`'s, pure and
proved (`Lanes/Lib/LogSound.lean`).
-/

public section

namespace Lanes.Log

/-- Milliseconds since the epoch, by the wall clock; `0` if it cannot be read. -/
def wallMs : BaseIO Nat := do
  match ← Std.Time.Timestamp.now.toBaseIO with
  | .ok t => return t.toMillisecondsSinceUnixEpoch.toInt.toNat
  | .error _ => return 0

/-- A line and its newline, written at once and flushed. A failed write is dropped: a log never
stops what it reports on. -/
def Sink.write (sink : Sink) (line : String) : BaseIO Unit :=
  match sink with
  | .off => pure ()
  | .stderr =>
    let put : IO Unit := do
      let err ← IO.getStderr
      err.putStr (line ++ "\n")
      err.flush
    discard put.toBaseIO
  | .call f => discard (f line).toBaseIO

/-- Where records go, from which level, and what each carries: the attributes and the request
of its context. -/
structure Logger where
  sink : Sink := .stderr
  level : Level := .info
  attrs : List (String × Json) := []
  requestId : Option String := none

namespace Logger

/-- The logger whose records also carry `attrs`. -/
def withAttrs (l : Logger) (attrs : List (String × Json)) : Logger :=
  { l with attrs := l.attrs ++ attrs }

/-- The logger whose records are about the request with this id. -/
def withRequest (l : Logger) (id : String) : Logger :=
  { l with requestId := some id }

def log (l : Logger) (level : Level) (msg : String) (attrs : List (String × Json) := []) :
    BaseIO Unit := do
  if l.sink.isOn && level.atLeast l.level then
    l.sink.write <| render
      { time_ms := ← wallMs, level, msg, attrs := l.attrs ++ attrs, requestId := l.requestId }

def debug (l : Logger) (msg : String) (attrs : List (String × Json) := []) : BaseIO Unit :=
  l.log .debug msg attrs

def info (l : Logger) (msg : String) (attrs : List (String × Json) := []) : BaseIO Unit :=
  l.log .info msg attrs

def warn (l : Logger) (msg : String) (attrs : List (String × Json) := []) : BaseIO Unit :=
  l.log .warn msg attrs

def error (l : Logger) (msg : String) (attrs : List (String × Json) := []) : BaseIO Unit :=
  l.log .error msg attrs

end Logger

end Lanes.Log
