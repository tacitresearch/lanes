/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Web.Http.Gate

/-!
How `Http.serve` recognises a journal written while the gate was an actor of the system
(`served sys`, `docs/decisions/D43-one-gate.md`). Such a journal holds every request that
arrived, and the gate's decisions were made again at every replay, so its name said which gate:
`journalName`. The server now makes those decisions before the shard and the journal holds only
what the gate admitted: it is named `admittedName`, which says nothing of the gate's settings,
and a journal named `journalName` is refused with a message that says why. The name is not the
application's alone, so that a journal of the server from before D43, which was, is refused too;
once a journal's manifest names its format (`docs/decisions/D97-data-format.md`, 3.3) it can be.
-/

@[expose] public section

namespace Lanes.Http

/-- The name of the journal of the application `system` served behind `gate`, when the gate was
an actor of the system. -/
def journalName (system : String) (gate : GateConfig) : String :=
  s!"{system}, behind a gate of {gate.requestTimeout_ms} ms and {gate.maxPending} requests"

/-- The gate a journal named `name` was written behind, if it is such a journal of `system`:
the one whose `journalName` it is. -/
def gateOf (system name : String) : Option GateConfig := do
  let rest ← name.dropPrefix? s!"{system}, behind a gate of "
  let rest ← rest.toString.dropSuffix? " requests"
  let [timeout, pending] := rest.toString.splitOn " ms and " | none
  let gate : GateConfig := { requestTimeout_ms := ← timeout.toNat?, maxPending := ← pending.toNat? }
  if journalName system gate == name then some gate else none

/-- The name of the journal of the application `system` served with the gate before the shard:
it holds only the requests the gate admitted. -/
def admittedName (system : String) : String :=
  s!"{system}, admitted"

end Lanes.Http
