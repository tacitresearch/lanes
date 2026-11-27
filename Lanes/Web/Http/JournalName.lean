/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Durable.Upgrade
public import Lanes.Web.Http.Front

/-!
The name `Http.serve` gives its journal, and how it reads a journal it wrote behind another gate.

The gate is an actor of the system a journal replays, and its step function reads its
configuration. A request that found `maxPending` requests waiting was answered `503` and never
reached the system; replayed under a larger bound, or under a shorter `requestTimeout_ms` that
leaves fewer waiting, it is passed on, and the system applies a request its client was told
was refused (`docs/decisions/D36-what-a-durable-system-has-to.md`). So a journal is replayed
behind the gate that wrote it, and its name says which. A journal of the same application
written behind another gate is not refused: it is replayed behind its own gate, and the kernel
it gives goes on behind the new one as it is (`regate`), once, as any migration does
(`docs/decisions/D66-a-migration-carries-the-kernel-across.md`).
-/

@[expose] public section

namespace Lanes.Http

variable {σ : Signature}

/-- The name of the journal of the application `system` served behind `gate`. A field added to
`GateConfig` that its step function reads is added here and in `gateOf`. -/
def journalName (system : String) (gate : GateConfig) : String :=
  s!"{system}, behind a gate of {gate.requestTimeout_ms} ms and {gate.maxPending} requests"

/-- The gate a journal named `name` was written behind, if it is a journal of `system`: the one
whose `journalName` it is. -/
def gateOf (system name : String) : Option GateConfig := do
  let rest ← name.dropPrefix? s!"{system}, behind a gate of "
  let rest ← rest.toString.dropSuffix? " requests"
  let [timeout, pending] := rest.toString.splitOn " ms and " | none
  let gate : GateConfig := { requestTimeout_ms := ← timeout.toNat?, maxPending := ← pending.toNat? }
  if journalName system gate == name then some gate else none

/-- The gate other than `gate` that the journal named `name` of `system` was written behind. -/
def formerGate (system : String) (gate : GateConfig) (name : String) : Option GateConfig :=
  if name == journalName system gate then none else gateOf system name

/-- A kernel behind one gate is a kernel behind another: its states, messages and outputs have
the same types, and are carried as they are. Nothing is claimed of them after: the waiting
list may be longer than the new `maxPending` until it drains. -/
def regate (sys : System σ) (bridge : Bridge σ) (old new : GateConfig) :
    Migration (served sys bridge old) (served sys bridge new) where
  id i := i
  injective _ _ h := h
  state _ s := s
  msg _ m := m
  output o := o
  inv _ _ := True
  keeps _ := ⟨trivial, fun _ _ _ => trivial, fun _ _ => trivial⟩
  lands _ _ _ := trivial

/-- How `serve` reads the journal of `system` that it wrote behind the gate `old`: replayed
behind `old`, then carried behind `new`. -/
def regateUpgrade [Hashable σ.Id] (sys : System σ) (bridge : Bridge σ)
    (actors : Kernel.Image.Codecs sys) (out : Codec σ.Out) (system : String)
    (old new : GateConfig) : Journal.Upgrade (served sys bridge new) where
  old := served sys bridge old
  system := journalName system old
  input := Codec.pair Codec.nat Request.codec
  actors := some (servedActors actors out bridge old)
  migration := regate sys bridge old new

end Lanes.Http
