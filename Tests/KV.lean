/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Examples.KV

/-!
Refinement checks of the key-value store against its service spec, on one key, two values and
two front ends. The driver sends a read, a write and a second read; the monitor checks every
response against the map spec.
-/

namespace Tests.KV

open Lanes Examples.KV

abbrev K := Fin 1
abbrev V := Fin 2
abbrev F := Fin 2

instance : (sig K V F).Inspect := by instance_by_cases
instance (caching : Bool) : (system K V F caching).Inspect := by instance_by_cases

/-- Read through front end 0, write through front end 1, read through front end 0 again. -/
def requests : List (Request K V F) :=
  [⟨1, 0, .get 0⟩, ⟨2, 1, .put 0 1⟩, ⟨3, 0, .get 0⟩]

abbrev W (caching : Bool) :=
  World (system K V F caching) (List (Request K V F) × Check.Monitor (sig K V F) (K → Option V))

def props (caching : Bool) : List (Check.Property (W caching)) :=
  [ Check.refines "every response is allowed by the map spec",
    .sometimes "a read sees the written value" fun w =>
      w.state.outbox.any fun r => r.res == .value (some 1),
    .sometimes "a read sees the empty store" fun w =>
      w.state.outbox.any fun r => r.res == .value none ]

def check (caching : Bool) :=
  Check.system (system K V F caching)
    { driver := (spec K V F).monitored (Driver.anyOrder requests) } (props caching)

def tests : List (String × Bool) :=
  let plain := check false
  let cached := check true
  [ ("kv: without caching the store refines the map spec",
      plain.ok && plain.complete),
    ("kv: the check is not vacuous: reads see both the empty store and the written value",
      plain.witnesses.length == 2),
    ("kv: read caching breaks refinement: a stale read after an acknowledged write",
      match cached.failure with
      | some (.violated "every response is allowed by the map spec" t) =>
        (match t.labels.getLast? with
          | some (.output ⟨3, .value none⟩) => true
          | _ => false)
      | _ => false) ]

end Tests.KV
