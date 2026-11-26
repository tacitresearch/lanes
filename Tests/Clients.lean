/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Tests.KV

/-! `Driver.after` on the key-value store: a read sent once a write is answered must see it. -/

namespace Tests.Clients

open Lanes Examples.KV Tests.KV

/-- Read through front end 0; once that is answered, write through front end 1; once that is
answered, read through front end 0 again. -/
def script : List (Request K V F × List Nat) :=
  [(⟨1, 0, .get 0⟩, []), (⟨2, 1, .put 0 1⟩, [1]), (⟨3, 0, .get 0⟩, [2])]

def check (caching : Bool) :=
  Check.system (system K V F caching)
    { driver := (spec K V F).monitored (Driver.after (fun r => some r.req) script) }
    [Check.refines "every response is allowed by the map spec"]

def tests : List (String × Bool) :=
  let plain := check false
  let cached := check true
  [ ("clients: requests that wait for answers refine the map spec without a cache",
      plain.ok && plain.complete),
    ("clients: and a cache serves the stale read after the write was answered",
      match cached.failure with
      | some (.violated _ t) => t.labels.getLast? == some (.output ⟨3, .value none⟩)
      | _ => false),
    ("clients: the order cuts the states the checker visits",
      plain.states < (Tests.KV.check false).states) ]

end Tests.Clients
