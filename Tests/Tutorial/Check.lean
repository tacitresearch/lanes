/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Tests.Tutorial.Counter

/-!
Step 3 of `docs/TUTORIAL.md`: the model check of the app's `Check.lean`, run on the counter and
on the counter with the step's bug.
-/

namespace Tests.Tutorial

open Lanes Tut

instance : sig.Inspect := {}
instance : system.Inspect := {}

/-- The browser: the requests still to send, and what the front answered. -/
structure Browser where
  toSend : List (Nat × Request)
  answered : List (Nat × Response) := []
  deriving DecidableEq, Hashable

instance : BEq Browser := instBEqOfDecidableEq

def browser (requests : List (Nat × Request)) : Outside sig Browser where
  init := { toSend := requests }
  allow d
    | .request n r => if (n, r) ∈ d.toSend then some { d with toSend := d.toSend.erase (n, r) } else none
    | .store _ => none
  observe d
    | .answered n r => { d with answered := d.answered ++ [(n, r)] }
    | _ => d

def config : Config := { limit := 2 }

abbrev D := Browser × Db.State Request Response

def countsOf (db : Db.Db) : List Count := (db.rows counts.table.name).filterMap counts.ofRow

def requests : List (Nat × Request) := [(1, .increment), (2, .increment), (3, .decrement)]

/-- The bug the tutorial seeds: a decrement at one is refused. -/
def buggy (config : Config) : Db.Handler Request Response
  | .decrement => do
    let c ← current
    if 1 < c.value.toInt.toNat then
      let c := { c with value := Int64.ofNat (c.value.toInt.toNat - 1) }
      let _ ← counts.upsert c
      return ⟨c.value, true⟩
    else return ⟨c.value, false⟩
  | r => handler config r

def report (handler : Config → Db.Handler Request Response) :=
  let world := fun (requests : List (Nat × Request)) =>
    (browser requests).both (Db.outside {} (handler config) (Db.Db.empty schema) port)
      fun x => x matches .request ..
  let samples := fun (d : D) =>
    d.1.toSend.map (fun (n, r) => In.request n r) ++ Db.samples (handler config) port true true d.2
  Check.system system
    { env := { mayRestart := true }, driver := (world requests).driver samples, maxRestarts := 1 }
    [ .always "the count never passes its limit, in any database the store may hold" fun w =>
        w.driver.2.worlds.all fun world => (countsOf world.db).all (·.value.toInt ≤ config.limit),
      .sometimes "the count reaches its limit" fun w =>
        w.driver.2.worlds.any fun world => (countsOf world.db).any (·.value.toInt == config.limit),
      .always "a request is refused only at zero or at the limit" fun w =>
        w.driver.1.answered.all fun (_, r) => r.applied || r.value == 0 || r.value == 2,
      .sometimes "a decrement is refused" fun w =>
        w.driver.1.answered.any fun (_, r) => !r.applied && r.value == 0 ]
    {}

end Tests.Tutorial
