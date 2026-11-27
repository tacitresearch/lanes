/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Durable

/-!
A shard that ends on an error while commands it never took wait in its inbox. `failTest` in
`Tests/Durable.lean` sees this only when its commands happen to arrive after the shard took its
last batch; here the journal's second write holds the shard until they have, and then fails.
-/

namespace Tests.Ending

open Lanes Std Std.Async Tests.Fixtures.Bank Tests.Durable

def untakenTest : Async (List (String × Bool)) := do
  let calls ← IO.mkRef 0
  let writing ← IO.Promise.new
  let fail ← IO.Promise.new
  let log : Journal.Log Bank3 := {
    past := []
    append := fun _ => do
      if (← calls.modifyGet fun n => (n, n + 1)) ≥ 1 then
        writing.resolve ()
        discard <| IO.wait fail.result?
        throw (IO.userError "no room on the device")
    note := fun _ => pure ()
    close := pure () }
  let rt ← Runtime.start Bank3 {} (journal := some log)
  rt.input (.transfer ⟨100, 0, 1, 3⟩)
  rt.idle
  discard <| rt.tryInput (.transfer ⟨0, 0, 1, 3⟩)
  discard <| await writing.result?
  let waiters ← (List.range 4).mapM fun _ => do
    let done ← IO.Promise.new
    background do done.resolve (← throws rt.idle)
    return done
  Async.sleep 200
  fail.resolve ()
  let released ← waiters.mapM fun done => within 2000 (await done.result?)
  let error ← within 2000 rt.ended
  rt.stop
  return [
    ("ending: a shard that cannot write releases callers whose commands it never took",
      released.all (· == some (some true)) && (error.map (·.isSome)) == some true) ]

def tests : IO (List (String × Bool)) :=
  untakenTest.block

end Tests.Ending
