/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Proofs
import Reminders.App

/-!
# What holds of the reminders

Every transaction of the reminders keeps the table (`Reminders.keeps`): a request may add a
reminder or cancel one, and never changes what a reminder says. So the worker's theorems hold
of them, in every run, under every environment model (lost, repeated and reordered messages,
crashes and restarts of the worker), with lost `COMMIT`s and failed calls:

- a reminder is delivered only once every database the store may hold has it, with its text: a
  request whose transaction did not commit delivers nothing (`Reminders.delivered_committed`);
- at a notification service that honours idempotency keys, no reminder takes effect twice,
  however often it is delivered (`Reminders.delivered_once`).

What a claim, an attempt and a lease are, that a claim takes every reminder due, and that the
attempts of a reminder are bounded, is the jobs table's (`Lanes/Db/JobsSound.lean`).
-/

namespace Reminders

open Lanes Lanes.Db Lanes.Db.Jobs

variable (config : Config)

theorem answer_reads (notice : String) : (answer config notice).Reads :=
  Txn.Reads.bind (TableOf.scan_reads _ _) fun _ => .pure _

theorem answer_keeps (notice : String) : queue.Keeps (answer config notice) :=
  Queue.Keeps.of_reads (answer_reads config notice)

/-- Every transaction of the reminders keeps the table. -/
theorem keeps : ∀ x, queue.Keeps (handler config x)
  | .list => answer_keeps config _
  | .remind text due_ms => by
    simp only [handler, remind]
    split
    · exact answer_keeps config _
    · refine Queue.Keeps.bind (Queue.Keeps.of_reads (TableOf.scan_reads _ _)) fun js => ?_
      split
      · exact answer_keeps config _
      · refine Queue.Keeps.bind (Queue.Keeps.of_reads Queue.nextId_reads) fun id => ?_
        exact Queue.Keeps.bind (Queue.Keeps.map _ (Queue.enqueue_keeps _ _ _ _)) fun _ => answer_keeps config _
  | .cancel id => by
    simp only [handler, cancel]
    refine Queue.Keeps.bind (Queue.Keeps.of_reads (TableOf.get_reads _ _)) fun r => ?_
    cases r with
    | none => exact answer_keeps config _
    | some j =>
      refine Queue.Keeps.bind (Queue.cancel_keeps _) fun b => ?_
      cases b <;> exact answer_keeps config _

/-- **Only what committed is delivered.** In every run of the worker under every environment
model, beside any clients, the store's model with the reminders' transactions, and any
notification service, every reminder delivered is, with its text, in every database the store
may hold, also once any call still outstanding or lost takes effect. -/
theorem delivered_committed {D S E : Type} (clients : Outside (Worker.sig Action Answer String Nat) D)
    (dbcfg : Db.Config) (svc : Rpc.Server S (Idempotent.Keyed Int64 String) Nat E) (attempt_ms : Nat)
    (env : EnvModel (Worker.sig Action Answer String Nat)) {events : List (Event (Worker.sig Action Answer String Nat))}
    {c : SysState (Worker.system (Q := Action) (A := Answer) (W := String) (config.worker attempt_ms))}
    (hrun : (SysState.init (Worker.system (config.worker attempt_ms)) env).run env events = some c)
    {d : (D × Db.State (Action ⊕ Req) (Answer ⊕ Ans String)) × Rpc.State S}
    (hd : (Worker.world clients dbcfg (store config) (Db.empty schema) svc).after events = some d) :
    ∀ id lease dl text, Event.output (Worker.Out.run id lease dl text) ∈ events →
      Db.Holds (store config) (Worker.Holding queue id text) d.1.2 :=
  Worker.committed_only (cfg := config.worker attempt_ms) (app := handler config) (keeps config)
    (Queue.functional_empty _) env hrun hd

/-- **At most once.** At a notification service that honours idempotency keys, at most one
delivery of each reminder takes effect, in every run. -/
theorem delivered_once {D S E : Type} (clients : Outside (Worker.sig Action Answer String Nat) D)
    (dbcfg : Db.Config) (inner : Rpc.Server S String Nat E) (refusal : Nat → Bool)
    {events : List (Event (Worker.sig Action Answer String Nat))}
    {d : (D × Db.State (Action ⊕ Req) (Answer ⊕ Ans String)) × Rpc.State (Idempotent.State Int64 String Nat S)}
    (hd : (Worker.world clients dbcfg (store config) (Db.empty schema) (Idempotent.server inner refusal)).after events = some d)
    (id : Int64) : (d.2.server.slots.filter fun slot => slot.key == some id).length ≤ 1 :=
  Worker.once_each clients dbcfg (store config) _ inner refusal hd id

end Reminders
