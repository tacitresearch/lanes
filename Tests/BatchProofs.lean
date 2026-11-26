/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Semantics
import Tests.Batch

/-!
The server of `Tests/Batch.lean` implements its service, for every service and under every
environment that does not hand a request over twice, lossy links and crashes included.

It has no refinement mapping: one step of it is several of the service, and a lost request
stays pending in the service. So `Refines.of_map` does not apply; the standard simulation
(`Lanes.Account`) does, with the queue held in the server's state and a flush the queue taking
effect. `System.Refines.to_ghost` and `of_ghost` carry the result to the
server with its history and back. Built by `lake build`, not linked into the test executable.
-/

namespace Tests.Batch

open Lanes Cslib

variable {In Out S : Type} [DecidableEq In] [DecidableEq Out]

omit [DecidableEq In] [DecidableEq Out] in
theorem serve_eq_run (svc : Service In Out S) (s : S) (queue : List In) :
    serve svc s queue = svc.run s queue := by
  induction queue generalizing s with
  | nil => rfl
  | cons x queue ih => simp [serve, Service.run, ih]

/-- The requests still to be served are pending in the service: those on their way and those
queued. -/
def account (svc : Service In Out S) : Account (system svc) S Unit where
  pend e := match (e.msg : Msg In) with
    | .request x => some x
    | .flush => none
  held state _ := ↑(state ()).2
  value state _ _ v := v = (state ()).1

/-- A request joins the queue, and a flush is the queue taking effect. -/
theorem handles {svc : Service In Out S} (state : (i : Unit) → S × List In)
    (net net' : List (Envelope (sig In Out))) (src : Option Unit) (m : Msg In) :
    (account svc).Handles svc state net net' () ((actor svc).step (state ()) m)
      ((account svc).pend ⟨src, (), m⟩) none := by
  rintro _ _ rfl
  cases m with
  | request x =>
    exact ⟨(), [], rfl, le_of_eq (by simp [account, actor, add_comm, ← Multiset.coe_add]), by simp [account, actor]⟩
  | flush =>
    exact ⟨(), (state ()).2, by simp [account, actor, serve_eq_run], by simp [account, actor],
      by simp [account, actor, serve_eq_run]⟩

theorem implements (svc : Service In Out S) (env : EnvModel (sig In Out))
    (henv : (env.link none ()).duplicating = false) : (system svc).Implements env svc := by
  refine (account svc).implements (inv := fun _ => True) (fun _ _ => trivial)
    ⟨(), by simp [account, SysState.init, SysState.startActor, SysState.settle, SysState.blank,
      SysState.perform, Effect.isStop, actor], by simp [Account.pending, account, SysState.init,
      SysState.startActor, SysState.settle, SysState.blank, SysState.perform, Effect.isStop, actor],
      by simp [Account.owed, account, SysState.init, SysState.startActor, SysState.settle,
        SysState.blank, SysState.perform, Effect.isStop, actor]⟩
    (fun _ => ⟨rfl, rfl⟩) (fun _ _ _ _ _ h => h)
    (fun c ⟨src, ⟨⟩, m⟩ _ _ hd => .handle (SysState.mem_of_deliverable hd) (handles _ _ _ src m))
    ?_
    (fun _ _ _ _ _ _ => .of_loses ⟨rfl, List.erase_sublist, fun _ _ h => h, rfl⟩ fun _ _ h => h)
    (fun c i _ => .of_loses (SysState.Loses.down env c i) fun _ _ h => h)
    (fun c ⟨⟩ m _ h _ => by
      obtain rfl : m = .flush := by cases h <;> rename_i h <;> cases ‹Msg In› <;> simp_all [actor]
      exact .grow (handles _ _ _ none .flush))
    (fun c ⟨⟩ _ => .quiet (fun _ _ h => by simpa [account] using h) rfl rfl (fun _ => by simp)
      (fun _ => rfl))
  rintro c ⟨src, ⟨⟩, m⟩ _ hsent _ hdup
  obtain rfl : src = none := by
    cases hsent with
    | accept => rfl
    | step s msg h => cases msg <;> simp [actor] at h
    | recover s h => simp [actor] at h
  simp [henv] at hdup

/-- The same of the server that remembers every state it has been in, and back. -/
theorem implements_withPast (svc : Service In Out S) (env : EnvModel (sig In Out))
    (henv : (env.link none ()).duplicating = false) :
    (system svc).withPast.Implements env svc :=
  System.Refines.to_ghost _ (implements svc env henv)

example (svc : Service In Out S) (env : EnvModel (sig In Out))
    (henv : (env.link none ()).duplicating = false) : (system svc).Implements env svc :=
  System.Refines.of_ghost (.past _) (implements_withPast svc env henv)

end Tests.Batch
