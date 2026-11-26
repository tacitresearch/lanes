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

/-- The queue is served: it takes effect, from the network `net` the server leaves. -/
theorem flush_moves {svc : Service In Out S} {c : SysState (system svc)}
    {net : List (Envelope (sig In Out))} (hsub : net.Sublist c.net) :
    (account svc).Moves svc c
      (({ c with net := net }).grow () ((actor svc).step (c.state ()) .flush)) := by
  rintro _ v rfl
  refine ⟨(), (c.state ()).2, ?_, ?_, le_of_eq ?_⟩
  · simp [account, SysState.grow, actor, serve_eq_run]
  · simp only [Account.pending, account, SysState.grow, actor, update_self]
    rw [Effect.sends_append, Effect.sends_map_emit (σ := sig In Out) (i := ())]
    simp only [Effect.sends, List.filterMap_cons, List.filterMap_nil, List.append_nil,
      Multiset.coe_nil, add_zero]
    exact add_le_add (Multiset.coe_le.mpr (hsub.filterMap _).subperm) le_rfl
  · simp only [Account.owed, account, SysState.grow, actor]
    rw [Effect.emits_append, Effect.emits_map_emit (σ := sig In Out) (i := ()),
      Effect.sends_append, Effect.sends_map_emit (σ := sig In Out) (i := ())]
    simp [serve_eq_run, Effect.emits, Effect.sends]

/-- The one timer is `flush`, and requests come from outside. -/
def Tame {svc : Service In Out S} (c : SysState (system svc)) : Prop :=
  (∀ i m, m ∈ c.timers i → m = Msg.flush) ∧ ∀ e ∈ c.net, e.src = none

theorem tame_invariant (svc : Service In Out S) (env : EnvModel (sig In Out)) :
    (system svc).Invariant env Tame := by
  have htimers := System.Monotone.timers (system svc) (T := fun _ m => m = Msg.flush)
    (fun i s msg delay m h => by cases msg <;> simp_all [actor])
    (fun i s delay m h => by simp_all [actor])
  refine (htimers.and_net (fun _ h => nomatch h) ?_ ?_ ?_).invariant env
  · intro c up net timers outbox h hnet e he
    rcases hnet e he with he | ⟨x, rfl⟩
    · exact h e he
    · rfl
  · intro c i msg _ _ h _ e he
    rcases SysState.mem_grow_net.mp he with he | ⟨_, he⟩
    · exact h e he
    · cases msg <;> simp [actor] at he
  · intro c i _ _ h e he
    rcases SysState.mem_grow_net.mp he with he | ⟨_, he⟩
    · exact h e he
    · simp [actor] at he

theorem implements (svc : Service In Out S) (env : EnvModel (sig In Out))
    (henv : (env.link none ()).duplicating = false) : (system svc).Implements env svc := by
  refine (account svc).implements (tame_invariant svc env)
    ⟨(), by simp [account, SysState.init, SysState.startActor, SysState.settle, SysState.blank,
      SysState.perform, Effect.isStop, actor], by simp [Account.pending, account, SysState.init,
      SysState.startActor, SysState.settle, SysState.blank, SysState.perform, Effect.isStop, actor],
      by simp [Account.owed, account, SysState.init, SysState.startActor, SysState.settle,
        SysState.blank, SysState.perform, Effect.isStop, actor]⟩
    (fun _ => ⟨rfl, rfl⟩) (fun _ _ _ _ _ h => h) ?_ ?_
    (fun _ _ _ _ _ => .of_loses ⟨rfl, List.erase_sublist, fun _ _ h => h, rfl⟩ fun _ _ h => h)
    (fun c i _ => .of_loses (SysState.Loses.down env c i) fun _ _ h => h)
    (fun c ⟨⟩ m ⟨htimers, _⟩ hmem => by
      obtain rfl := htimers () m hmem
      exact flush_moves (List.Sublist.refl _))
    (fun c ⟨⟩ _ => .quiet (fun _ _ h => by simpa [account] using h) rfl rfl (fun _ => by simp)
      (fun _ => rfl))
  · rintro c ⟨src, ⟨⟩, m⟩ _ hd
    have hmem := SysState.mem_of_deliverable hd
    cases m with
    | request x =>
      refine .of_le fun _ v h => ⟨(), by simpa [account, SysState.grow, actor] using h,
        le_of_eq ?_, le_of_eq ?_⟩
      · simp only [Account.pending, account, SysState.grow, actor, update_self,
          Multiset.coe_eq_coe.mpr (filterMap_perm_erase hmem)]
        simp [Effect.sends, ← Multiset.coe_add]
        rw [← Multiset.cons_coe, ← Multiset.singleton_add]
        abel
      · simp [Account.owed, account, SysState.grow, actor, Effect.emits]
    | flush => exact flush_moves List.erase_sublist
  · rintro c ⟨src, ⟨⟩, m⟩ ⟨_, hnet⟩ hd hdup
    obtain rfl : src = none := hnet _ (SysState.mem_of_deliverable hd)
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
