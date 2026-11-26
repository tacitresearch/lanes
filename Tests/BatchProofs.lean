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
stays pending in the service. So `Refines.of_map` does not apply, and this is the small case of
`System.Refines.of_steps`. `System.Refines.to_ghost` and `of_ghost` carry the result to the
server with its history and back. Built by `lake build`, not linked into the test executable.
-/

namespace Tests.Batch

open Lanes Cslib

variable {In Out S : Type} [DecidableEq In] [DecidableEq Out]

def waiting (net : List (Envelope (sig In Out))) : List In :=
  net.filterMap fun e =>
    match (e.msg : Msg In) with
    | .request x => some x
    | .flush => none

theorem waiting_erase {net : List (Envelope (sig In Out))} {src : Option Unit} {x : In}
    (h : (⟨src, (), .request x⟩ : Envelope (sig In Out)) ∈ net) :
    (x ::ₘ ↑(waiting (net.erase ⟨src, (), .request x⟩)) : Multiset In) = ↑(waiting net) := by
  have hperm : (waiting net).Perm (x :: waiting (net.erase ⟨src, (), .request x⟩)) :=
    (List.perm_cons_erase h).filterMap _
  exact (Multiset.coe_eq_coe.mpr hperm).symm

/-- The requests still to be served are pending in the service: at least those on their way
and those queued. -/
structure Sim {svc : Service (sig In Out) S} (c : SysState (system svc))
    (t : Service.Abs (sig In Out) S) : Prop where
  value : t.value = (c.state ()).1
  outbox : t.outbox = ↑c.outbox
  pending : (↑(waiting c.net) : Multiset In) + ↑(c.state ()).2 ≤ t.pending

/-- The service serves a queue in as many internal steps as it is long. -/
theorem serves (svc : Service (sig In Out) S) (queue : List In) :
    ∀ (t : Service.Abs (sig In Out) S) (rest : Multiset In), rest + ↑queue ≤ t.pending →
      ∃ t', svc.spec.lts.τSTr t t' ∧ t'.value = (serve svc t.value queue).1 ∧
        t'.outbox = t.outbox + ↑(serve svc t.value queue).2 ∧ rest ≤ t'.pending := by
  induction queue with
  | nil => exact fun t rest h => ⟨t, .refl, rfl, by simp [serve], by simpa using h⟩
  | cons x queue ih =>
    intro t rest h
    rw [← Multiset.cons_coe, Multiset.add_cons] at h
    obtain ⟨t', ht', hvalue, houtbox, hrest⟩ := ih
      ⟨(svc.step t.value x).1, t.pending.erase x, t.outbox + (svc.step t.value x).2⟩ rest
      (by simpa using Multiset.erase_le_erase x h)
    refine ⟨t', .head ⟨x, Multiset.mem_of_le h (Multiset.mem_cons_self _ _), rfl⟩ ht', hvalue, ?_,
      hrest⟩
    rw [houtbox, serve, ← Multiset.coe_add, add_assoc]

namespace Sim

variable {svc : Service (sig In Out) S} {c : SysState (system svc)}
  {t : Service.Abs (sig In Out) S}

theorem loses {c' : SysState (system svc)} (h : Sim c t) (hl : c'.Loses c) : Sim c' t where
  value := by rw [hl.state]; exact h.value
  outbox := by rw [hl.outbox]; exact h.outbox
  pending := by
    rw [hl.state]
    exact (add_le_add_left (Multiset.coe_le.mpr (hl.net.filterMap _).subperm) _).trans h.pending

theorem recover (h : Sim c t) : Sim (c.grow () ((actor svc).recover (c.state ()))) t where
  value := by rw [SysState.grow_state_self]; exact h.value
  outbox := h.outbox.trans (congrArg _ (List.append_nil _).symm)
  pending := by
    rw [SysState.grow_state_self]
    show (↑(waiting (c.net ++ [])) : Multiset In) + ↑(c.state ()).2 ≤ t.pending
    rw [List.append_nil]
    exact h.pending

/-- The server handles `m`, taken from `net`, which is what was in flight without it. -/
theorem step (h : Sim c t) {net : List (Envelope (sig In Out))} (m : Msg In)
    (hsub : net.Sublist c.net)
    (htaken : ∀ x, m = .request x → (x ::ₘ ↑(waiting net) : Multiset In) ≤ ↑(waiting c.net)) :
    ∃ t', svc.spec.lts.τSTr t t' ∧
      Sim (({ c with net := net }).grow () ((actor svc).step (c.state ()) m)) t' := by
  have hless : (↑(waiting net) : Multiset In) ≤ ↑(waiting c.net) :=
    Multiset.coe_le.mpr (hsub.filterMap _).subperm
  cases m with
  | request x =>
    refine ⟨t, .refl, by rw [SysState.grow_state_self]; exact h.value,
      h.outbox.trans (congrArg _ (List.append_nil _).symm), ?_⟩
    rw [SysState.grow_state_self]
    show (↑(waiting (net ++ [])) : Multiset In) + ↑((c.state ()).2 ++ [x]) ≤ t.pending
    have heq : (↑(waiting net) : Multiset In) + ↑((c.state ()).2 ++ [x]) =
        (x ::ₘ ↑(waiting net)) + ↑(c.state ()).2 := by
      rw [← Multiset.coe_add, ← Multiset.singleton_add, Multiset.coe_singleton]
      abel
    rw [List.append_nil, heq]
    exact (add_le_add_left (htaken x rfl) _).trans h.pending
  | flush =>
    obtain ⟨t', ht', hvalue, houtbox, hrest⟩ := serves svc (c.state ()).2 t ↑(waiting net)
      ((add_le_add_left hless _).trans h.pending)
    have hemits : Effect.emits (((actor svc).step (c.state ()) .flush).2) =
        (serve svc (c.state ()).1 (c.state ()).2).2 := by
      show Effect.emits (List.map _ _ ++ [_]) = _
      rw [Effect.emits_append, Effect.emits_map_emit (σ := sig In Out) (i := ())]
      exact List.append_nil _
    have hsends : Effect.sends (σ := sig In Out) () (((actor svc).step (c.state ()) .flush).2) =
        [] := by
      show Effect.sends (σ := sig In Out) () (List.map _ _ ++ [_]) = _
      rw [Effect.sends_append, Effect.sends_map_emit (σ := sig In Out) (i := ())]
      rfl
    refine ⟨t', ht', by rw [SysState.grow_state_self, hvalue, h.value]; rfl, ?_, ?_⟩
    · show t'.outbox = ↑(c.outbox ++ Effect.emits ((actor svc).step (c.state ()) .flush).2)
      rw [hemits, houtbox, h.outbox, h.value, Multiset.coe_add]
    · rw [SysState.grow_state_self]
      show (↑(waiting (net ++ Effect.sends () _)) : Multiset In) + ↑([] : List In) ≤ t'.pending
      rw [hsends, List.append_nil]
      simpa using hrest

end Sim

/-- Requests come from outside, and the one timer is `flush`. -/
def Tame {svc : Service (sig In Out) S} (c : SysState (system svc)) : Prop :=
  (∀ e ∈ c.net, e.src = none) ∧ ∀ i m, m ∈ c.timers i → m = Msg.flush

theorem tame_invariant (svc : Service (sig In Out) S) (env : EnvModel (sig In Out)) :
    (system svc).Invariant env Tame := by
  have hsends : ∀ (s : S × List In) (m : Msg In) (dst : Unit) (msg : Msg In),
      Effect.send (σ := sig In Out) (self := ()) dst msg ∉ ((actor svc).step s m).2 := by
    intro s m dst msg
    cases m <;> simp [actor]
  have hnet : (system svc).Monotone fun c => ∀ e ∈ c.net, e.src = none :=
    { blank := fun _ h => nomatch h
      below := fun _ _ h hbelow e he => h e (hbelow.net e he)
      input := fun c x h e he => by
        rcases List.mem_append.mp he with he | he
        · exact h e he
        · rw [List.mem_singleton.mp he]
      step := fun c i msg h _ e he => by
        rcases SysState.mem_grow_net.mp he with he | ⟨_, he⟩
        · exact h e he
        · exact absurd he (hsends _ _ _ _)
      recover := fun c i h e he => by
        rcases SysState.mem_grow_net.mp he with he | ⟨_, he⟩
        · exact h e he
        · simp [actor] at he }
  have htimers := System.Monotone.timers (system svc) (T := fun _ m => m = Msg.flush)
    (fun i s msg delay m h => by cases msg <;> simp_all [actor])
    (fun i s delay m h => by simp_all [actor])
  exact fun c hc => ⟨hnet.invariant env c hc, htimers.invariant env c hc⟩

theorem implements (svc : Service (sig In Out) S) (env : EnvModel (sig In Out))
    (henv : (env.link none ()).duplicating = false) : (system svc).Implements env svc := by
  refine System.Refines.of_steps (tame_invariant svc env) Sim ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · refine ⟨⟨svc.init, 0, 0⟩, rfl, SysState.init_induction (env := env)
      (P := fun c => Sim c ⟨svc.init, 0, 0⟩) ⟨rfl, rfl, ?_⟩
      fun c i h => h.recover.loses (SysState.Loses.startActor c env i)⟩
    simp [SysState.blank, waiting, actor]
  · exact fun c c' t h hl => h.loses hl
  · intro c t x _ h
    refine ⟨{ t with pending := x ::ₘ t.pending }, .single rfl, h.value, h.outbox, ?_⟩
    show (↑(waiting (c.net ++ [⟨none, (), .request x⟩])) : Multiset In) + _ ≤ x ::ₘ t.pending
    have hw : waiting (c.net ++ [(⟨none, (), .request x⟩ : Envelope (sig In Out))]) =
        waiting c.net ++ [x] := by simp [waiting]
    have heq : (↑(waiting c.net ++ [x]) : Multiset In) + ↑(c.state ()).2 =
        x ::ₘ (↑(waiting c.net) + ↑(c.state ()).2) := by
      rw [← Multiset.coe_add, ← Multiset.singleton_add, Multiset.coe_singleton]
      abel
    rw [hw, heq]
    exact Multiset.cons_le_cons x h.pending
  · intro c t out _ h hmem
    have hin : out ∈ t.outbox := h.outbox ▸ Multiset.mem_coe.mpr hmem
    refine ⟨{ t with outbox := t.outbox.erase out }, .single ⟨hin, rfl⟩, h.value, ?_, h.pending⟩
    show t.outbox.erase out = ↑(c.outbox.erase out)
    rw [h.outbox, Multiset.coe_erase]
  · rintro c t ⟨src, ⟨⟩, m⟩ _ h hmem
    exact h.step m List.erase_sublist fun x hm => by
      subst hm
      exact le_of_eq (waiting_erase hmem)
  · rintro c t ⟨src, ⟨⟩, m⟩ ⟨hnet, _⟩ h hmem hdup
    refine h.step (net := c.net) m (List.Sublist.refl _) fun x hm => ?_
    obtain rfl : src = none := hnet _ hmem
    simp [henv] at hdup
  · rintro c t ⟨⟩ m ⟨_, htimers⟩ h hmem
    refine h.step (net := c.net) m (List.Sublist.refl _) fun x hm => ?_
    exact nomatch (htimers () m hmem).symm.trans hm
  · rintro c t ⟨⟩ _ h
    exact ⟨t, .refl, h.recover⟩

/-- The same of the server that remembers every state it has been in, and back. -/
theorem implements_withPast (svc : Service (sig In Out) S) (env : EnvModel (sig In Out))
    (henv : (env.link none ()).duplicating = false) :
    (system svc).withPast.Implements env svc :=
  System.Refines.to_ghost _ (implements svc env henv)

example (svc : Service (sig In Out) S) (env : EnvModel (sig In Out))
    (henv : (env.link none ()).duplicating = false) : (system svc).Implements env svc :=
  System.Refines.of_ghost (.past _) (implements_withPast svc env henv)

end Tests.Batch
