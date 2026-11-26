/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Behaviours.Once
public import Lanes.Semantics.Service
public import Lanes.Semantics.Simulation

/-!
# A service whose clients name their requests

`Service.once svc key` is the spec of `svc` used by clients that name each request by `key`
and may send it more than once, over links that may hand it over more than once. A request takes
effect at most once per key, atomically, between its arrival and its answer, and an answer
given may be handed over again. Its state only grows (`Service.Once.Grows`), which is why a
simulation to it can read messages in flight as a set and a duplicate cannot break it
(`System.Refines.of_handles`).

## Main definitions

- `Service.once`: the transition system of a service whose requests are named by a key.
- `System.ImplementsOnce`: a system refines it.
- `Once.Memo.Agrees`: what the memo of `Once.actor` says of the spec.

## Main statements

- `Server.implementsOnce`: a `Server` behind `Once.actor` implements `once` of its service in
  every environment: links lose, reorder and duplicate, and the server crashes.
-/

@[expose] public section

namespace Lanes

variable {In Out S K : Type}

namespace Service

/-- The state of a service whose clients name their requests by a key. -/
structure Once (In Out S K : Type) where
  /-- The state of the sequential spec. -/
  value : S
  /-- The inputs that have arrived. -/
  arrived : Set In
  /-- The keys of the inputs that have taken effect. -/
  taken : Set K
  /-- The outputs given, each of which may be handed over any number of times. -/
  answered : Set Out

/-- Input `x` takes effect. -/
def Once.take (svc : Service In Out S) (key : In → K) (t : Once In Out S K) (x : In) :
    Once In Out S K :=
  ⟨(svc.step t.value x).1, t.arrived, insert (key x) t.taken,
    t.answered ∪ {out | out ∈ (svc.step t.value x).2}⟩

/--
The transition system of a service whose requests are named by `key`: an input arrives
(visible), an arrived input whose key has not taken effect takes effect (internal), an answer
given is handed over (visible) and stays given.
-/
def once (svc : Service In Out S) (key : In → K) : Spec (Once In Out S K) (Option (Visible In Out))
    where
  init t := t = ⟨svc.init, ∅, ∅, ∅⟩
  Tr t label t' :=
    match label with
    | some (.input x) => t' = { t with arrived := insert x t.arrived }
    | some (.output out) => out ∈ t.answered ∧ t' = t
    | some (.fire t) => t.elim
    | none => ∃ x ∈ t.arrived, key x ∉ t.taken ∧ t' = t.take svc key x

/-- `t'` has arrived, taken and answered everything `t` has. -/
structure Once.Grows (t t' : Once In Out S K) : Prop where
  /-- What has arrived stays arrived. -/
  arrived : t.arrived ⊆ t'.arrived
  /-- What has taken effect stays taken. -/
  taken : t.taken ⊆ t'.taken
  /-- What has been answered stays answered. -/
  answered : t.answered ⊆ t'.answered

namespace Once.Grows

/-- A state grows to itself. -/
theorem refl (t : Once In Out S K) : t.Grows t :=
  ⟨subset_rfl, subset_rfl, subset_rfl⟩

/-- Growing twice is growing. -/
theorem trans {t₁ t₂ t₃ : Once In Out S K} (h₁ : t₁.Grows t₂) (h₂ : t₂.Grows t₃) : t₁.Grows t₃ :=
  ⟨h₁.arrived.trans h₂.arrived, h₁.taken.trans h₂.taken, h₁.answered.trans h₂.answered⟩

end Once.Grows

variable {svc : Service In Out S} {key : In → K}

/-- Every step of `once` grows its state. -/
theorem once_grows {t t' : Once In Out S K} {μ : Option (Visible In Out)} (h : (svc.once key).Tr t μ t') :
    t.Grows t' := by
  match μ, h with
  | some (.input x), h =>
    subst h
    exact ⟨Set.subset_insert _ _, subset_rfl, subset_rfl⟩
  | some (.output _), ⟨_, h⟩ =>
    subst h
    exact .refl _
  | some (.fire t), _ => exact t.elim
  | none, ⟨x, _, _, h⟩ =>
    subst h
    exact ⟨subset_rfl, Set.subset_insert _ _, Set.subset_union_left⟩

/-- Internal steps of `once` grow its state. -/
theorem once_grows_τSTr {t t' : Once In Out S K} (h : (svc.once key).lts.τSTr t t') : t.Grows t' := by
  induction h with
  | refl => exact .refl _
  | tail _ htr ih => exact ih.trans (once_grows (μ := none) htr)

/-- An arrived input whose key has not taken effect may take effect. -/
theorem once_take {t : Once In Out S K} {x : In} (hx : x ∈ t.arrived) (hk : key x ∉ t.taken) :
    (svc.once key).lts.τSTr t (t.take svc key x) :=
  .single ⟨x, hx, hk, rfl⟩

end Service

/-- `sys` implements `svc` for clients that name their requests by `key`. -/
abbrev System.ImplementsOnce {σ : Signature} (sys : System σ) (env : EnvModel σ)
    (svc : Service σ.In σ.Out S) (key : σ.In → K) : Prop :=
  sys.Refines env (svc.once key)

namespace Once.Memo

variable {C E : Type} [DecidableEq C]

/--
What the memo of `Once.actor` says of the spec's keys taken: a key taken has a number at most
its client's last remembered, and a number remembered has been taken, with effects `covered`,
which is what the spec has already accounted for.
-/
structure Agrees (memo : Memo C E) (taken : Set (C × Nat)) (covered : E → Prop) : Prop where
  /-- A key taken is no later than its client's last remembered. -/
  below : ∀ c n, (c, n) ∈ taken → ∃ last effs, memo.find? c = some (last, effs) ∧ n ≤ last
  /-- A number remembered has been taken, and what was done is accounted for. -/
  remembered : ∀ c n effs, memo.find? c = some (n, effs) → (c, n) ∈ taken ∧ ∀ e ∈ effs, covered e

namespace Agrees

variable {memo : Memo C E} {taken : Set (C × Nat)} {covered : E → Prop}

/-- An empty memo agrees with no key taken. -/
theorem empty : Agrees ({} : Memo C E) ∅ covered :=
  ⟨fun _ _ h => h.elim, fun _ _ _ h => by simp at h⟩

/-- Agreement survives accounting for more. -/
theorem mono (h : Agrees memo taken covered) {covered' : E → Prop}
    (hc : ∀ e, covered e → covered' e) : Agrees memo taken covered' :=
  ⟨h.below, fun c n effs hf => ⟨(h.remembered c n effs hf).1,
    fun e he => hc e ((h.remembered c n effs hf).2 e he)⟩⟩

/-- A request the memo has not seen has not taken effect. -/
theorem fresh (h : Agrees memo taken covered) {c : C} {n : Nat} (hs : memo.seen c n = .fresh) :
    (c, n) ∉ taken := by
  intro hmem
  obtain ⟨last, effs, hf, hle⟩ := h.below c n hmem
  simp only [seen, hf] at hs
  split at hs
  · cases hs
  · split at hs
    · cases hs
    · omega

/-- What a request seen again gets is accounted for. -/
theorem again (h : Agrees memo taken covered) {c : C} {n : Nat} {effs : List E}
    (hs : memo.seen c n = .again effs) : ∀ e ∈ effs, covered e := by
  unfold seen at hs
  split at hs
  · next last effs' hf =>
    split at hs
    · cases hs
      exact (h.remembered c last effs hf).2
    · split at hs <;> cases hs
  · cases hs

/-- Acting on a request not seen, and taking its key, keeps agreement. -/
theorem record (h : Agrees memo taken covered) {c : C} {n : Nat} {effs : List E}
    (hs : memo.seen c n = .fresh) (heffs : ∀ e ∈ effs, covered e) :
    Agrees (memo.record c n effs) (insert (c, n) taken) covered := by
  refine ⟨fun c' n' hmem => ?_, fun c' n' effs' hf => ?_⟩
  · by_cases hc : c' = c
    · subst hc
      refine ⟨n, effs, find?_record_self .., ?_⟩
      rcases Set.mem_insert_iff.mp hmem with heq | hmem
      · exact le_of_eq (Prod.mk.inj heq).2
      · obtain ⟨last, effs'', hf, hle⟩ := h.below c' n' hmem
        simp only [seen, hf] at hs
        split at hs
        · cases hs
        · split at hs
          · cases hs
          · omega
    · rw [find?_record_of_ne _ _ _ hc]
      rcases Set.mem_insert_iff.mp hmem with heq | hmem
      · exact absurd (Prod.mk.inj heq).1 hc
      · exact h.below c' n' hmem
  · by_cases hc : c' = c
    · subst hc
      rw [find?_record_self] at hf
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hf)
      exact ⟨Set.mem_insert _ _, heffs⟩
    · rw [find?_record_of_ne _ _ _ hc] at hf
      exact ⟨Set.mem_insert_of_mem _ (h.remembered c' n' effs' hf).1,
        (h.remembered c' n' effs' hf).2⟩

end Agrees

end Once.Memo

namespace Once.Server

open Service

variable [DecidableEq In] [DecidableEq Out] {C : Type} [DecidableEq C]
  {svc : Service In Out S} {key : In → C × Nat}

/-- What an effect of the server leaves is accounted for in `t`, and it arms no timer. -/
def Covered (t : Service.Once In Out S (C × Nat)) :
    Effect (Server.sig In Out) () → Prop
  | .send _ msg => (msg : In) ∈ t.arrived
  | .emit out => out ∈ t.answered
  | .after .. => False
  | _ => True

omit [DecidableEq C] in
/-- What is covered stays covered as the spec grows. -/
theorem Covered.mono {t t' : Service.Once In Out S (C × Nat)}
    {eff : Effect (Server.sig In Out) ()} (h : Covered t eff) (hg : t.Grows t') :
    Covered t' eff := by
  cases eff with
  | send _ msg => exact hg.arrived h
  | emit out => exact hg.answered h
  | after => exact h.elim
  | cancel => trivial
  | stop => trivial

/-- The server's state is the spec's value, every request in flight has arrived, every output
waiting has been given, no timer is armed, and the memo agrees with the keys taken. -/
structure Sim (c : SysState (server svc key)) (t : Service.Once In Out S (C × Nat)) :
    Prop where
  /-- The server's state is the spec's value. -/
  value : t.value = (c.state ()).1
  /-- Every request in flight has arrived. -/
  net : ∀ e ∈ c.net, (e.msg : In) ∈ t.arrived
  /-- Every output waiting has been given. -/
  outbox : ∀ out ∈ c.outbox, out ∈ t.answered
  /-- No timer is armed. -/
  timers : ∀ m, m ∉ c.timers ()
  /-- The memo agrees with the keys taken. -/
  memo : (c.state ()).2.Agrees t.taken (Covered t)

/-- The server moves to `r.1` with effects `r.2`, all accounted for in `t'`, with what is left
of the network. -/
theorem Sim.grow {c : SysState (server svc key)} {t t' : Service.Once In Out S (C × Nat)}
    (h : Sim c t) (hg : t.Grows t') {net : List (Envelope (Server.sig In Out))}
    (hnet : net.Sublist c.net) {r : (server svc key).State () × List (Effect (Server.sig In Out) ())}
    (hvalue : t'.value = r.1.1) (hmemo : r.1.2.Agrees t'.taken (Covered t'))
    (heffs : ∀ eff ∈ r.2, Covered t' eff) : Sim (({ c with net }).grow () r) t' := by
  refine ⟨by simpa using hvalue, fun e he => ?_, fun o ho => ?_, fun m hm => ?_,
    by simpa using hmemo⟩
  · rcases SysState.mem_grow_net.mp he with he | ⟨_, hsend⟩
    · exact hg.arrived (h.net e (hnet.subset he))
    · exact heffs _ hsend
  · simp only [SysState.grow, List.mem_append] at ho
    rcases ho with ho | ho
    · exact hg.answered (h.outbox o ho)
    · exact heffs _ (Effect.mem_emits.mp ho)
  · rcases SysState.mem_grow_timers.mp hm with hm | ⟨_, delay, hafter⟩
    · exact h.timers m hm
    · simpa [Covered] using heffs _ hafter

omit [DecidableEq C] in
/-- Every effect of the service's step on `x` is an output it gives. -/
theorem covered_step {t : Service.Once In Out S (C × Nat)} (s : S) (x : In)
    (h : ∀ out ∈ (svc.step s x).2, out ∈ t.answered) :
    ∀ eff ∈ ((Server.actor svc).step s x).2, Covered t eff := by
  intro eff heff
  obtain ⟨out, hout, rfl⟩ := List.mem_map.mp heff
  exact h out hout

end Once.Server

open Once.Server in
/--
A `Server` that acts once on each request its key names implements `once` of its service in
every environment: links lose, reorder and hand over twice every message, and the server
crashes. `Server.implements` needs an environment with no fault at all.
-/
theorem Once.server_implements {In Out C : Type} [DecidableEq In] [DecidableEq Out]
    [DecidableEq C] (svc : Service In Out S) (key : In → C × Nat)
    (env : EnvModel (Server.sig In Out)) : (server svc key).ImplementsOnce env svc key := by
  refine System.Refines.of_handles (inv := fun _ => True) (fun _ _ => trivial) Sim
    ⟨⟨svc.init, ∅, ∅, ∅⟩, rfl, rfl, by simp [SysState.init, SysState.blank],
      by simp [SysState.init, SysState.blank], by simp [SysState.init, SysState.blank],
      Memo.Agrees.empty⟩ (fun c c' t h hl => ?_) ?_ ?_ ?_ ?_
  · exact ⟨by rw [hl.state]; exact h.value, fun e he => h.net e (hl.net.subset he),
      fun o ho => h.outbox o (hl.outbox ▸ ho), fun m hm => h.timers m (hl.timers () m hm),
      by rw [hl.state]; exact h.memo⟩
  · intro c t x _ h
    have hg : t.Grows { t with arrived := insert x t.arrived } :=
      ⟨Set.subset_insert _ _, subset_rfl, subset_rfl⟩
    refine ⟨_, .single rfl, h.value, fun e he => ?_, h.outbox, h.timers,
      h.memo.mono fun _ he => he.mono hg⟩
    rcases List.mem_append.mp he with he | he
    · exact hg.arrived (h.net e he)
    · obtain rfl := List.mem_singleton.mp he
      exact Set.mem_insert _ _
  · intro c t out _ h hmem
    exact ⟨t, .single ⟨h.outbox out hmem, rfl⟩, h.value, h.net,
      fun o ho => h.outbox o (List.mem_of_mem_erase ho), h.timers, h.memo⟩
  · rintro c t net ⟨⟩ x _ h hnet hpend
    obtain ⟨src, hmem⟩ := hpend.resolve_right (h.timers x)
    have harrived : x ∈ t.arrived := h.net _ hmem
    have hval := h.value
    have hmemo := h.memo
    rw [← Prod.mk.eta (p := c.state ())]
    rw [← Prod.mk.eta (p := c.state ())] at hval hmemo
    generalize (c.state ()).1 = s at hval hmemo ⊢
    generalize (c.state ()).2 = memo at hval hmemo ⊢
    have hkey : (fun x => some (key x)) x = some ((key x).1, (key x).2) := rfl
    cases hs : memo.seen (key x).1 (key x).2 with
    | fresh =>
      have hstep := Service.once_take (svc := svc) (key := key) harrived (hmemo.fresh hs)
      have hg := Service.once_grows_τSTr hstep
      have heffs := covered_step (t := t.take svc key x) s x fun o ho => Or.inr (by rw [hval]; exact ho)
      refine ⟨_, hstep, ?_⟩
      rw [show (server svc key).actor () = actor (Server.actor svc) (fun x => some (key x)) from rfl,
        Once.step_of_fresh (Server.actor svc) (fun x => some (key x)) s memo x hkey hs]
      exact h.grow hg hnet (by simp [Service.Once.take, hval, Server.actor])
        ((hmemo.mono fun _ he => he.mono hg).record hs heffs) heffs
    | again effs =>
      refine ⟨t, .refl, ?_⟩
      rw [show (server svc key).actor () = actor (Server.actor svc) (fun x => some (key x)) from rfl,
        Once.step_of_again (Server.actor svc) (fun x => some (key x)) s memo x hkey hs]
      exact h.grow (.refl _) hnet hval hmemo (hmemo.again hs)
    | stale =>
      refine ⟨t, .refl, ?_⟩
      rw [show (server svc key).actor () = actor (Server.actor svc) (fun x => some (key x)) from rfl,
        Once.step_of_stale (Server.actor svc) (fun x => some (key x)) s memo x hkey hs]
      exact h.grow (.refl _) hnet hval hmemo (by simp)
  · rintro c t ⟨⟩ _ h
    refine ⟨t, .refl, ?_⟩
    exact h.grow (net := c.net) (.refl _) (.refl _) (by simpa [Once.recover_eq, Server.actor] using h.value)
      (by simpa [Once.recover_eq, Server.actor] using h.memo) (by simp [Once.recover_eq, Server.actor])

end Lanes
