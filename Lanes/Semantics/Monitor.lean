/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Check.Monitor
public import Lanes.Semantics.Service

/-!
# The spec monitor is exact

`Lanes.Check.Monitor` is the model checker's refinement check. This file proves that its
candidates are exactly the states `Service.spec` can be in after the observed inputs,
outputs and deadlines passing, so the monitor runs out of candidates exactly when the spec does not allow what was
observed.

The checker works on lists and `Service.spec` on multisets; `Service.State.toAbs` relates them.
Soundness holds for any `BEq` on the spec state, because candidates are only ever dropped as
duplicates. Completeness needs `LawfulBEq`: a duplicate must really be the same state.

## Main definitions

- `Service.State.toAbs`: the mathematical state a checker-side state stands for.
- `Check.Monitor.after`: the monitor after a sequence of visible events.

## Main statements

- `Check.Monitor.sound`: every candidate is a state the spec can be in.
- `Check.Monitor.complete`: every state the spec can be in is a candidate.
- `Check.Monitor.ok_iff`: the monitor accepts exactly the observations the spec allows.
-/

@[expose] public section

namespace Lanes

open Cslib

variable {In Out S T : Type} [DecidableEq In] [DecidableEq Out]

/-- The mathematical state a checker-side state stands for. -/
def Service.State.toAbs (st : Service.State In Out S) : Service.Abs In Out S :=
  ⟨st.value, st.pending, st.outbox⟩

namespace Service

omit [DecidableEq In] [DecidableEq Out] in
/-- An arriving input is the spec's input step. -/
theorem State.toAbs_call (st : State In Out S) (x : In) :
    (st.call x).toAbs = { st.toAbs with pending := x ::ₘ st.toAbs.pending } := by
  have h : ((st.pending ++ [x] : List In) : Multiset In) = x ::ₘ ↑st.pending :=
    Multiset.coe_eq_coe.mpr (List.perm_append_singleton x st.pending)
  simp only [State.toAbs, State.call, h]

omit [DecidableEq Out] in
/-- An input taking effect is the spec's internal step. -/
theorem toAbs_apply (svc : Service In Out S T) (st : State In Out S) (x : In) :
    (svc.apply st x).toAbs = ⟨(svc.step st.value x).1, st.toAbs.pending.erase x,
      st.toAbs.outbox + (svc.step st.value x).2⟩ := by
  simp [State.toAbs, apply]

omit [DecidableEq In] in
/-- A delivered output is the spec's output step. -/
theorem State.ret_eq_some {st st' : State In Out S} {out : Out} (h : st.ret out = some st') :
    out ∈ st.toAbs.outbox ∧
      st'.toAbs = { st.toAbs with outbox := st.toAbs.outbox.erase out } := by
  unfold State.ret at h
  split at h
  · rename_i hmem
    obtain rfl := Option.some.inj h
    exact ⟨by simpa [State.toAbs] using hmem, by simp [State.toAbs]⟩
  · cases h

omit [DecidableEq In] in
/-- An output that is waiting can be delivered. -/
theorem State.ret_of_mem {st : State In Out S} {out : Out} (h : out ∈ st.toAbs.outbox) :
    ∃ st', st.ret out = some st' := by
  have hmem : out ∈ st.outbox := by simpa [State.toAbs] using h
  exact ⟨{ st with outbox := st.outbox.erase out }, by simp [State.ret, hmem]⟩

/-- A deadline passing in a checker-side state is the spec's step for it. -/
theorem State.fire_eq_some {svc : Service In Out S T} {st st' : State In Out S} {t : T}
    (h : st.fire svc t = some st') : svc.spec.lts.Tr st.toAbs (some (.fire t)) st'.toAbs := by
  unfold State.fire at h
  split at h
  · rename_i harmed
    obtain rfl := Option.some.inj h
    exact ⟨harmed, by simp [State.toAbs]⟩
  · cases h

/-- Every step of the spec for a deadline passing is one in a checker-side state. -/
theorem State.exists_fire {svc : Service In Out S T} {st : State In Out S} {t : T}
    {a : Abs In Out S} (h : svc.spec.lts.Tr st.toAbs (some (.fire t)) a) :
    ∃ st', st.fire svc t = some st' ∧ st'.toAbs = a := by
  obtain ⟨harmed, rfl⟩ := h
  refine ⟨⟨(svc.fire st.value t).1, st.pending, st.outbox ++ (svc.fire st.value t).2⟩, ?_,
    by simp [State.toAbs]⟩
  simp only [State.fire, show svc.armed st.value t = true from harmed, ite_true]

/-- States the checker treats as the same stand for the same mathematical state. -/
theorem State.toAbs_eq_of_equiv [BEq S] [LawfulBEq S] {a b : State In Out S}
    (h : a.equiv b = true) : a.toAbs = b.toAbs := by
  simp only [State.equiv, Bool.and_eq_true, beq_iff_eq, List.isPerm_iff] at h
  obtain ⟨⟨hvalue, hpending⟩, houtbox⟩ := h
  simp [State.toAbs, hvalue, Multiset.coe_eq_coe.mpr hpending, Multiset.coe_eq_coe.mpr houtbox]

/-- A pending input taking effect is an internal step of the spec. -/
theorem spec_tr_apply (svc : Service In Out S T) (st : State In Out S) {x : In} (hx : x ∈ st.pending) :
    svc.spec.lts.Tr st.toAbs none (svc.apply st x).toAbs :=
  ⟨x, Multiset.mem_coe.mpr hx, toAbs_apply svc st x⟩

/-- Every internal step of the spec is a pending input taking effect. -/
theorem exists_apply_of_spec_tr {svc : Service In Out S T} {st : State In Out S} {a : Abs In Out S}
    (h : svc.spec.lts.Tr st.toAbs none a) : ∃ x ∈ st.pending, (svc.apply st x).toAbs = a := by
  obtain ⟨x, hx, rfl⟩ := h
  exact ⟨x, Multiset.mem_coe.mp hx, toAbs_apply svc st x⟩

/-- With nothing pending the spec has no internal step. -/
theorem not_spec_tr_of_pending_eq_zero {svc : Service In Out S T} {a b : Abs In Out S}
    (hpending : a.pending = 0) : ¬ svc.spec.lts.Tr a none b := by
  rintro ⟨x, hx, -⟩
  simp [hpending] at hx

/-- With nothing pending the spec stays where it is until the next visible step. -/
theorem eq_of_τSTr_of_pending_eq_zero {svc : Service In Out S T} {a b : Abs In Out S}
    (hpending : a.pending = 0) (h : svc.spec.lts.τSTr a b) : b = a := by
  cases h using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head htr _ => exact absurd htr (not_spec_tr_of_pending_eq_zero hpending)

/--
Delivering an output commutes with inputs taking effect: internal steps taken after a delivery
can be taken before it. This is why the monitor does not close its candidates again after an
output.
-/
theorem τSTr_erase_outbox {svc : Service In Out S T} {a b : Abs In Out S} {out : Out}
    (hmem : out ∈ a.outbox)
    (h : svc.spec.lts.τSTr { a with outbox := a.outbox.erase out } b) :
    ∃ a', svc.spec.lts.τSTr a a' ∧ out ∈ a'.outbox ∧
      b = { a' with outbox := a'.outbox.erase out } := by
  induction h with
  | refl => exact ⟨a, .refl, hmem, rfl⟩
  | tail _ htr ih =>
    obtain ⟨a', ha', hmem', rfl⟩ := ih
    obtain ⟨x, hx, rfl⟩ := htr
    refine ⟨⟨(svc.step a'.value x).1, a'.pending.erase x,
      a'.outbox + (svc.step a'.value x).2⟩, ha'.tail ⟨x, hx, rfl⟩,
      Multiset.mem_add.mpr (.inl hmem'), ?_⟩
    simp [Multiset.erase_add_left_pos _ hmem']

end Service

/-- A saturated run ending in a visible label is a saturated run, then that step, then internal
steps. -/
theorem sMTr_concat_some {State α : Type*} {lts : LTS State (Option α)} {s s' : State}
    {μs : List (Option α)} {e : α} :
    lts.SMTr s (μs ++ [some e]) s' ↔
      ∃ s₁ s₂, lts.SMTr s μs s₁ ∧ lts.Tr s₁ (some e) s₂ ∧ lts.τSTr s₂ s' := by
  constructor
  · intro h
    induction μs generalizing s with
    | nil =>
      obtain _ | ⟨hstr, hrest⟩ := h
      rw [← LTS.sMTr_τSTr_iff] at hrest
      generalize hμ : some e = μ at hstr
      cases hstr with
      | refl => cases hμ
      | tr h₁ htr h₂ =>
        subst hμ
        exact ⟨_, _, LTS.sMTr_τSTr_iff.mp h₁, htr, h₂.trans hrest⟩
    | cons μ μs ih =>
      obtain _ | ⟨hstr, hrest⟩ := h
      obtain ⟨s₁, s₂, hrun, htr, hτ⟩ := ih hrest
      exact ⟨s₁, s₂, .stepL hstr hrun, htr, hτ⟩
  · rintro ⟨s₁, s₂, hrun, htr, hτ⟩
    exact hrun.comp (.stepL (.tr .refl htr hτ) (LTS.SMTr.refl lts s'))

namespace Check.Monitor

open Service

omit [DecidableEq Out] in
/-- The members of `expand`. -/
theorem mem_expand {svc : Service In Out S T} {frontier : List (State In Out S)} {t : State In Out S} :
    t ∈ expand svc frontier ↔ ∃ f ∈ frontier, ∃ x ∈ f.pending, svc.apply f x = t := by
  simp [expand]

omit [DecidableEq In] [DecidableEq Out] in
/-- The running maximum in `rounds` never decreases. -/
theorem le_foldl_max_pending (states : List (State In Out S)) (n : Nat) :
    n ≤ states.foldl (fun n s => max n s.pending.length) n := by
  induction states generalizing n with
  | nil => exact Nat.le_refl n
  | cons s states ih => exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

omit [DecidableEq In] [DecidableEq Out] in
/-- No state has more inputs pending than `close` runs rounds. -/
theorem length_pending_le_rounds {states : List (State In Out S)} {s : State In Out S}
    (h : s ∈ states) : s.pending.length ≤ rounds states := by
  unfold rounds
  generalize 0 = n
  induction states generalizing n with
  | nil => cases h
  | cons s' states ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_trans (Nat.le_max_right _ _) (le_foldl_max_pending _ _)
    · exact ih h _

variable [BEq S]

/-- Observe one visible event. -/
def observe (svc : Service In Out S T) (m : Monitor In Out S) : Visible In Out T → Monitor In Out S
  | .input x => m.input svc x
  | .output out => m.output out
  | .fire t => m.fire svc t

/-- The monitor after a sequence of visible events. -/
def after (svc : Service In Out S T) (obs : List (Visible In Out T)) : Monitor In Out S :=
  obs.foldl (observe svc) (start svc)

/-- `insertAll` never drops a known state. -/
theorem mem_insertAll_of_mem {known new : List (State In Out S)} {t : State In Out S} (h : t ∈ known) :
    t ∈ insertAll known new := by
  induction new generalizing known with
  | nil => exact h
  | cons s new ih =>
    refine ih (known := if known.any (s.equiv ·) then known else known ++ [s]) ?_
    split
    · exact h
    · exact List.mem_append_left _ h

/-- `insertAll` invents nothing. -/
theorem mem_or_mem_of_mem_insertAll {known new : List (State In Out S)} {t : State In Out S}
    (h : t ∈ insertAll known new) : t ∈ known ∨ t ∈ new := by
  induction new generalizing known with
  | nil => exact .inl h
  | cons s new ih =>
    rcases ih (known := if known.any (s.equiv ·) then known else known ++ [s]) h with h | h
    · split at h
      · exact .inl h
      · rcases List.mem_append.mp h with h | h
        · exact .inl h
        · exact .inr (by simp_all)
    · exact .inr (List.mem_cons_of_mem _ h)

/-- `insertAll` keeps every new state, up to the order of its lists. -/
theorem exists_mem_insertAll_toAbs_eq [LawfulBEq S] {known new : List (State In Out S)}
    {s : State In Out S} (h : s ∈ new) : ∃ t ∈ insertAll known new, t.toAbs = s.toAbs := by
  induction new generalizing known with
  | nil => cases h
  | cons s' new ih =>
    rcases List.mem_cons.mp h with rfl | h
    · by_cases hany : known.any (s.equiv ·) = true
      · obtain ⟨t, ht, hequiv⟩ := List.any_eq_true.mp hany
        exact ⟨t, mem_insertAll_of_mem ht, (State.toAbs_eq_of_equiv hequiv).symm⟩
      · refine ⟨s, ?_, rfl⟩
        refine mem_insertAll_of_mem
          (known := if known.any (s.equiv ·) then known else known ++ [s]) ?_
        simp [hany]
    · exact ih h

/-- A fresh state is one of the states offered. -/
theorem mem_of_mem_freshFrom {known acc next : List (State In Out S)} {t : State In Out S}
    (h : t ∈ freshFrom known acc next) : t ∈ acc ∨ t ∈ next := by
  induction next generalizing acc with
  | nil => exact .inl h
  | cons s next ih =>
    rcases ih (acc := if (known ++ acc).any (s.equiv ·) then acc else acc ++ [s]) h with h | h
    · split at h
      · exact .inl h
      · rcases List.mem_append.mp h with h | h
        · exact .inl h
        · exact .inr (by simp_all)
    · exact .inr (List.mem_cons_of_mem _ h)

/-- `close` is `closeStep` repeated. -/
theorem close_eq (svc : Service In Out S T) (states : List (State In Out S)) :
    close svc states = ((List.range (rounds states)).foldl (fun acc _ => closeStep svc acc)
      (insertAll [] states, insertAll [] states)).1 :=
  rfl

/-- The states found in a round were offered by `expand`. -/
theorem mem_expand_of_mem_closeStep {svc : Service In Out S T}
    {acc : List (State In Out S) × List (State In Out S)} {s : State In Out S}
    (h : s ∈ (closeStep svc acc).2) : s ∈ expand svc acc.2 := by
  rcases mem_of_mem_freshFrom h with h | h
  · cases h
  · exact h

/-- Rounds only add known states. -/
theorem mem_foldl_closeStep {svc : Service In Out S T} (l : List Nat)
    {acc : List (State In Out S) × List (State In Out S)} {s : State In Out S} (h : s ∈ acc.1) :
    s ∈ (l.foldl (fun acc _ => closeStep svc acc) acc).1 := by
  induction l generalizing acc with
  | nil => exact h
  | cons _ l ih => exact ih (acc := closeStep svc acc) (List.mem_append_left _ h)

/-- Every state `close` returns is reached from one it was given by internal steps of the
spec. -/
theorem close_sound (svc : Service In Out S T) {states : List (State In Out S)} {st : State In Out S}
    (h : st ∈ close svc states) :
    ∃ seed ∈ states, svc.spec.lts.τSTr seed.toAbs st.toAbs := by
  rw [close_eq] at h
  suffices hfold : ∀ (l : List Nat) (acc : List (State In Out S) × List (State In Out S)),
      (∀ s ∈ acc.1, ∃ seed ∈ states, svc.spec.lts.τSTr seed.toAbs s.toAbs) →
      (∀ s ∈ acc.2, ∃ seed ∈ states, svc.spec.lts.τSTr seed.toAbs s.toAbs) →
      ∀ s ∈ (l.foldl (fun acc _ => closeStep svc acc) acc).1,
        ∃ seed ∈ states, svc.spec.lts.τSTr seed.toAbs s.toAbs by
    have hseed : ∀ s ∈ insertAll [] states,
        ∃ seed ∈ states, svc.spec.lts.τSTr seed.toAbs s.toAbs := by
      intro s hs
      rcases mem_or_mem_of_mem_insertAll hs with hs | hs
      · cases hs
      · exact ⟨s, hs, .refl⟩
    exact hfold _ _ hseed hseed st h
  intro l
  induction l with
  | nil => exact fun acc h₁ _ => h₁
  | cons _ l ih =>
    intro acc h₁ h₂
    have hfresh : ∀ s ∈ (closeStep svc acc).2,
        ∃ seed ∈ states, svc.spec.lts.τSTr seed.toAbs s.toAbs := by
      intro s hs
      obtain ⟨f, hf, x, hx, rfl⟩ := mem_expand.mp (mem_expand_of_mem_closeStep hs)
      obtain ⟨seed, hseed, hτ⟩ := h₂ f hf
      exact ⟨seed, hseed, hτ.tail (spec_tr_apply svc f hx)⟩
    refine ih (closeStep svc acc) ?_ hfresh
    intro s hs
    rcases List.mem_append.mp hs with hs | hs
    · exact h₁ s hs
    · exact hfresh s hs

/--
What `close` has established with `n` rounds to go. At `n = 0` the frontier has nothing pending,
so the known states are closed under the spec's internal steps.
-/
structure Closing (svc : Service In Out S T) (n : Nat)
    (acc : List (State In Out S) × List (State In Out S)) : Prop where
  /-- A frontier state has at most `n` inputs pending. -/
  short : ∀ f ∈ acc.2, f.pending.length ≤ n
  /-- A known state is on the frontier or has every successor known. -/
  closed : ∀ s ∈ acc.1, (∃ f ∈ acc.2, f.toAbs = s.toAbs) ∨
    ∀ a, svc.spec.lts.Tr s.toAbs none a → ∃ t ∈ acc.1, t.toAbs = a

/-- A round of `close` uses up one round of the budget. -/
theorem Closing.step [LawfulBEq S] {svc : Service In Out S T} {n : Nat}
    {acc : List (State In Out S) × List (State In Out S)} (h : Closing svc (n + 1) acc) :
    Closing svc n (closeStep svc acc) where
  short := by
    intro f hf
    obtain ⟨g, hg, x, hx, rfl⟩ := mem_expand.mp (mem_expand_of_mem_closeStep hf)
    have hshort := h.short g hg
    simp only [Service.apply, List.length_erase_of_mem hx]
    omega
  closed := by
    intro s hs
    rcases List.mem_append.mp hs with hs | hs
    · refine .inr fun a ha => ?_
      rcases h.closed s hs with ⟨f, hf, hfs⟩ | hknown
      · rw [← hfs] at ha
        obtain ⟨x, hx, rfl⟩ := exists_apply_of_spec_tr ha
        have hmem : svc.apply f x ∈ expand svc acc.2 := mem_expand.mpr ⟨f, hf, x, hx, rfl⟩
        obtain ⟨t, ht, hta⟩ := exists_mem_insertAll_toAbs_eq (known := acc.1 ++ []) hmem
        rw [← append_freshFrom] at ht
        exact ⟨t, ht, hta⟩
      · obtain ⟨t, ht, hta⟩ := hknown a ha
        exact ⟨t, List.mem_append_left _ ht, hta⟩
    · exact .inl ⟨s, hs, rfl⟩

/-- Enough rounds use up the budget. -/
theorem Closing.foldl [LawfulBEq S] {svc : Service In Out S T} :
    ∀ (l : List Nat) {acc : List (State In Out S) × List (State In Out S)}, Closing svc l.length acc →
      Closing svc 0 (l.foldl (fun acc _ => closeStep svc acc) acc)
  | [], _, h => h
  | _ :: l, _, h => Closing.foldl l h.step

omit [BEq S] in
/-- With no rounds to go the known states are closed under the spec's internal steps. -/
theorem Closing.exists_of_τSTr {svc : Service In Out S T}
    {acc : List (State In Out S) × List (State In Out S)} (h : Closing svc 0 acc) {s : State In Out S}
    (hs : s ∈ acc.1) {a : Abs In Out S} (hτ : svc.spec.lts.τSTr s.toAbs a) :
    ∃ t ∈ acc.1, t.toAbs = a := by
  induction hτ with
  | refl => exact ⟨s, hs, rfl⟩
  | tail _ htr ih =>
    obtain ⟨t, ht, rfl⟩ := ih
    rcases h.closed t ht with ⟨f, hf, hft⟩ | hknown
    · have hnil : f.pending = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp (h.short f hf))
      refine absurd htr (not_spec_tr_of_pending_eq_zero ?_)
      rw [← hft]
      simp [State.toAbs, hnil]
    · exact hknown _ htr

/-- Every state reached from one `close` was given by internal steps of the spec is returned. -/
theorem close_complete [LawfulBEq S] (svc : Service In Out S T) {states : List (State In Out S)}
    {seed : State In Out S} (hseed : seed ∈ states) {a : Abs In Out S}
    (hτ : svc.spec.lts.τSTr seed.toAbs a) : ∃ st ∈ close svc states, st.toAbs = a := by
  rw [close_eq]
  have hinit : Closing svc (List.range (rounds states)).length
      (insertAll [] states, insertAll [] states) :=
    { short := fun f hf => by
        rcases mem_or_mem_of_mem_insertAll hf with hf | hf
        · cases hf
        · simpa using length_pending_le_rounds hf
      closed := fun s hs => .inl ⟨s, hs, rfl⟩ }
  obtain ⟨t, ht, hts⟩ := exists_mem_insertAll_toAbs_eq (known := []) hseed
  rw [← hts] at hτ
  exact (Closing.foldl _ hinit).exists_of_τSTr (mem_foldl_closeStep _ ht) hτ

/-- Observing one more event. -/
theorem after_concat (svc : Service In Out S T) (obs : List (Visible In Out T)) (e : Visible In Out T) :
    after svc (obs ++ [e]) = observe svc (after svc obs) e := by
  simp [after]

/-- Every candidate is a state the spec can be in after these observations. -/
theorem sound (svc : Service In Out S T) {obs : List (Visible In Out T)} {st : State In Out S}
    (h : st ∈ (after svc obs).candidates) :
    svc.spec.lts.SMTr ⟨svc.init, 0, 0⟩ (obs.map some) st.toAbs := by
  induction obs using List.reverseRecOn generalizing st with
  | nil =>
    obtain rfl : st = svc.start := by simpa [after, start] using h
    exact LTS.SMTr.refl _ _
  | append_singleton obs e ih =>
    rw [after_concat] at h
    rw [List.map_append, List.map_singleton, sMTr_concat_some]
    cases e with
    | input x =>
      obtain ⟨seed, hseed, hτ⟩ := close_sound svc h
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hseed
      exact ⟨s.toAbs, (s.call x).toAbs, ih hs, State.toAbs_call s x, hτ⟩
    | output out =>
      rcases mem_or_mem_of_mem_insertAll h with h | h
      · cases h
      · obtain ⟨s, hs, hret⟩ := List.mem_filterMap.mp h
        exact ⟨s.toAbs, st.toAbs, ih hs, State.ret_eq_some hret, .refl⟩
    | fire t =>
      obtain ⟨seed, hseed, hτ⟩ := close_sound svc h
      obtain ⟨s, hs, hfire⟩ := List.mem_filterMap.mp hseed
      exact ⟨s.toAbs, seed.toAbs, ih hs, State.fire_eq_some hfire, hτ⟩

/-- Every state the spec can be in after these observations is a candidate. -/
theorem complete [LawfulBEq S] (svc : Service In Out S T) {obs : List (Visible In Out T)} {a : Abs In Out S}
    (h : svc.spec.lts.SMTr ⟨svc.init, 0, 0⟩ (obs.map some) a) :
    ∃ st ∈ (after svc obs).candidates, st.toAbs = a := by
  induction obs using List.reverseRecOn generalizing a with
  | nil =>
    obtain rfl := eq_of_τSTr_of_pending_eq_zero rfl (LTS.sMTr_τSTr_iff.mpr h)
    exact ⟨svc.start, by simp [after, start], rfl⟩
  | append_singleton obs e ih =>
    rw [List.map_append, List.map_singleton, sMTr_concat_some] at h
    obtain ⟨a₁, a₂, hrun, htr, hτ⟩ := h
    rw [after_concat]
    cases e with
    | input x =>
      obtain ⟨s, hs, rfl⟩ := ih hrun
      obtain rfl : a₂ = (s.call x).toAbs := htr.trans (State.toAbs_call s x).symm
      exact close_complete svc (List.mem_map_of_mem hs) hτ
    | output out =>
      obtain ⟨hmem, rfl⟩ := htr
      obtain ⟨a', ha', hmem', rfl⟩ := τSTr_erase_outbox hmem hτ
      obtain ⟨s, hs, rfl⟩ := ih (by simpa using hrun.comp (LTS.sMTr_τSTr_iff.mp ha'))
      obtain ⟨s', hret⟩ := State.ret_of_mem hmem'
      have hmem : s' ∈ (after svc obs).candidates.filterMap (·.ret out) :=
        List.mem_filterMap.mpr ⟨s, hs, hret⟩
      obtain ⟨t, ht, hts⟩ := exists_mem_insertAll_toAbs_eq (known := []) hmem
      exact ⟨t, ht, hts.trans (State.ret_eq_some hret).2⟩
    | fire t =>
      obtain ⟨s, hs, rfl⟩ := ih hrun
      obtain ⟨s', hfire, rfl⟩ := State.exists_fire htr
      exact close_complete svc (List.mem_filterMap.mpr ⟨s, hs, hfire⟩) hτ

/-- The monitor accepts exactly the observation sequences the spec allows. -/
theorem ok_iff [LawfulBEq S] (svc : Service In Out S T) (obs : List (Visible In Out T)) :
    (after svc obs).ok = true ↔
      ∃ a, svc.spec.lts.SMTr ⟨svc.init, 0, 0⟩ (obs.map some) a := by
  constructor
  · intro h
    cases hc : (after svc obs).candidates with
    | nil => simp [ok, hc] at h
    | cons st _ => exact ⟨st.toAbs, sound svc (by simp [hc])⟩
  · rintro ⟨a, ha⟩
    obtain ⟨st, hst, -⟩ := complete svc ha
    cases hc : (after svc obs).candidates with
    | nil => simp [hc] at hst
    | cons _ _ => simp [ok, hc]

end Check.Monitor

end Lanes
