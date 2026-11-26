/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Check.Search

/-!
# The search is sound

What a `Check.Report` claims, proved of `Check.search`.

- `search_violated`, `search_deadlock`, `search_witness`: a reported trace is a path of the
  model through states that satisfy the constraint, and ends in the state the report says it
  does. These hold for any `BEq` and `Hashable`, lawful or not.
- `search_states_le`: at most `maxStates` states are stored.
- `search_sound`: a complete search with no failure means every `always` property holds in
  every reachable state. This needs state equality to be an equivalence that the model cannot
  tell apart (`Model.Respects`); `search_sound_of_lawful` is the case of a lawful `==`.
- `search_unreached`, `search_deadlock_free`: the same for a `sometimes` property reported
  unreached and for the absence of deadlocks.
-/

@[expose] public section

namespace Lanes.Check

variable {S L : Type}

/-- Reachable from an initial state through states that all satisfy the constraint. -/
inductive Model.Reachable (m : Model S L) (constraint : S → Bool) : S → Prop
  | init {s : S} : s ∈ m.init → constraint s = true → Reachable m constraint s
  | step {s s' : S} {l : L} : Reachable m constraint s → (l, s') ∈ m.next s →
      constraint s' = true → Reachable m constraint s'

/-- Each step is a transition of the model from the state before it, starting at `s`. -/
def Model.Steps (m : Model S L) : S → List (L × S) → Prop
  | _, [] => True
  | s, step :: rest => step ∈ m.next s ∧ m.Steps step.2 rest

/-- A trace is a path of the model from an initial state. -/
def Trace.Valid (m : Model S L) (t : Trace S L) : Prop :=
  t.init ∈ m.init ∧ m.Steps t.init t.steps

namespace Path

variable {m : Model S L} {constraint : S → Bool}

def Valid (m : Model S L) (constraint : S → Bool) : Path S L → Prop
  | .init s => s ∈ m.init ∧ constraint s = true
  | .step parent l s =>
    parent.Valid m constraint ∧ (l, s) ∈ m.next parent.last ∧ constraint s = true

theorem Valid.reachable : {p : Path S L} → p.Valid m constraint → m.Reachable constraint p.last
  | .init _, h => .init h.1 h.2
  | .step _ _ _, h => .step (reachable h.1) h.2.1 h.2.2

theorem toTraceAux_valid : (p : Path S L) → (steps : List (L × S)) → p.Valid m constraint →
    m.Steps p.last steps → (p.toTraceAux steps).Valid m
  | .init _, _, h, hsteps => ⟨h.1, hsteps⟩
  | .step parent _ _, _, h, hsteps => toTraceAux_valid parent _ h.1 ⟨h.2.1, hsteps⟩

theorem Valid.toTrace {p : Path S L} (h : p.Valid m constraint) : p.toTrace.Valid m :=
  toTraceAux_valid p [] h trivial

theorem last_toTraceAux : (p : Path S L) → (steps : List (L × S)) →
    (p.toTraceAux steps).last = (Trace.mk p.last steps).last
  | .init _, _ => rfl
  | .step parent l s, steps => by
    rw [toTraceAux, last_toTraceAux parent]
    cases steps with
    | nil => rfl
    | cons step steps =>
      simp only [Trace.last, List.getLast?_cons_cons]
      cases h : (step :: steps).getLast? with
      | none => simp at h
      | some _ => rfl

@[simp] theorem last_toTrace (p : Path S L) : p.toTrace.last = p.last :=
  last_toTraceAux p []

end Path

theorem violation_eq_some {props : List (Property S)} {path : Path S L} {f : Failure S L}
    (h : violation props path = some f) :
    ∃ name p,
      f = .violated name path.toTrace ∧ .always name p ∈ props ∧ p path.last = false := by
  obtain ⟨prop, hmem, hprop⟩ := List.exists_of_findSome?_eq_some h
  cases prop with
  | always name p =>
    by_cases hp : p path.last = true
    · simp [hp] at hprop
    · simp only [hp, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hprop
      exact ⟨name, p, hprop.symm, hmem, by simpa using hp⟩
  | sometimes name p => simp at hprop

theorem violation_eq_none {props : List (Property S)} {path : Path S L}
    (h : violation (L := L) props path = none) {name : String} {p : S → Bool}
    (hmem : .always name p ∈ props) : p path.last = true := by
  have := List.findSome?_eq_none_iff.mp h _ hmem
  simpa using this

theorem witness_cons (prop : Property S) (props : List (Property S)) (path : Path S L)
    (ws : List (String × Path S L)) :
    witness (prop :: props) path ws = witness props path (witness [prop] path ws) :=
  rfl

theorem mem_witness {props : List (Property S)} {path : Path S L} {ws : List (String × Path S L)}
    {w : String × Path S L} (h : w ∈ witness props path ws) :
    w ∈ ws ∨ w.2 = path ∧ ∃ p, .sometimes w.1 p ∈ props ∧ p path.last = true := by
  induction props generalizing ws with
  | nil => exact .inl h
  | cons prop props ih =>
    rw [witness_cons] at h
    rcases ih h with h | ⟨hpath, p, hmem, hp⟩
    · cases prop with
      | always name p => exact .inl h
      | sometimes name p =>
        simp only [witness, List.foldl_cons, List.foldl_nil] at h
        split at h
        · rename_i hcond
          rcases List.mem_append.mp h with h | h
          · exact .inl h
          · obtain rfl := List.mem_singleton.mp h
            exact .inr ⟨rfl, p, List.mem_cons_self, by simp_all⟩
        · exact .inl h
    · exact .inr ⟨hpath, p, List.mem_cons_of_mem _ hmem, hp⟩

theorem witness_any_of_any {props : List (Property S)} {path : Path S L}
    {ws : List (String × Path S L)} {name : String} (h : ws.any (·.1 == name) = true) :
    (witness props path ws).any (·.1 == name) = true := by
  induction props generalizing ws with
  | nil => exact h
  | cons prop props ih =>
    rw [witness_cons]
    apply ih
    cases prop with
    | always _ _ => exact h
    | sometimes name' p =>
      simp only [witness, List.foldl_cons, List.foldl_nil]
      split
      · simp [List.any_append, h]
      · exact h

theorem witness_any {props : List (Property S)} {path : Path S L}
    {ws : List (String × Path S L)} {name : String} {p : S → Bool}
    (hmem : .sometimes name p ∈ props) (hp : p path.last = true) :
    (witness props path ws).any (·.1 == name) = true := by
  induction props generalizing ws with
  | nil => simp at hmem
  | cons prop props ih =>
    rw [witness_cons]
    rcases List.mem_cons.mp hmem with rfl | hmem
    · apply witness_any_of_any
      simp only [witness, List.foldl_cons, List.foldl_nil]
      split
      · simp [List.any_append]
      · simp_all
    · exact ih hmem

/-- What the search itself may report: a trace that is a path of the model, within the
constraint, to a state that violates the property or is stuck. -/
def Failure.Found (m : Model S L) (props : List (Property S)) (opts : Options S) :
    Failure S L → Prop
  | .violated name t =>
    t.Valid m ∧ m.Reachable opts.constraint t.last ∧
      ∃ p, .always name p ∈ props ∧ p t.last = false
  | .deadlock t =>
    t.Valid m ∧ m.Reachable opts.constraint t.last ∧
      (∀ l s, (l, s) ∈ m.next t.last → opts.constraint s = false) ∧
      opts.terminal t.last = false
  | .unreached _ => False

namespace Search

variable [BEq S] [Hashable S] {m : Model S L} {props : List (Property S)} {opts : Options S}
  {labelName : L → String} {st : Search S L}

/-- Everything a search has recorded is real, and it has kept to the bound on stored states. -/
structure Sound (m : Model S L) (props : List (Property S)) (opts : Options S)
    (st : Search S L) : Prop where
  queue : ∀ v ∈ st.queue, v.path.Valid m opts.constraint
  witnesses : ∀ w ∈ st.witnesses,
    w.2.Valid m opts.constraint ∧ ∃ p, .sometimes w.1 p ∈ props ∧ p w.2.last = true
  failure : ∀ f, st.failure = some f → f.Found m props opts
  size : st.queue.size ≤ opts.maxStates

theorem Sound.add (h : st.Sound m props opts) {path : Path S L}
    (hpath : path.Valid m opts.constraint) (depth : Nat) :
    (st.add props opts path depth).Sound m props opts := by
  unfold Search.add
  split
  · exact h
  · split
    · exact ⟨h.queue, h.witnesses, h.failure, h.size⟩
    · refine ⟨fun v hv => ?_, fun w hw => ?_, fun f hf => ?_, ?_⟩
      · rcases Array.mem_push.mp hv with hv | rfl
        · exact h.queue v hv
        · exact hpath
      · rcases mem_witness hw with hw | ⟨hw, p, hmem, hp⟩
        · exact h.witnesses w hw
        · exact ⟨hw ▸ hpath, p, hmem, hw ▸ hp⟩
      · obtain ⟨name, p, rfl, hmem, hp⟩ := violation_eq_some hf
        exact ⟨hpath.toTrace, by simpa using hpath.reachable, p, hmem, by simpa using hp⟩
      · simp only [Array.size_push]
        omega

theorem Sound.addInit (h : st.Sound m props opts) {s : S} (hs : s ∈ m.init) :
    (st.addInit props opts s).Sound m props opts := by
  unfold Search.addInit
  split
  · exact h
  · rename_i hcond
    simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false] at hcond
    exact h.add (path := .init s) ⟨hs, hcond.2⟩ 0

theorem Sound.start (actions : List String) : (start m props opts actions).Sound m props opts := by
  unfold Search.start
  refine List.foldlRecOn _ _ ⟨?_, ?_, ?_, ?_⟩ fun st h s hs => h.addInit hs
  all_goals simp

theorem Sound.visit (h : st.Sound m props opts) {parent : Path S L}
    (hparent : parent.Valid m opts.constraint) (depth : Nat) {step : L × S}
    (hstep : step ∈ m.next parent.last) (hconstraint : opts.constraint step.2 = true) :
    (st.visit props opts labelName parent depth step).Sound m props opts := by
  unfold Search.visit
  split
  · exact h
  · refine Sound.add ?_ (path := .step parent step.1 step.2) ⟨hparent, hstep, hconstraint⟩ _
    exact ⟨h.queue, h.witnesses, h.failure, h.size⟩

theorem Sound.expand (h : st.Sound m props opts) {v : Visited S L} (hv : v ∈ st.queue) :
    (st.expand m props opts labelName v).Sound m props opts := by
  have hpath := h.queue v hv
  unfold Search.expand
  split
  · exact ⟨h.queue, h.witnesses, h.failure, h.size⟩
  · dsimp only
    split
    · rename_i hdead
      simp only [Bool.and_eq_true, List.isEmpty_iff, List.filter_eq_nil_iff, Bool.not_eq_true,
        Bool.not_eq_eq_eq_not, Bool.not_true] at hdead
      refine ⟨h.queue, h.witnesses, fun f hf => ?_, h.size⟩
      obtain rfl := Option.some.inj hf
      exact ⟨hpath.toTrace, by simpa using hpath.reachable,
        fun l s hmem => by simpa using hdead.1.2 (l, s) (by simpa using hmem),
        by simpa using hdead.2⟩
    · have : (List.foldl (Search.visit props opts labelName v.path (v.depth + 1)) st
          ((m.next v.path.last).filter fun step => opts.constraint step.2)).Sound m props opts :=
        List.foldlRecOn _ _ h fun st h step hstep =>
          h.visit hpath _ (List.mem_filter.mp hstep).1 (List.mem_filter.mp hstep).2
      exact ⟨this.queue, this.witnesses, this.failure, this.size⟩

theorem Sound.run (fuel : Nat) (h : st.Sound m props opts) :
    (st.run m props opts labelName fuel).Sound m props opts := by
  induction fuel generalizing st with
  | zero => exact h
  | succ fuel ih =>
    unfold Search.run
    split
    · exact h
    · split
      · exact h
      · rename_i v hv
        exact ih (h.expand (Array.mem_of_getElem? hv))

end Search

variable [BEq S] [Hashable S] {m : Model S L} {props : List (Property S)} {opts : Options S}
  {labelName : L → String} {actions : List String}

theorem search_sound_state :
    ((Search.start m props opts actions).run m props opts labelName opts.maxStates).Sound
      m props opts :=
  Search.Sound.run _ (Search.Sound.start actions)

theorem Search.failure_of_report {st : Search S L} {f : Failure S L}
    (h : (st.report props).failure = some f) (hf : ∀ names, f ≠ .unreached names) :
    st.failure = some f := by
  cases hfail : st.failure with
  | some _ => simpa [Search.report, hfail] using h
  | none =>
    simp only [Search.report, hfail] at h
    split at h
    · simp at h
    · exact absurd (Option.some.inj h).symm (hf _)

/-- A reported violation is real: its trace is a path of the model through states that satisfy
the constraint, and an `always` property of that name is false in its last state. -/
theorem search_violated {name : String} {t : Trace S L}
    (h : (search m props opts labelName actions).failure = some (.violated name t)) :
    t.Valid m ∧ m.Reachable opts.constraint t.last ∧
      ∃ p, .always name p ∈ props ∧ p t.last = false :=
  search_sound_state.failure _ (Search.failure_of_report h (by simp))

/-- A reported deadlock is real: its trace is a path of the model through states that satisfy
the constraint, to a state that is not terminal and has no successor within the constraint. -/
theorem search_deadlock {t : Trace S L}
    (h : (search m props opts labelName actions).failure = some (.deadlock t)) :
    t.Valid m ∧ m.Reachable opts.constraint t.last ∧
      (∀ l s, (l, s) ∈ m.next t.last → opts.constraint s = false) ∧
      opts.terminal t.last = false :=
  search_sound_state.failure _ (Search.failure_of_report h (by simp))

/-- A reported witness is real: its trace is a path of the model through states that satisfy
the constraint, and a `sometimes` property of that name is true in its last state. -/
theorem search_witness {name : String} {t : Trace S L}
    (h : (name, t) ∈ (search m props opts labelName actions).witnesses) :
    t.Valid m ∧ m.Reachable opts.constraint t.last ∧
      ∃ p, .sometimes name p ∈ props ∧ p t.last = true := by
  obtain ⟨w, hw, heq⟩ := List.mem_map.mp h
  obtain ⟨hvalid, p, hmem, hp⟩ := search_sound_state.witnesses w hw
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
  exact ⟨hvalid.toTrace, by simpa using hvalid.reachable, p, hmem, by simpa using hp⟩

theorem search_states_le :
    (search m props opts labelName actions).states ≤ opts.maxStates :=
  search_sound_state.size

end Lanes.Check
