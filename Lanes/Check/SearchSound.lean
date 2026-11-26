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

/-- State equality is invisible to the model: equal states have equal successors, up to
equality and whatever the labels, and the constraint and the properties do not tell them
apart. -/
structure Model.Respects [BEq S] (m : Model S L) (constraint : S → Bool)
    (props : List (Property S)) : Prop where
  next : ∀ a b, (a == b) = true → ∀ l a', (l, a') ∈ m.next a →
    ∃ l' b', (l', b') ∈ m.next b ∧ (a' == b') = true
  constraint : ∀ a b, (a == b) = true → constraint a = constraint b
  prop : ∀ p ∈ props, ∀ a b, (a == b) = true → p.holds a = p.holds b

theorem Model.Respects.of_lawful [BEq S] [LawfulBEq S] (m : Model S L) (constraint : S → Bool)
    (props : List (Property S)) : m.Respects constraint props where
  next _ _ hab l a' ha' := ⟨l, a', eq_of_beq hab ▸ ha', BEq.rfl⟩
  constraint _ _ hab := eq_of_beq hab ▸ rfl
  prop _ _ _ _ hab := eq_of_beq hab ▸ rfl

namespace Search

variable [BEq S] [Hashable S] {m : Model S L} {props : List (Property S)} {opts : Options S}
  {labelName : L → String} {actions : List String} {st st' st'' : Search S L}

/-- A state equal to `s` is stored. -/
def Stored (st : Search S L) (s : S) : Prop :=
  ∃ v ∈ st.queue, (v.path.last == s) = true

/-- Nothing so far stops the search from ending as a complete pass. -/
def Live (st : Search S L) : Prop :=
  st.complete = true ∧ st.failure = none

/-- `st'` continues `st`: it has stored more, expanded no more, and is live only if `st` was. -/
structure Le (st st' : Search S L) : Prop where
  queue : ∀ (i : Nat) v, st.queue[i]? = some v → st'.queue[i]? = some v
  complete : st'.complete = true → st.complete = true
  failure : st'.failure = none → st.failure = none
  head : st'.head = st.head

theorem Le.refl (st : Search S L) : st.Le st :=
  ⟨fun _ _ h => h, id, id, rfl⟩

theorem Le.trans (h : st.Le st') (h' : st'.Le st'') : st.Le st'' :=
  ⟨fun i v hv => h'.queue i v (h.queue i v hv), h.complete ∘ h'.complete,
    h.failure ∘ h'.failure, h'.head.trans h.head⟩

theorem Le.live (h : st.Le st') (hlive : st'.Live) : st.Live :=
  ⟨h.complete hlive.1, h.failure hlive.2⟩

theorem Le.stored (h : st.Le st') {s : S} (hs : st.Stored s) : st'.Stored s := by
  obtain ⟨v, hv, hvs⟩ := hs
  obtain ⟨i, hi⟩ := Array.mem_iff_getElem?.mp hv
  exact ⟨v, Array.mem_of_getElem? (h.queue i v hi), hvs⟩

theorem Le.getElem? (h : st.Le st') {i : Nat} (hi : i < st.queue.size) :
    st'.queue[i]? = st.queue[i]? := by
  rw [Array.getElem?_eq_getElem hi]
  exact h.queue i _ (Array.getElem?_eq_getElem hi)

/-- What has been checked of the stored states: `seen` covers only them, no `always` property
fails in one unless a failure is recorded, and each `sometimes` property true in one has a
witness. -/
structure Checked (props : List (Property S)) (st : Search S L) : Prop where
  seen : ∀ s, st.seen.contains s = true → st.Stored s
  always : st.failure = none → ∀ v ∈ st.queue, ∀ name p, .always name p ∈ props →
    p v.path.last = true
  sometimes : ∀ v ∈ st.queue, ∀ name p, .sometimes name p ∈ props →
    p v.path.last = true → st.witnesses.any (·.1 == name) = true

/-- Every initial state and every successor of an expanded state is stored, if within the
constraint; and with deadlock checking on, no expanded state is stuck. -/
structure Closed (m : Model S L) (opts : Options S) (st : Search S L) : Prop where
  init : ∀ s ∈ m.init, opts.constraint s = true → st.Stored s
  next : ∀ (i : Nat) v, i < st.head → st.queue[i]? = some v → ∀ step ∈ m.next v.path.last,
    opts.constraint step.2 = true → st.Stored step.2
  moves : opts.checkDeadlock = true → ∀ (i : Nat) v, i < st.head → st.queue[i]? = some v →
    opts.terminal v.path.last = true ∨
      ∃ step ∈ m.next v.path.last, opts.constraint step.2 = true

theorem le_add (hfailure : st.failure = none) (path : Path S L) (depth : Nat) :
    st.Le (st.add props opts path depth) := by
  unfold Search.add
  split
  · exact .refl st
  · split
    · exact ⟨fun _ _ h => h, fun h => by simp at h, id, rfl⟩
    · refine ⟨fun i v hv => ?_, id, fun _ => hfailure, rfl⟩
      have hi : i < st.queue.size := (Array.getElem?_eq_some_iff.mp hv).1
      simp [Array.getElem?_push, Nat.ne_of_lt hi, hv]

theorem stored_add [ReflBEq S] (h : st.Checked props) {path : Path S L} {depth : Nat}
    (hcomplete : (st.add props opts path depth).complete = true) :
    (st.add props opts path depth).Stored path.last := by
  unfold Search.add at hcomplete ⊢
  split
  · rename_i hseen
    exact h.seen _ hseen
  · rename_i hseen
    split
    · rename_i hfull
      simp [hseen, hfull] at hcomplete
    · exact ⟨_, Array.mem_push_self, BEq.rfl⟩

/-- A fold of steps that each keep `Checked`, continue the search and store their own state
stores the state of every step. -/
theorem foldl_spec {α : Type} {f : Search S L → α → Search S L} {key : α → S}
    {want : α → Prop}
    (hf : ∀ st x, st.Checked props → (f st x).Checked props ∧ st.Le (f st x) ∧
      ((f st x).Live → want x → (f st x).Stored (key x)))
    (xs : List α) (h : st.Checked props) :
    (xs.foldl f st).Checked props ∧ st.Le (xs.foldl f st) ∧
      ((xs.foldl f st).Live → ∀ x ∈ xs, want x → (xs.foldl f st).Stored (key x)) := by
  induction xs generalizing st with
  | nil => exact ⟨h, .refl st, fun _ _ hx => by simp at hx⟩
  | cons x xs ih =>
    obtain ⟨hchecked, hle, hstored⟩ := hf st x h
    obtain ⟨hchecked', hle', hstored'⟩ := ih hchecked
    refine ⟨hchecked', hle.trans hle', fun hlive y hy hwant => ?_⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hle'.stored (hstored (hle'.live hlive) hwant)
    · exact hstored' hlive y hy hwant

/-- Moving `head` past a state whose successors are stored keeps the search closed. -/
theorem Closed.advance (h : st.Closed m opts) (hle : st.Le st') {v : Visited S L}
    (hv : st.queue[st.head]? = some v)
    (hnext : ∀ step ∈ m.next v.path.last, opts.constraint step.2 = true → st'.Stored step.2)
    (hmoves : opts.checkDeadlock = true → opts.terminal v.path.last = true ∨
      ∃ step ∈ m.next v.path.last, opts.constraint step.2 = true) :
    ({ st' with head := st'.head + 1 } : Search S L).Closed m opts := by
  have hhead : st.head < st.queue.size := (Array.getElem?_eq_some_iff.mp hv).1
  have hget : ∀ (i : Nat) w, i < st'.head + 1 → st'.queue[i]? = some w →
      i < st.head ∧ st.queue[i]? = some w ∨ w = v := by
    intro i w hi hw
    rw [hle.head] at hi
    by_cases hlt : i < st.head
    · exact .inl ⟨hlt, by rw [← hle.getElem? (by omega)]; exact hw⟩
    · obtain rfl : i = st.head := by omega
      rw [hle.queue _ v hv] at hw
      exact .inr (Option.some.inj hw).symm
  refine ⟨fun s hs hconstraint => hle.stored (h.init s hs hconstraint),
    fun i w hi hw step hstep hconstraint => ?_, fun hcheck i w hi hw => ?_⟩
  · rcases hget i w hi hw with ⟨hlt, hw⟩ | rfl
    · exact hle.stored (h.next i w hlt hw step hstep hconstraint)
    · exact hnext step hstep hconstraint
  · rcases hget i w hi hw with ⟨hlt, hw⟩ | rfl
    · exact h.moves hcheck i w hlt hw
    · exact hmoves hcheck

section Equiv

variable [EquivBEq S] [LawfulHashable S]

theorem Checked.add (h : st.Checked props) (hfailure : st.failure = none) (path : Path S L)
    (depth : Nat) : (st.add props opts path depth).Checked props := by
  unfold Search.add
  split
  · exact h
  · split
    · exact ⟨h.seen, h.always, h.sometimes⟩
    · refine ⟨fun s hs => ?_, fun hnone v hv name p hmem => ?_, fun v hv name p hmem hp => ?_⟩
      · rw [Std.HashSet.contains_insert, Bool.or_eq_true] at hs
        rcases hs with hs | hs
        · exact ⟨_, Array.mem_push_self, hs⟩
        · obtain ⟨v, hv, hvs⟩ := h.seen s hs
          exact ⟨v, Array.mem_push_of_mem _ hv, hvs⟩
      · rcases Array.mem_push.mp hv with hv | rfl
        · exact h.always hfailure v hv name p hmem
        · exact violation_eq_none hnone hmem
      · rcases Array.mem_push.mp hv with hv | rfl
        · exact witness_any_of_any (h.sometimes v hv name p hmem hp)
        · exact witness_any hmem hp

theorem visit_spec (h : st.Checked props) (parent : Path S L) (depth : Nat) (step : L × S) :
    (st.visit props opts labelName parent depth step).Checked props ∧
      st.Le (st.visit props opts labelName parent depth step) ∧
      ((st.visit props opts labelName parent depth step).Live →
        (st.visit props opts labelName parent depth step).Stored step.2) := by
  unfold Search.visit
  split
  · rename_i hsome
    exact ⟨h, .refl st, fun hlive => by simp [hlive.2] at hsome⟩
  · rename_i hsome
    have hfailure : st.failure = none := by simpa using hsome
    dsimp only
    generalize hcounted : ({ st with
      transitions := st.transitions + 1
      coverage := st.coverage.insert (labelName step.1)
        (st.coverage.getD (labelName step.1) 0 + 1) } : Search S L) = counted
    have hchecked : counted.Checked props := by
      subst hcounted
      exact ⟨h.seen, h.always, h.sometimes⟩
    have hfailure' : counted.failure = none := by
      subst hcounted
      exact hfailure
    have hle : st.Le counted := by
      subst hcounted
      exact ⟨fun _ _ h => h, id, id, rfl⟩
    exact ⟨hchecked.add hfailure' _ _, hle.trans (le_add hfailure' _ _),
      fun hlive => stored_add (path := .step parent step.1 step.2) hchecked hlive.1⟩

theorem addInit_spec (h : st.Checked props) (s : S) :
    (st.addInit props opts s).Checked props ∧ st.Le (st.addInit props opts s) ∧
      ((st.addInit props opts s).Live → opts.constraint s = true →
        (st.addInit props opts s).Stored s) := by
  unfold Search.addInit
  split
  · rename_i hskip
    refine ⟨h, .refl st, fun hlive hs => ?_⟩
    simp [hlive.2, hs] at hskip
  · rename_i hskip
    have hfailure : st.failure = none := by
      simp only [Bool.or_eq_true, not_or] at hskip
      simpa using hskip.1
    exact ⟨h.add hfailure _ _, le_add hfailure _ _,
      fun hlive _ => stored_add (path := .init s) h hlive.1⟩

/-- What holds of a search between expansions. -/
structure Inv (m : Model S L) (props : List (Property S)) (opts : Options S)
    (st : Search S L) : Prop where
  checked : st.Checked props
  closed : st.Live → st.Closed m opts

theorem Inv.start (actions : List String) : (start m props opts actions).Inv m props opts := by
  unfold Search.start
  generalize hst : ({ coverage := actions.foldl (fun c a => c.insert a 0) {} } : Search S L) = st
  have hchecked : st.Checked props := by
    subst hst
    exact ⟨fun s hs => by simp at hs, fun _ v hv => by simp at hv, fun v hv => by simp at hv⟩
  have hhead : st.head = 0 := by
    subst hst
    rfl
  obtain ⟨hchecked', hle, hstored⟩ :=
    foldl_spec (key := id) (want := fun s => opts.constraint s = true)
      (fun st s h => addInit_spec (opts := opts) h s) m.init hchecked
  have hhead' := hle.head.trans hhead
  exact ⟨hchecked', fun hlive =>
    ⟨hstored hlive, fun i v hi => by omega, fun _ i v hi => by omega⟩⟩

theorem Inv.expand (h : st.Inv m props opts) {v : Visited S L}
    (hv : st.queue[st.head]? = some v) :
    (st.expand m props opts labelName v).Inv m props opts := by
  unfold Search.expand
  split
  · exact ⟨⟨h.checked.seen, h.checked.always, h.checked.sometimes⟩,
      fun hlive => absurd hlive.1 (by simp)⟩
  · dsimp only
    split
    · exact ⟨⟨h.checked.seen, fun hnone => by simp at hnone, h.checked.sometimes⟩,
        fun hlive => absurd hlive.2 (by simp)⟩
    · rename_i hdead
      obtain ⟨hchecked, hle, hstored⟩ :=
        foldl_spec (key := fun step : L × S => step.2) (want := fun _ => True)
          (fun st step h =>
            have := visit_spec (opts := opts) (labelName := labelName) h v.path (v.depth + 1) step
            ⟨this.1, this.2.1, fun hlive _ => this.2.2 hlive⟩)
          ((m.next v.path.last).filter fun step => opts.constraint step.2) h.checked
      generalize List.foldl (Search.visit props opts labelName v.path (v.depth + 1)) st
        ((m.next v.path.last).filter fun step => opts.constraint step.2) = st'
        at hchecked hle hstored
      refine ⟨⟨hchecked.seen, hchecked.always, hchecked.sometimes⟩, fun hlive => ?_⟩
      have hlive' : st'.Live := hlive
      refine (h.closed (hle.live hlive')).advance hle hv
        (fun step hstep hconstraint =>
          hstored hlive' step (List.mem_filter.mpr ⟨hstep, hconstraint⟩) trivial)
        fun hcheck => ?_
      simp only [hcheck, Bool.true_and, Bool.and_eq_true, List.isEmpty_iff, Bool.not_eq_true',
        not_and, Bool.not_eq_false] at hdead
      by_cases hterminal : opts.terminal v.path.last = true
      · exact .inl hterminal
      · obtain ⟨step, hstep⟩ := List.exists_mem_of_ne_nil _ fun hnil => hterminal (hdead hnil)
        exact .inr ⟨step, (List.mem_filter.mp hstep).1, (List.mem_filter.mp hstep).2⟩

theorem Inv.run (fuel : Nat) (h : st.Inv m props opts) :
    (st.run m props opts labelName fuel).Inv m props opts := by
  induction fuel generalizing st with
  | zero => exact h
  | succ fuel ih =>
    unfold Search.run
    split
    · exact h
    · split
      · exact h
      · rename_i v hv
        exact ih (h.expand hv)

theorem Inv.final :
    ((Search.start m props opts actions).run m props opts labelName opts.maxStates).Inv
      m props opts :=
  Inv.run _ (Inv.start actions)

end Equiv

theorem Sound.final :
    ((Search.start m props opts actions).run m props opts labelName opts.maxStates).Sound
      m props opts :=
  Sound.run _ (Sound.start actions)

/-- Once nothing is left to expand, every reachable state is stored, up to equality. -/
theorem Closed.stored [EquivBEq S] (hm : m.Respects opts.constraint props)
    (h : st.Closed m opts) (hdone : st.queue.size ≤ st.head) {s : S}
    (hs : m.Reachable opts.constraint s) : st.Stored s := by
  induction hs with
  | init hs hconstraint => exact h.init _ hs hconstraint
  | @step s s' l _ hstep hconstraint ih =>
    obtain ⟨v, hv, hvs⟩ := ih
    obtain ⟨l', b', hb', hsb'⟩ := hm.next s v.path.last (BEq.symm hvs) l s' hstep
    obtain ⟨i, hi⟩ := Array.mem_iff_getElem?.mp hv
    have hlt : i < st.head := Nat.lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp hi).1 hdone
    obtain ⟨w, hw, hwb'⟩ :=
      h.next i v hlt hi (l', b') hb' (hm.constraint s' b' hsb' ▸ hconstraint)
    exact ⟨w, hw, BEq.trans hwb' (BEq.symm hsb')⟩

theorem failure_of_report {f : Failure S L} (h : (st.report props).failure = some f)
    (hf : ∀ names, f ≠ .unreached names) : st.failure = some f := by
  cases hfailure : st.failure with
  | some _ => simpa [Search.report, hfailure] using h
  | none =>
    simp only [Search.report, hfailure] at h
    split at h
    · simp at h
    · exact absurd (Option.some.inj h).symm (hf _)

theorem failure_none_of_report (h : (st.report props).failure = none) : st.failure = none := by
  cases hfailure : st.failure with
  | none => rfl
  | some _ => simp [Search.report, hfailure] at h

theorem done_of_report (hcomplete : (st.report props).complete = true)
    (hfailure : st.failure = none) : st.complete = true ∧ st.queue.size ≤ st.head := by
  simpa [Search.report, hfailure] using hcomplete

theorem unreached_of_report (hsound : st.Sound m props opts) {names : List String}
    (h : (st.report props).failure = some (.unreached names)) {name : String}
    (hname : name ∈ names) :
    st.failure = none ∧ st.witnesses.any (·.1 == name) = false := by
  cases hfailure : st.failure with
  | some f =>
    have hfound := hsound.failure f hfailure
    simp only [Search.report, hfailure, Option.some.injEq] at h
    subst h
    exact hfound.elim
  | none =>
    refine ⟨rfl, ?_⟩
    simp only [Search.report, hfailure] at h
    split at h
    · simp at h
    · obtain rfl := Failure.unreached.inj (Option.some.inj h)
      obtain ⟨prop, _, hprop⟩ := List.mem_filterMap.mp hname
      cases prop with
      | always _ _ => simp at hprop
      | sometimes name' _ =>
        by_cases hany : st.witnesses.any (·.1 == name') = true
        · simp [hany] at hprop
        · simp only [hany] at hprop
          obtain rfl := Option.some.inj hprop
          exact Bool.eq_false_iff.mpr hany

/-- A search that ends as a complete pass has stored a state equal to each reachable one. -/
theorem Inv.stored [EquivBEq S] (h : st.Inv m props opts)
    (hm : m.Respects opts.constraint props) (hfailure : st.failure = none)
    (hcomplete : (st.report props).complete = true) {s : S}
    (hs : m.Reachable opts.constraint s) : st.Stored s :=
  have hdone := done_of_report hcomplete hfailure
  (h.closed ⟨hdone.1, hfailure⟩).stored hm hdone.2 hs

end Search

variable [BEq S] [Hashable S] {m : Model S L} {props : List (Property S)} {opts : Options S}
  {labelName : L → String} {actions : List String}

/-- A reported violation is real: its trace is a path of the model through states that satisfy
the constraint, and an `always` property of that name is false in its last state. -/
theorem search_violated {name : String} {t : Trace S L}
    (h : (search m props opts labelName actions).failure = some (.violated name t)) :
    t.Valid m ∧ m.Reachable opts.constraint t.last ∧
      ∃ p, .always name p ∈ props ∧ p t.last = false :=
  Search.Sound.final.failure _ (Search.failure_of_report h (by simp))

/-- A reported deadlock is real: its trace is a path of the model through states that satisfy
the constraint, to a state that is not terminal and has no successor within the constraint. -/
theorem search_deadlock {t : Trace S L}
    (h : (search m props opts labelName actions).failure = some (.deadlock t)) :
    t.Valid m ∧ m.Reachable opts.constraint t.last ∧
      (∀ l s, (l, s) ∈ m.next t.last → opts.constraint s = false) ∧
      opts.terminal t.last = false :=
  Search.Sound.final.failure _ (Search.failure_of_report h (by simp))

/-- A reported witness is real: its trace is a path of the model through states that satisfy
the constraint, and a `sometimes` property of that name is true in its last state. -/
theorem search_witness {name : String} {t : Trace S L}
    (h : (name, t) ∈ (search m props opts labelName actions).witnesses) :
    t.Valid m ∧ m.Reachable opts.constraint t.last ∧
      ∃ p, .sometimes name p ∈ props ∧ p t.last = true := by
  obtain ⟨w, hw, heq⟩ := List.mem_map.mp h
  obtain ⟨hvalid, p, hmem, hp⟩ := Search.Sound.final.witnesses w hw
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
  exact ⟨hvalid.toTrace, by simpa using hvalid.reachable, p, hmem, by simpa using hp⟩

theorem search_states_le : (search m props opts labelName actions).states ≤ opts.maxStates :=
  Search.Sound.final.size

/--
PASS is sound: if the search reports no failure and is complete, every `always` property holds
in every state reachable within the constraint.

`==` on states need not be equality, only an equivalence with a matching hash that the model,
the constraint and the properties respect.
-/
theorem search_sound [EquivBEq S] [LawfulHashable S] (hm : m.Respects opts.constraint props)
    (hfailure : (search m props opts labelName actions).failure = none)
    (hcomplete : (search m props opts labelName actions).complete = true)
    {name : String} {p : S → Bool} (hp : .always name p ∈ props) {s : S}
    (hs : m.Reachable opts.constraint s) : p s = true := by
  have hnone := Search.failure_none_of_report hfailure
  obtain ⟨v, hv, hvs⟩ := Search.Inv.final.stored hm hnone hcomplete hs
  rw [← Search.Inv.final.checked.always hnone v hv name p hp]
  exact (hm.prop _ hp _ _ hvs).symm

/-- PASS is sound, for a state type whose `==` is equality. -/
theorem search_sound_of_lawful [LawfulBEq S]
    (hfailure : (search m props opts labelName actions).failure = none)
    (hcomplete : (search m props opts labelName actions).complete = true)
    {name : String} {p : S → Bool} (hp : .always name p ∈ props) {s : S}
    (hs : m.Reachable opts.constraint s) : p s = true :=
  search_sound (.of_lawful m opts.constraint props) hfailure hcomplete hp hs

/-- A complete search that reports a `sometimes` property unreached is right: every
`sometimes` property of that name is false in every state reachable within the constraint. -/
theorem search_unreached [EquivBEq S] [LawfulHashable S] (hm : m.Respects opts.constraint props)
    {names : List String}
    (hfailure : (search m props opts labelName actions).failure = some (.unreached names))
    (hcomplete : (search m props opts labelName actions).complete = true)
    {name : String} (hname : name ∈ names) {p : S → Bool} (hp : .sometimes name p ∈ props)
    {s : S} (hs : m.Reachable opts.constraint s) : p s = false := by
  obtain ⟨hnone, hany⟩ := Search.unreached_of_report Search.Sound.final hfailure hname
  obtain ⟨v, hv, hvs⟩ := Search.Inv.final.stored hm hnone hcomplete hs
  cases hps : p s with
  | false => rfl
  | true =>
    have hwitness := Search.Inv.final.checked.sometimes v hv name p hp
      ((hm.prop _ hp _ _ hvs).trans hps)
    rw [hany] at hwitness
    exact absurd hwitness (by simp)

/-- A complete pass with deadlock checking on leaves no deadlock: every state reachable within
the constraint is terminal or has a successor within the constraint. -/
theorem search_deadlock_free [EquivBEq S] [LawfulHashable S]
    (hm : m.Respects opts.constraint props)
    (hterminal : ∀ a b, (a == b) = true → opts.terminal a = opts.terminal b)
    (hcheck : opts.checkDeadlock = true)
    (hfailure : (search m props opts labelName actions).failure = none)
    (hcomplete : (search m props opts labelName actions).complete = true) {s : S}
    (hs : m.Reachable opts.constraint s) :
    opts.terminal s = true ∨ ∃ l s', (l, s') ∈ m.next s ∧ opts.constraint s' = true := by
  have hnone := Search.failure_none_of_report hfailure
  have hdone := Search.done_of_report hcomplete hnone
  obtain ⟨v, hv, hvs⟩ := Search.Inv.final.stored hm hnone hcomplete hs
  obtain ⟨i, hi⟩ := Array.mem_iff_getElem?.mp hv
  have hlt := Nat.lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp hi).1 hdone.2
  rcases (Search.Inv.final.closed ⟨hdone.1, hnone⟩).moves hcheck i v hlt hi with
    h | ⟨step, hstep, h⟩
  · exact .inl (hterminal _ _ hvs ▸ h)
  · obtain ⟨l', b', hb', hsb'⟩ := hm.next _ _ hvs step.1 step.2 hstep
    exact .inr ⟨l', b', hb', hm.constraint _ _ hsb' ▸ h⟩

end Lanes.Check
