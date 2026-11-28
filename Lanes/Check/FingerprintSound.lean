/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Check.Fingerprint
public import Lanes.Check.SystemSound

/-!
# What a fingerprinted search reports is real

`Check.fingerprint` keeps hashes, not states, so a pass proves nothing about the states a
collision hid. What it reports does not depend on the hashes: a trace is replayed from the
recorded choices through `Model.next`, and the property, deadlock or witness is checked again on
the state the replay reaches.

- `fingerprint_violated`, `fingerprint_deadlock`, `fingerprint_witness`: the same statements as
  `search_violated`, `search_deadlock` and `search_witness`, for any hash.
- `systemFingerprinted_violated`: a violation `Check.systemFingerprinted` reports is a run of the
  semantics from the initial state, as `system_violated` says of `Check.system`.
-/

@[expose] public section

namespace Lanes.Check

variable {S L : Type} {m : Model S L} {constraint : S → Bool}

namespace Fingerprint

theorem replaySteps_valid : ∀ {s : S} {ks : List Nat} {steps : List (L × S)},
    replaySteps m constraint s ks = some steps → m.Reachable constraint s →
      m.Steps s steps ∧ m.Reachable constraint (Trace.mk s steps).last
  | s, [], steps, h, hs => by
    simp only [replaySteps, Option.some.injEq] at h
    subst h
    exact ⟨trivial, hs⟩
  | s, k :: ks, steps, h, hs => by
    simp only [replaySteps] at h
    split at h
    · rename_i l t hk
      split at h
      · rename_i ht
        obtain ⟨rest, hrest, rfl⟩ := Option.map_eq_some_iff.mp h
        have hmem : (l, t) ∈ m.next s := List.mem_of_getElem? hk
        obtain ⟨hsteps, hlast⟩ := replaySteps_valid hrest (.step hs hmem ht)
        exact ⟨⟨hmem, hsteps⟩, by rw [Trace.last_cons]; exact hlast⟩
      · simp at h
    · simp at h

/-- A replayed trace is a path of the model from an initial state, through states within the
constraint. -/
theorem replay_valid {ks : List Nat} {t : Trace S L} (h : replay m constraint ks = some t) :
    t.Valid m ∧ m.Reachable constraint t.last := by
  cases ks with
  | nil => simp [replay] at h
  | cons k ks =>
    simp only [replay] at h
    split at h
    · rename_i s hk
      split at h
      · rename_i hs
        obtain ⟨steps, hsteps, rfl⟩ := Option.map_eq_some_iff.mp h
        have hinit : s ∈ m.init := List.mem_of_getElem? hk
        obtain ⟨hvalid, hlast⟩ := replaySteps_valid hsteps (.init hinit hs)
        exact ⟨⟨hinit, hvalid⟩, hlast⟩
      · simp at h
    · simp at h

variable {props : List (Property S)} {opts : Options S}

theorem recheck_violated {f : Found} {t t' : Trace S L} {name : String}
    (h : recheck props opts m f t = some (.violated name t')) :
    t' = t ∧ ∃ p, .always name p ∈ props ∧ p t.last = false := by
  cases f with
  | deadlock _ =>
    simp only [recheck] at h
    split at h <;> simp at h
  | violated _ =>
    obtain ⟨prop, hprop, hsome⟩ := List.exists_of_findSome?_eq_some h
    cases prop with
    | sometimes _ _ => simp at hsome
    | always name' p =>
      simp only at hsome
      split at hsome
      · simp at hsome
      · rename_i hp
        simp only [Option.some.injEq, Failure.violated.injEq] at hsome
        obtain ⟨rfl, rfl⟩ := hsome
        exact ⟨rfl, p, hprop, by simpa using hp⟩

theorem recheck_deadlock {f : Found} {t t' : Trace S L}
    (h : recheck props opts m f t = some (.deadlock t')) :
    t' = t ∧ (∀ l s, (l, s) ∈ m.next t.last → opts.constraint s = false) ∧
      opts.terminal t.last = false := by
  cases f with
  | violated _ =>
    obtain ⟨prop, _, hsome⟩ := List.exists_of_findSome?_eq_some h
    cases prop with
    | sometimes _ _ => simp at hsome
    | always _ p =>
      simp only at hsome
      split at hsome <;> simp at hsome
  | deadlock _ =>
    simp only [recheck] at h
    split at h
    · rename_i hstuck
      simp only [Option.some.injEq, Failure.deadlock.injEq] at h
      subst h
      simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hstuck
      exact ⟨rfl, fun l s hs => hstuck.1 (l, s) hs, hstuck.2⟩
    · simp at h

variable {st : Search S}

/-- A failure in the report, other than unreached properties, is one a replay showed. -/
theorem report_failure {fl : Failure S L} (h : (st.report m props opts).failure = some fl)
    (hfl : ∀ names, fl ≠ .unreached names) :
    ∃ f t, replay m opts.constraint (st.choicesTo st.parents.size f.record []) = some t ∧
      recheck props opts m f t = some fl := by
  simp only [Search.report] at h
  split at h
  · rename_i f' hf'
    obtain rfl := Option.some.inj h
    obtain ⟨f, _, hbind⟩ := Option.bind_eq_some_iff.mp hf'
    obtain ⟨t, ht, hre⟩ := Option.bind_eq_some_iff.mp hbind
    exact ⟨f, t, ht, hre⟩
  · split at h
    · simp at h
    · exact absurd (Option.some.inj h).symm (hfl _)

theorem report_violated {name : String} {t : Trace S L}
    (h : (st.report m props opts).failure = some (.violated name t)) :
    t.Valid m ∧ m.Reachable opts.constraint t.last ∧
      ∃ p, .always name p ∈ props ∧ p t.last = false := by
  obtain ⟨f, t', ht', hre⟩ := report_failure h (by simp)
  obtain ⟨rfl, hp⟩ := recheck_violated hre
  exact ⟨(replay_valid ht').1, (replay_valid ht').2, hp⟩

theorem report_deadlock {t : Trace S L}
    (h : (st.report m props opts).failure = some (.deadlock t)) :
    t.Valid m ∧ m.Reachable opts.constraint t.last ∧
      (∀ l s, (l, s) ∈ m.next t.last → opts.constraint s = false) ∧
      opts.terminal t.last = false := by
  obtain ⟨f, t', ht', hre⟩ := report_failure h (by simp)
  obtain ⟨rfl, hp⟩ := recheck_deadlock hre
  exact ⟨(replay_valid ht').1, (replay_valid ht').2, hp⟩

theorem report_witness {name : String} {t : Trace S L}
    (h : (name, t) ∈ (st.report m props opts).witnesses) :
    t.Valid m ∧ m.Reachable opts.constraint t.last ∧
      ∃ p, .sometimes name p ∈ props ∧ p t.last = true := by
  simp only [Search.report, List.mem_filterMap] at h
  obtain ⟨⟨prop, found⟩, hmem, hsome⟩ := h
  have hprop := List.of_mem_zip hmem |>.1
  cases prop with
  | always _ _ => simp at hsome
  | sometimes name' p =>
    cases found with
    | none => simp at hsome
    | some r =>
      obtain ⟨t', ht', hsome⟩ := Option.bind_eq_some_iff.mp hsome
      split at hsome
      · rename_i hp
        simp only [Option.some.injEq, Prod.mk.injEq] at hsome
        obtain ⟨rfl, rfl⟩ := hsome
        exact ⟨(replay_valid ht').1, (replay_valid ht').2, p, hprop, hp⟩
      · simp at hsome

namespace Search

variable [Hashable S] {labelName : L → String}

theorem foldl_expand (entries : List (S × Nat)) (st : Search S) :
    entries.foldl (expand m props opts labelName) st =
      (entries.map fun e => (e, successors m opts e.1)).foldl
        (fun st (e, succs) => st.expandWith props opts labelName e succs) st := by
  rw [List.foldl_map]
  rfl

theorem expandInTasks_eq : ∀ (fuel : Nat) (entries : List (S × Nat)) (st : Search S),
    expandInTasks m props opts labelName fuel entries st =
      entries.foldl (expand m props opts labelName) st
  | 0, _, _ => rfl
  | fuel + 1, entries, st => by
    rw [expandInTasks]
    split
    · rename_i h
      rw [List.isEmpty_iff.mp h]
      rfl
    · rw [expandInTasks_eq fuel, ← List.foldl_flatMap, Check.Search.flatMap_mapInTasks,
        ← foldl_expand, ← List.foldl_append, List.take_append_drop]

/-- Computing each level's successors in tasks changes nothing: the parallel run stores the same
states, in the same order, with the same records, and so gives the same report. -/
theorem runParallel_eq : ∀ (fuel : Nat) (st : Search S),
    st.runParallel m props opts labelName fuel = st.run m props opts labelName fuel
  | 0, _ => rfl
  | fuel + 1, st => by
    rw [runParallel, run]
    split
    · rfl
    · rw [expandInTasks_eq, Array.foldl_toList, runParallel_eq fuel]

end Search

end Fingerprint

/-- With `Options.tasks` the fingerprinted search is the same function. -/
theorem fingerprint_tasks [Hashable S] {props : List (Property S)} {opts : Options S}
    {labelName : L → String} {actions : List String} :
    fingerprint m props opts labelName actions =
      ((Fingerprint.Search.start m props opts actions).run m props opts labelName
        (opts.maxStates + 1)).report m props opts := by
  unfold fingerprint
  split <;> simp only [Fingerprint.Search.runParallel_eq]

variable [Hashable S] {props : List (Property S)} {opts : Options S} {labelName : L → String}
  {actions : List String}

/-- A violation a fingerprinted search reports is real, whatever the hash: its trace is a path
of the model through states that satisfy the constraint, and an `always` property of that name
is false in its last state. -/
theorem fingerprint_violated {name : String} {t : Trace S L}
    (h : (fingerprint m props opts labelName actions).failure = some (.violated name t)) :
    t.Valid m ∧ m.Reachable opts.constraint t.last ∧
      ∃ p, .always name p ∈ props ∧ p t.last = false :=
  Fingerprint.report_violated h

/-- A deadlock a fingerprinted search reports is real, whatever the hash. -/
theorem fingerprint_deadlock {t : Trace S L}
    (h : (fingerprint m props opts labelName actions).failure = some (.deadlock t)) :
    t.Valid m ∧ m.Reachable opts.constraint t.last ∧
      (∀ l s, (l, s) ∈ m.next t.last → opts.constraint s = false) ∧
      opts.terminal t.last = false :=
  Fingerprint.report_deadlock h

/-- A witness a fingerprinted search reports is real, whatever the hash. -/
theorem fingerprint_witness {name : String} {t : Trace S L}
    (h : (name, t) ∈ (fingerprint m props opts labelName actions).witnesses) :
    t.Valid m ∧ m.Reachable opts.constraint t.last ∧
      ∃ p, .sometimes name p ∈ props ∧ p t.last = true :=
  Fingerprint.report_witness h

/-- A fingerprinted report says so. -/
theorem fingerprint_fingerprinted :
    (fingerprint m props opts labelName actions).fingerprinted = true :=
  rfl

variable {σ : Signature} {sys : System σ} {D : Type}

/--
A violation `Check.systemFingerprinted` reports is real, whatever the hashes: the events of its
trace are a run of the semantics from the initial state, and the named property is false in the
state they reach.
-/
theorem systemFingerprinted_violated [σ.Inspect] [sys.Inspect] [Hashable D] (sc : Scenario σ D)
    (props : List (Property (World sys D))) (opts : Options (World sys D)) {name : String}
    {t : Trace (World sys D) (Event σ)}
    (h : (systemFingerprinted sys sc props opts).failure = some (.violated name t)) :
    (SysState.init sys sc.env).run sc.env t.labels = some t.last.state ∧
      ∃ p, .always name p ∈ props ∧ p t.last = false := by
  simp only [systemFingerprinted, Report.map, Option.map_eq_some_iff] at h
  obtain ⟨failure, hsearch, hmap⟩ := h
  cases failure with
  | deadlock t₀ => simp at hmap
  | unreached names => simp at hmap
  | violated name₀ t₀ =>
    simp only [Failure.violated.injEq] at hmap
    obtain ⟨rfl, rfl⟩ := hmap
    obtain ⟨⟨hinit, hsteps⟩, _, p', hp', hfalse⟩ := fingerprint_violated hsearch
    obtain ⟨prop, hprop, hprop'⟩ := List.mem_map.mp hp'
    rw [Trace.last_map, Trace.labels_map]
    have hstart : t₀.init.world.state = SysState.init sys sc.env := by
      rw [mem_model_init.mp hinit]
      rfl
    refine ⟨?_, ?_⟩
    · rw [← hstart]
      exact run_of_steps t₀.init t₀.steps hsteps
    · cases prop with
      | sometimes n q => simp at hprop'
      | always n q =>
        simp only [Property.always.injEq] at hprop'
        obtain ⟨rfl, rfl⟩ := hprop'
        exact ⟨q, hprop, hfalse⟩

end Lanes.Check
