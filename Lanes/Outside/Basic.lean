/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Core.Scheduler

/-!
# What the outside may do

A system talks to things it does not contain: clients, clocks, other services. An `Outside` says
what such a thing may do: which inputs it may send, given what it has seen so far.

It is used twice, and that is the point. The model checker explores the system against it
(`Outside.driver`), so properties are checked against everything the outside may do. And a
recorded run of the real system, with the real thing attached, is tested against it
(`Outside.allows`): if the real thing ever does what the model forbids, the properties were
checked against the wrong outside, and the test says so.
-/

@[expose] public section

namespace Lanes

variable {σ : Signature}

structure Outside (σ : Signature) (D : Type) where
  init : D
  /-- Whether the outside may send `x` now, and what it remembers afterwards. -/
  allow : D → σ.In → Option D
  observe : D → σ.Out → D := fun d _ => d

namespace Outside

variable {D E : Type}

/-- Anything, at any time. -/
def any : Outside σ Unit where
  init := ()
  allow _ _ := some ()

/-- The outside as the checker explores it: of the inputs `samples` proposes, those allowed. -/
def driver (outside : Outside σ D) (samples : D → List σ.In) : Driver σ D where
  init := outside.init
  inputs d := (samples d).filterMap fun x => (outside.allow d x).map (x, ·)
  observe := outside.observe

/-- What the outside remembers after one more event, or `none` if it is an input not allowed. -/
def see (outside : Outside σ D) (d : D) : Event σ → Option D
  | .input x => outside.allow d x
  | .output out => some (outside.observe d out)
  | _ => some d

/-- What the outside remembers after `events`, or `none` if one of the inputs among them was
not allowed. -/
def after (outside : Outside σ D) (events : List (Event σ)) : Option D :=
  events.foldlM outside.see outside.init

/-- Whether a recorded run shows the outside doing only what this model allows. -/
def allows (outside : Outside σ D) (events : List (Event σ)) : Bool :=
  (outside.after events).isSome

/-- Two things outside at once, each sending its own kind of input: `first` says which inputs
are the first one's. A kind of input that both may send has no model as a pair, because the
model would have to guess who sent it, and a guess loses runs. -/
def both (a : Outside σ D) (b : Outside σ E) (first : σ.In → Bool) : Outside σ (D × E) where
  init := (a.init, b.init)
  allow d x := if first x then (a.allow d.1 x).map (·, d.2) else (b.allow d.2 x).map (d.1, ·)
  observe d out := (a.observe d.1 out, b.observe d.2 out)

@[simp] theorem after_nil (outside : Outside σ D) : outside.after [] = some outside.init := rfl

theorem after_concat (outside : Outside σ D) (events : List (Event σ)) (event : Event σ) :
    outside.after (events ++ [event]) = (outside.after events).bind (outside.see · event) := by
  simp only [after, List.foldlM_append, List.foldlM_cons, List.foldlM_nil]
  cases List.foldlM outside.see outside.init events with
  | none => rfl
  | some d => cases h : outside.see d event <;> simp [h, bind, Option.bind]

/-- Induction along a run the outside allows, for properties that relate the events so far to
what it remembers. -/
theorem after_induction (outside : Outside σ D) {P : List (Event σ) → D → Prop}
    (init : P [] outside.init)
    (step : ∀ events d event d', P events d → outside.see d event = some d' →
      P (events ++ [event]) d')
    {events : List (Event σ)} {d : D} (h : outside.after events = some d) : P events d := by
  suffices h' : ∀ (rest pre : List (Event σ)) (d₀ : D), P pre d₀ →
      rest.foldlM outside.see d₀ = some d → P (pre ++ rest) d from h' events [] _ init h
  intro rest
  induction rest with
  | nil =>
    intro pre d₀ hP hfold
    simp only [List.foldlM_nil, pure, Option.some.injEq] at hfold
    simpa [← hfold] using hP
  | cons event rest ih =>
    intro pre d₀ hP hfold
    simp only [List.foldlM_cons, bind, Option.bind] at hfold
    cases hsee : outside.see d₀ event with
    | none => simp [hsee] at hfold
    | some d₁ =>
      simp only [hsee] at hfold
      simpa using ih (pre ++ [event]) d₁ (step pre d₀ event d₁ hP hsee) hfold

/-- What the outside's start has, every input it allows keeps and every output `good` admits
keeps, it has after every run whose outputs `good` admits. -/
theorem after_invariant (outside : Outside σ D) (good : σ.Out → Prop) (P : D → Prop)
    (init : P outside.init) (allow : ∀ d x d', P d → outside.allow d x = some d' → P d')
    (observe : ∀ d out, P d → good out → P (outside.observe d out)) {events : List (Event σ)}
    (hgood : ∀ out, Event.output out ∈ events → good out) {d : D}
    (h : outside.after events = some d) : P d := by
  have := outside.after_induction (P := fun events d =>
      (∀ out, Event.output out ∈ events → good out) → P d) (fun _ => init)
    (fun events d event d' ih hsee hgood => by
      have hd := ih fun out hout => hgood out (List.mem_append_left _ hout)
      cases event with
      | input x => exact allow d x d' hd hsee
      | output out =>
        simp only [see, Option.some.injEq] at hsee
        exact hsee ▸ observe d out hd (hgood out (by simp))
      | _ => simp only [see, Option.some.injEq] at hsee; exact hsee ▸ hd) h
  exact this hgood

/-- Of two outsides at once, each remembers what it would alone after the events it sees: the
inputs `first` gives it, or does not, and everything else. -/
def mine (first : σ.In → Bool) (left : Bool) : Event σ → Bool
  | .input x => first x == left
  | _ => true

theorem after_both (a : Outside σ D) (b : Outside σ E) (first : σ.In → Bool)
    {events : List (Event σ)} {d : D × E} (h : (a.both b first).after events = some d) :
    a.after (events.filter (mine first true)) = some d.1 ∧
      b.after (events.filter (mine first false)) = some d.2 := by
  refine (a.both b first).after_induction (P := fun events d =>
      a.after (events.filter (mine first true)) = some d.1 ∧
        b.after (events.filter (mine first false)) = some d.2) ⟨rfl, rfl⟩ ?_ h
  intro events d event d' ⟨ha, hb⟩ hsee
  cases event with
  | input x =>
    simp only [see, both] at hsee
    by_cases hx : first x = true
    · simp only [hx, ↓reduceIte, Option.map_eq_some_iff] at hsee
      obtain ⟨d₁, hd₁, rfl⟩ := hsee
      simp [List.filter_append, List.filter_nil, mine, hx, after_concat, ha, hb, see, hd₁]
    · simp only [hx, Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff] at hsee
      obtain ⟨d₂, hd₂, rfl⟩ := hsee
      simp [List.filter_append, List.filter_nil, mine, hx, after_concat, ha, hb, see, hd₂]
  | output out =>
    simp only [see, both, Option.some.injEq] at hsee
    subst hsee
    simp [List.filter_append, List.filter_cons, List.filter_nil, mine, after_concat, ha, hb, see]
  | _ =>
    simp only [see, Option.some.injEq] at hsee
    subst hsee
    simp [List.filter_append, List.filter_cons, List.filter_nil, mine, after_concat, ha, hb, see]

/-- Every input the checker explores is one the model allows, with the same memory after. -/
theorem allow_of_mem_driver (outside : Outside σ D) (samples : D → List σ.In) {d d' : D}
    {x : σ.In} (h : (x, d') ∈ (outside.driver samples).inputs d) : outside.allow d x = some d' := by
  simp only [driver, List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨x', _, d'', hallow, rfl, rfl⟩ := h
  exact hallow

end Outside

end Lanes
