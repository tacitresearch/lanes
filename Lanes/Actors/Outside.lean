/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Actors.Scheduler

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

/-- What the outside remembers after `events`, or `none` if one of the inputs among them was
not allowed. -/
def after (outside : Outside σ D) (events : List (Event σ)) : Option D :=
  events.foldlM (init := outside.init) fun d event =>
    match event with
    | .input x => outside.allow d x
    | .output out => some (outside.observe d out)
    | _ => some d

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

/-- Every input the checker explores is one the model allows, with the same memory after. -/
theorem allow_of_mem_driver (outside : Outside σ D) (samples : D → List σ.In) {d d' : D}
    {x : σ.In} (h : (x, d') ∈ (outside.driver samples).inputs d) : outside.allow d x = some d' := by
  simp only [driver, List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨x', _, d'', hallow, rfl, rfl⟩ := h
  exact hallow

end Outside

end Lanes
