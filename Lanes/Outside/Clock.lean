/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Outside.Basic

/-!
# Clocks

A system asks the time with an output and is told with an input (`Lanes/Outside/IO/Clock.lean`
is the adapter). Two models of what it may be told:

- `Clock.outside`, a monotonic clock: never a time earlier than one it gave
  (`Clock.outside_ge`). The adapter's `Wall` clock is one, since it never goes back.
- `Clock.wall skew_ms`, the wall clock as the operating system reads it: each reading is within
  `skew_ms` of a true time that never goes back, so NTP may step it back or forward between two
  readings. A reading is never more than twice the skew before one given earlier
  (`Clock.wall_back_le`), and may be that far before it.

A duration worked out as the difference of two wall-clock readings may be negative, or zero in
`Nat`, however much time passed; one worked out from a monotonic clock may not.
-/

@[expose] public section

namespace Lanes.Clock

variable {σ : Signature}

/-- Which outputs ask the time and which inputs tell it. `told` reads back what `tell` made. -/
structure Port (σ : Signature) where
  asked : σ.Out → Option Nat
  tell : (question time_ms : Nat) → σ.In
  told : σ.In → Option (Nat × Nat)

/-- What a clock may do: answer a question that was asked and not yet answered, with a time no
earlier than any it has given. It may also not answer. It remembers the open questions and the
last time it gave. -/
def outside (port : Port σ) : Outside σ (List Nat × Nat) where
  init := ([], 0)
  allow d x :=
    match port.told x with
    | some (question, time_ms) =>
      if question ∈ d.1 ∧ d.2 ≤ time_ms then some (d.1.erase question, time_ms) else none
    | none => none
  observe d out :=
    match port.asked out with
    | some question => (question :: d.1, d.2)
    | none => d

/-- A monotonic clock never tells a time earlier than the last it told. -/
theorem outside_ge (port : Port σ) {d d' : List Nat × Nat} {x : σ.In} {question time_ms : Nat}
    (hx : port.told x = some (question, time_ms)) (h : (outside port).allow d x = some d') :
    d.2 ≤ time_ms := by
  simp only [outside, hx] at h
  split at h
  · next hok => exact hok.2
  · simp at h

/-- What a wall clock has said: the open questions, the earliest the true time may now be, and
the latest reading. -/
structure Readings where
  asked : List Nat := []
  floor_ms : Nat := 0
  latest_ms : Nat := 0
  deriving DecidableEq, Repr, Hashable

/-- What a wall clock may do: answer an open question with any time within `skew_ms` of a true
time no earlier than the true time of any earlier reading. -/
def wall (port : Port σ) (skew_ms : Nat) : Outside σ Readings where
  init := {}
  allow d x :=
    match port.told x with
    | some (question, time_ms) =>
      if question ∈ d.asked ∧ d.floor_ms ≤ time_ms + skew_ms then
        some { asked := d.asked.erase question, floor_ms := max d.floor_ms (time_ms - skew_ms)
               latest_ms := max d.latest_ms time_ms }
      else none
    | none => none
  observe d out :=
    match port.asked out with
    | some question => { d with asked := question :: d.asked }
    | none => d

/-- No reading so far is more than the skew after the earliest the true time may be. -/
theorem wall_latest_le (port : Port σ) (skew_ms : Nat) {events : List (Event σ)} {d : Readings}
    (h : (wall port skew_ms).after events = some d) : d.latest_ms ≤ d.floor_ms + skew_ms := by
  refine (wall port skew_ms).after_invariant (fun _ => True)
    (fun d => d.latest_ms ≤ d.floor_ms + skew_ms) (by simp [wall]) ?_ ?_ (fun _ _ => trivial) h
  · intro d x d' hd hallow
    simp only [wall] at hallow
    split at hallow
    · split at hallow
      · obtain rfl := Option.some.inj hallow
        simp only
        omega
      · simp at hallow
    · simp at hallow
  · intro d out hd _
    simp only [wall]
    split <;> exact hd

/-- A wall clock may be set back, but never by more than twice its skew: in every run the model
allows, a reading it may give next is at most `2 * skew_ms` before the latest it gave. -/
theorem wall_back_le (port : Port σ) (skew_ms : Nat) {events : List (Event σ)} {d d' : Readings}
    (h : (wall port skew_ms).after events = some d) {x : σ.In} {question time_ms : Nat}
    (hx : port.told x = some (question, time_ms)) (hallow : (wall port skew_ms).allow d x = some d') :
    d.latest_ms ≤ time_ms + 2 * skew_ms := by
  have hle := wall_latest_le port skew_ms h
  simp only [wall, hx] at hallow
  split at hallow
  · next hok => omega
  · simp at hallow

end Lanes.Clock
