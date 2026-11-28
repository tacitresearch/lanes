/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Init

/-!
# Infinite sequences

An infinite run of a system is a pair of infinite sequences, of states and of events. Here an
infinite sequence is a plain function `Nat → α`, named `ωSequence α` so that its operations can
be written with dot notation (`r.event.take n`). The names follow CSLib's ω-sequences
(`leanprover/cslib`, Apache-2.0, by Ching-Tsun Chou and Fabrizio Montesi).

A run is cut into finite blocks by a strictly increasing sequence of positions; `segment f k` is
the block that position `k` falls in.

## Main definitions

- `ωSequence α`: `Nat → α`.
- `ωSequence.take n s`: the first `n` elements, as a list.
- `ωSequence.LeadsTo s p q`: wherever `p` holds, `q` holds then or later.
- `StrictMono f`: `f : Nat → Nat` is strictly increasing.
- `segment f k`: the `m` with `f m ≤ k < f (m + 1)`, when `f` is strictly increasing from `0`.

## Main statements

- `ωSequence.leadsTo_trans`: leads-to is transitive.
- `segment_lower_bound`, `segment_upper_bound`, `segment_range_val`: what `segment` is.
-/

@[expose] public section

namespace Lanes

universe u

/-- An infinite sequence: a function from positions. -/
abbrev ωSequence (α : Type u) := Nat → α

namespace ωSequence

variable {α : Type u}

/-- The sequence that is `a` everywhere. -/
def const (a : α) : ωSequence α := fun _ => a

/-- The first `n` elements of `s`. -/
def take (n : Nat) (s : ωSequence α) : List α :=
  (List.range n).map s

/-- No elements. -/
@[simp] theorem take_zero (s : ωSequence α) : s.take 0 = [] := rfl

/-- `take n` has `n` elements. -/
@[simp] theorem length_take (n : Nat) (s : ωSequence α) : (s.take n).length = n := by
  simp [take]

/-- The `m`th element of `take n s` is `s m`. -/
@[simp] theorem take_get {s : ωSequence α} {m n : Nat} (h : m < (s.take n).length) :
    (s.take n)[m] = s m := by
  simp [take]

/-- One more element. -/
theorem take_succ' {s : ωSequence α} (n : Nat) : s.take (n + 1) = s.take n ++ [s n] := by
  simp [take, List.range_succ]

/-- `p` leads to `q` along `s`: wherever `p` holds, `q` holds at the same or a later position. -/
def LeadsTo (s : ωSequence α) (p q : α → Prop) : Prop :=
  ∀ k, p (s k) → ∃ k', k ≤ k' ∧ q (s k')

/-- Leads-to is transitive. -/
theorem leadsTo_trans {s : ωSequence α} {p q r : α → Prop} (h₁ : s.LeadsTo p q)
    (h₂ : s.LeadsTo q r) : s.LeadsTo p r := by
  intro k hp
  obtain ⟨k₁, hk₁, hq⟩ := h₁ k hp
  obtain ⟨k₂, hk₂, hr⟩ := h₂ k₁ hq
  exact ⟨k₂, Nat.le_trans hk₁ hk₂, hr⟩

end ωSequence

/-- Induction on the positions from `m` on: `P` holds at `m`, and at `n + 1` if at `n`. Use it as
`induction n, hn using le_induction with | base => _ | succ n hn ih => _`. -/
@[elab_as_elim]
theorem le_induction {m : Nat} {P : ∀ n, m ≤ n → Prop} (base : P m (Nat.le_refl m))
    (succ : ∀ n hmn, P n hmn → P (n + 1) (Nat.le_succ_of_le hmn)) : ∀ n hmn, P n hmn := by
  intro n hmn
  induction hmn with
  | refl => exact base
  | step hmn ih => exact succ _ hmn ih

/-! ### Strictly increasing sequences of positions -/

/-- `f` is strictly increasing. -/
def StrictMono (f : Nat → Nat) : Prop :=
  ∀ ⦃a b⦄, a < b → f a < f b

namespace StrictMono

variable {f g : Nat → Nat}

/-- A sequence that grows at each step is strictly increasing. -/
theorem of_lt_succ (h : ∀ n, f n < f (n + 1)) : StrictMono f := by
  intro a b hab
  induction b with
  | zero => exact absurd hab (Nat.not_lt_zero _)
  | succ b ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hab with hab | rfl
    · exact Nat.lt_trans (ih hab) (h b)
    · exact h a

/-- Strictly increasing sequences compose. -/
theorem comp (hf : StrictMono f) (hg : StrictMono g) : StrictMono (f ∘ g) :=
  fun _ _ h => hf (hg h)

/-- Adding a constant is strictly increasing. -/
theorem add_const (c : Nat) : StrictMono (· + c) :=
  fun _ _ h => Nat.add_lt_add_right h c

/-- A strictly increasing sequence is increasing. -/
theorem monotone (hf : StrictMono f) {a b : Nat} (h : a ≤ b) : f a ≤ f b := by
  rcases Nat.eq_or_lt_of_le h with rfl | h
  · exact Nat.le_refl _
  · exact Nat.le_of_lt (hf h)

/-- A strictly increasing sequence reflects `<`. -/
theorem lt_iff_lt (hf : StrictMono f) {a b : Nat} : f a < f b ↔ a < b := by
  refine ⟨fun h => ?_, fun h => hf h⟩
  exact Nat.lt_of_not_le fun hba => Nat.not_le_of_lt h (hf.monotone hba)

/-- A strictly increasing sequence is at least the identity. -/
theorem le_apply (hf : StrictMono f) (n : Nat) : n ≤ f n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih => exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt ih (hf (Nat.lt_succ_self n)))

end StrictMono

/-- The largest `m ≤ n` with `f m ≤ k`, or `0`. -/
def segmentFrom (f : Nat → Nat) (k : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => if f (m + 1) ≤ k then m + 1 else segmentFrom f k m

/-- The segment of `k` under a strictly increasing `f` with `f 0 = 0`: the `m` with
`f m ≤ k < f (m + 1)` (`segment_range_val`). -/
def segment (f : Nat → Nat) (k : Nat) : Nat :=
  segmentFrom f k k

variable {f : Nat → Nat}

private theorem segmentFrom_le {k : Nat} (h0 : f 0 ≤ k) :
    ∀ m, f (segmentFrom f k m) ≤ k
  | 0 => h0
  | m + 1 => by
    simp only [segmentFrom]
    split
    · assumption
    · exact segmentFrom_le h0 m

private theorem lt_of_segmentFrom_lt (k : Nat) :
    ∀ m j, segmentFrom f k m < j → j ≤ m → k < f j
  | 0, j, h, hj => absurd (Nat.lt_of_lt_of_le h hj) (Nat.lt_irrefl 0)
  | m + 1, j, h, hj => by
    simp only [segmentFrom] at h
    split at h
    · exact absurd (Nat.lt_of_lt_of_le h hj) (Nat.lt_irrefl _)
    · rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hj) with hj | rfl
      · exact lt_of_segmentFrom_lt k m j h (Nat.le_of_lt_succ hj)
      · exact Nat.lt_of_not_le ‹_›

/-- Position `k` is at or after the start of its segment. -/
theorem segment_lower_bound (_hm : StrictMono f) (h0 : f 0 = 0) (k : Nat) :
    f (segment f k) ≤ k :=
  segmentFrom_le (by rw [h0]; exact Nat.zero_le k) k

private theorem lt_segment_succ (hm : StrictMono f) (k : Nat) : k < f (segment f k + 1) := by
  by_cases h : segment f k + 1 ≤ k
  · exact lt_of_segmentFrom_lt k k _ (Nat.lt_succ_self _) h
  · exact Nat.lt_of_lt_of_le (Nat.lt_of_not_le h) (hm.le_apply _)

/-- Position `k` is before the start of the next segment. -/
theorem segment_upper_bound (hm : StrictMono f) (_h0 : f 0 = 0) (k : Nat) :
    k < f (segment f k + 1) :=
  lt_segment_succ hm k

/-- A position between the starts of segment `m` and the next is in segment `m`. -/
theorem segment_range_val (hm : StrictMono f) {m k : Nat} (hl : f m ≤ k) (hu : k < f (m + 1)) :
    segment f k = m := by
  have hlo : f (segment f k) ≤ k :=
    segmentFrom_le (Nat.le_trans (hm.monotone (Nat.zero_le m)) hl) k
  have hhi := lt_segment_succ hm k
  have h₁ : segment f k < m + 1 := hm.lt_iff_lt.mp (Nat.lt_of_le_of_lt hlo hu)
  have h₂ : m < segment f k + 1 := hm.lt_iff_lt.mp (Nat.lt_of_le_of_lt hl hhi)
  omega

end Lanes
