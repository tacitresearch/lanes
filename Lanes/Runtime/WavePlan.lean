/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std

/-!
How a batch of journal entries splits into waves, when an entry may touch several actors.

Two entries conflict when they touch an actor in common. Each entry goes in the earliest wave
after the waves of every earlier entry it conflicts with (`levels`), so the entries of a wave
touch no actor in common (`disjoint_of_split`) and each actor's entries are in waves in the
order the journal has them (`levels_lt`): applying the waves one after another, the entries of
each wave in parallel, gives each actor its entries in the journal's order.

`Kernel.mail` is the plan for a wave of messages, each of which has one receiver. This plan is
for entries applied whole, each with every actor its messages reach, and is what
`examples/videos/Videos/Waves.lean` measures a workload with
(`docs/decisions/new-waves-premise.md`).
-/

@[expose] public section

namespace Lanes.WavePlan

variable {α κ : Type} [DecidableEq κ]

/-- The first wave free for every actor of `actors`, where actor `a` is free from wave `next a`. -/
def first (next : κ → Nat) (actors : List κ) : Nat :=
  actors.foldl (fun w a => max w (next a)) 0

/-- The wave of each entry, in order, where actor `a` is free from wave `next a`. -/
def levelsFrom (touches : α → List κ) : (κ → Nat) → List α → List Nat
  | _, [] => []
  | next, e :: es =>
    let w := first next (touches e)
    w :: levelsFrom touches (fun a => if a ∈ touches e then w + 1 else next a) es

/-- The wave of each entry of `batch`, in order, the first wave `0`. -/
def levels (touches : α → List κ) (batch : List α) : List Nat :=
  levelsFrom touches (fun _ => 0) batch

/-- The waves of `batch`: wave `w` holds the entries of level `w`, in the batch's order. -/
def split (touches : α → List κ) (batch : List α) : List (List α) :=
  let ls := levels touches batch
  let tagged := batch.zip ls
  if batch.isEmpty then []
  else (List.range (ls.foldl max 0 + 1)).map fun w => (tagged.filter (·.2 == w)).map (·.1)

omit [DecidableEq κ] in
theorem le_foldl_max (next : κ → Nat) (actors : List κ) (w : Nat) :
    w ≤ actors.foldl (fun w a => max w (next a)) w ∧
      ∀ a ∈ actors, next a ≤ actors.foldl (fun w a => max w (next a)) w := by
  induction actors generalizing w with
  | nil => simp
  | cons b bs ih =>
    obtain ⟨h₁, h₂⟩ := ih (max w (next b))
    refine ⟨by simp only [List.foldl_cons]; omega, fun a ha => ?_⟩
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp ha with rfl | ha
    · omega
    · exact h₂ a ha

omit [DecidableEq κ] in
theorem le_first (next : κ → Nat) {actors : List κ} {a : κ} (h : a ∈ actors) :
    next a ≤ first next actors :=
  (le_foldl_max next actors 0).2 a h

theorem length_levelsFrom (touches : α → List κ) (next : κ → Nat) (es : List α) :
    (levelsFrom touches next es).length = es.length := by
  induction es generalizing next with
  | nil => rfl
  | cons e es ih => simp [levelsFrom, ih]

/-- An entry's wave is at or after the first wave free for each actor it touches. -/
theorem next_le (touches : α → List κ) (es : List α) :
    ∀ (next : κ → Nat) (i : Nat) (e : α) (l : Nat), es[i]? = some e →
      (levelsFrom touches next es)[i]? = some l → ∀ a ∈ touches e, next a ≤ l := by
  induction es with
  | nil => simp
  | cons x es ih =>
    intro next i e l he hl a ha
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, levelsFrom] at he hl
      subst he hl
      exact le_first next ha
    | succ i =>
      simp only [List.getElem?_cons_succ, levelsFrom] at he hl
      have := ih _ i e l he hl a ha
      split at this
      · next hx => have := le_first next hx; omega
      · exact this

/-- Each actor's entries are in waves in the journal's order: of two entries that touch an
actor in common, the earlier is in an earlier wave. -/
theorem levels_lt (touches : α → List κ) (es : List α) :
    ∀ (next : κ → Nat) (i j : Nat) (e f : α) (li lj : Nat), i < j → es[i]? = some e →
      es[j]? = some f → (levelsFrom touches next es)[i]? = some li →
      (levelsFrom touches next es)[j]? = some lj → ∀ a ∈ touches e, a ∈ touches f → li < lj := by
  induction es with
  | nil => simp
  | cons x es ih =>
    intro next i j e f li lj hij he hf hli hlj a hae haf
    cases j with
    | zero => omega
    | succ j =>
      simp only [List.getElem?_cons_succ, levelsFrom] at hf hlj
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, levelsFrom] at he hli
        subst he hli
        have := next_le touches es _ j f lj hf hlj a haf
        simp only [hae, ite_true] at this
        omega
      | succ i =>
        simp only [List.getElem?_cons_succ, levelsFrom] at he hli
        exact ih _ i j e f li lj (by omega) he hf hli hlj a hae haf

/-- The entries of one wave touch no actor in common. -/
theorem disjoint_of_level (touches : α → List κ) (batch : List α) {i j : Nat} (hij : i ≠ j)
    {e f : α} {l : Nat} (he : batch[i]? = some e) (hf : batch[j]? = some f)
    (hli : (levels touches batch)[i]? = some l) (hlj : (levels touches batch)[j]? = some l) :
    ∀ a ∈ touches e, a ∉ touches f := by
  intro a hae haf
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · exact Nat.lt_irrefl l (levels_lt touches batch _ i j e f l l h he hf hli hlj a hae haf)
  · exact Nat.lt_irrefl l (levels_lt touches batch _ j i f e l l h hf he hlj hli a haf hae)

theorem pairwise_zip_levels (touches : α → List κ) (batch : List α) :
    (batch.zip (levels touches batch)).Pairwise fun p q =>
      p.2 = q.2 → ∀ a ∈ touches p.1, a ∉ touches q.1 := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij heq
  have hlen := length_levelsFrom touches (fun _ => 0) batch
  simp only [List.length_zip] at hi hj
  simp only [List.getElem_zip] at heq ⊢
  exact disjoint_of_level touches batch (Nat.ne_of_lt hij)
    (List.getElem?_eq_getElem (by omega)) (List.getElem?_eq_getElem (by omega))
    (List.getElem?_eq_getElem (by unfold levels; omega))
    (by rw [heq]; exact List.getElem?_eq_getElem (by unfold levels; omega))

/-- The entries of each wave of `split` touch no actor in common. -/
theorem disjoint_of_split (touches : α → List κ) (batch : List α) :
    ∀ wave ∈ split touches batch, wave.Pairwise fun e f => ∀ a ∈ touches e, a ∉ touches f := by
  intro wave hw
  simp only [split] at hw
  split at hw
  · simp at hw
  · obtain ⟨w, -, rfl⟩ := List.mem_map.mp hw
    rw [List.pairwise_map, List.pairwise_filter]
    exact (pairwise_zip_levels touches batch).imp fun h hp hq =>
      h (by simp only [beq_iff_eq] at hp hq; rw [hp, hq])

end Lanes.WavePlan
