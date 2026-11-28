import Std

/-!
`Lanes.Quorum.majority_inter` again, with library lemmas in place of the induction of
`countP_add_countP_le` (`Lanes/Data/Quorum.lean`). Run with
`lake env lean experiments/LibraryProofs/Quorum.lean`.

Found: Lean core has what the hand-written induction proves, `List.length_eq_countP_add_countP`
and `List.countP_mono_left`. Mathlib adds `Finset.inter_nonempty_of_card_lt_card_add_card`, which
needs the nodes as a `Finset` (no repeats); Lanes counts a list, so core's two lemmas fit better.
-/

namespace Experiment

variable {α : Type} [DecidableEq α]

def isMajority (nodes votes : List α) : Bool :=
  2 * nodes.countP (· ∈ votes) > nodes.length

/-- The same statement as `Lanes.Quorum.majority_inter`: 7 lines of proof against 17 (the
private induction and its use). -/
theorem majority_inter {nodes a b : List α} (ha : isMajority nodes a = true)
    (hb : isMajority nodes b = true) : ∃ x, x ∈ a ∧ x ∈ b := by
  apply Classical.byContradiction
  intro hnone
  have hle : nodes.countP (· ∈ b) ≤ nodes.countP (fun x => decide ¬decide (x ∈ a) = true) :=
    List.countP_mono_left fun x _ hx => by
      simpa using fun h => hnone ⟨x, h, by simpa using hx⟩
  have := List.length_eq_countP_add_countP (fun x => decide (x ∈ a)) (l := nodes)
  simp only [isMajority, decide_eq_true_eq] at ha hb
  omega

end Experiment
