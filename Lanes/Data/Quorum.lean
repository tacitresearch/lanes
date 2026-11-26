/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std

/-!
Majority quorums. The one fact protocols need from them is that two majorities of the same
nodes share a node (`Quorum.majority_inter`).
-/

@[expose] public section

namespace Lanes.Quorum

variable {α : Type} [DecidableEq α]

/-- Whether more than half of `nodes` are in `votes`. Repeated votes count once. -/
def isMajority (nodes votes : List α) : Bool :=
  2 * nodes.countP (· ∈ votes) > nodes.length

omit [DecidableEq α] in
private theorem countP_add_countP_le (nodes : List α) (p q : α → Bool)
    (h : ∀ x ∈ nodes, ¬(p x = true ∧ q x = true)) :
    nodes.countP p + nodes.countP q ≤ nodes.length := by
  induction nodes with
  | nil => simp
  | cons x nodes ih =>
    have := ih fun y hy => h y (List.mem_cons_of_mem x hy)
    have hx := h x List.mem_cons_self
    simp only [List.countP_cons, List.length_cons]
    cases hp : p x <;> cases hq : q x <;> simp_all <;> omega

theorem majority_inter {nodes a b : List α} (ha : isMajority nodes a = true)
    (hb : isMajority nodes b = true) : ∃ x, x ∈ a ∧ x ∈ b := by
  apply Classical.byContradiction
  intro hnone
  have := countP_add_countP_le nodes (· ∈ a) (· ∈ b) fun x _ hx =>
    hnone ⟨x, by simpa using hx.1, by simpa using hx.2⟩
  simp only [isMajority, decide_eq_true_eq] at ha hb
  omega

end Lanes.Quorum
