import Mathlib.Data.List.Infix

/-!
Raft's log reasoning (`examples/raft-kv/RaftKV/Proofs/Log.lean`, section `Matching`) again, with
Mathlib's prefix lemmas or core's `grind`. `termAt`, `merge` and `Matching` are copied from
`examples/raft-kv/RaftKV/Protocol.lean` and `Log.lean` with entries reduced to their term, which
is all these proofs look at. Run with `lake env lean experiments/LibraryProofs/RaftLog.lean`.
-/

namespace Experiment

structure Entry where
  term : Nat

def termAt (log : List Entry) (index : Nat) : Nat :=
  if index = 0 then 0 else (log[index - 1]?.map (·.term)).getD 0

def merge : (own sent : List Entry) → List Entry
  | e :: own, n :: sent => if e.term = n.term then e :: merge own sent else n :: sent
  | [], sent => sent
  | own, [] => own

def Matching (a b : List Entry) : Prop :=
  ∀ k, k ≤ a.length → k ≤ b.length → termAt a k = termAt b k → a.take k = b.take k

/-- `termAt_cons_succ`, `termAt_drop`, `termAt_append_left`: 2, 2 and 4 lines in Raft. -/
theorem termAt_cons_succ (entry : Entry) (log : List Entry) {k : Nat} (hk : 0 < k) :
    termAt (entry :: log) (k + 1) = termAt log k := by
  grind [termAt]

theorem termAt_drop (log : List Entry) (prev : Nat) {k : Nat} (hk : 0 < k) :
    termAt (log.drop prev) k = termAt log (prev + k) := by
  grind [termAt]

theorem termAt_append_left (a b : List Entry) {k : Nat} (hk : k ≤ a.length) :
    termAt (a ++ b) k = termAt a k := by
  grind [termAt]

theorem termAt_of_prefix {a b : List Entry} (h : a <+: b) {k : Nat} (hk : k ≤ a.length) :
    termAt a k = termAt b k := by
  obtain ⟨rest, rfl⟩ := h
  exact (termAt_append_left a rest hk).symm

/-- `Matching.drop`: 8 lines in Raft, the same here; neither library has more to give. -/
theorem Matching.drop {a b : List Entry} (h : Matching a b) (prev : Nat) :
    Matching (a.drop prev) (b.drop prev) := by
  intro k hka hkb hterm
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · simp only [List.length_drop] at hka hkb
    rw [termAt_drop _ _ hk, termAt_drop _ _ hk] at hterm
    have := congrArg (List.drop prev) (h (prev + k) (by omega) (by omega) hterm)
    simpa [List.drop_take] using this

/-- `merge_of_prefix`: 5 lines in Raft, the same here. -/
theorem merge_of_prefix {own sent : List Entry} (h : sent <+: own) : merge own sent = own := by
  fun_induction merge own sent with
  | case1 e own n sent hterm ih => rw [ih (List.cons_prefix_cons.mp h).2]
  | case2 e own n sent hterm => exact absurd (by rw [(List.cons_prefix_cons.mp h).1]) hterm
  | case3 sent => exact List.prefix_nil.mp h
  | case4 own => rfl

end Experiment
