import Lanes.Semantics.Projection

/-!
`System.Run.ofBlocks` (`Lanes/Semantics/Projection.lean`) again, from CSLib's
`LTS.OmegaExecution.flatten_mTr` and `ωSequence.flatten` in place of the hand-built `blockStart`,
`blockOf` and the step proof of `ofBlocks`. The four facts the rest of `Projection.lean` uses
(`ofBlocks_state`, `ofBlocks_event`, `ofBlocks_start`, `ofBlocks_take`) are proved again, with
`cumLen` in place of `blockStart` (`cumLen_eq_blockStart` shows they are the same).
Run with `lake env lean experiments/LibraryProofs/Blocks.lean`.
-/

namespace Experiment

open Lanes Cslib ωSequence

variable {σ : Signature} {sys : System σ} {env : EnvModel σ}

/-- The `k`-th block: its events, then one stutter. Never empty. -/
def block (B : ℕ → List (Event σ)) : ωSequence (List (Option (Event σ))) :=
  fun k => (B k).map some ++ [none]

theorem block_apply (B : ℕ → List (Event σ)) (k : ℕ) : block B k = (B k).map some ++ [none] :=
  rfl

theorem block_pos (B : ℕ → List (Event σ)) (k : ℕ) : 0 < (block B k).length := by
  simp [block_apply]

theorem cumLen_eq_blockStart (B : ℕ → List (Event σ)) (k : ℕ) :
    (block B).cumLen k = System.Run.blockStart B k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [cumLen_succ, ih, block_apply]; simp [System.Run.blockStart]; omega

/-- A finite run of the system is a finite run of its stuttering spec, stutter included. -/
theorem mTr_block {B : ℕ → List (Event σ)} {c c' : SysState sys} {k : ℕ}
    (h : c.run env (B k) = some c') : (sys.sem env).stutter.MTr c (block B k) c' := by
  rw [block_apply]
  generalize B k = evs at h
  induction evs generalizing c with
  | nil =>
    simp only [SysState.run, Option.some.injEq] at h
    subst h
    exact LTS.MTr.single _ (show (sys.sem env).stutter.Tr c none c from rfl)
  | cons ev evs ih =>
    cases hs : c.step env ev with
    | none => simp [SysState.run, hs] at h
    | some d =>
      exact .stepL (show (sys.sem env).stutter.Tr c (some ev) d from hs)
        (ih (by simpa [SysState.run, hs] using h))

variable (D : ℕ → SysState sys) (B : ℕ → List (Event σ)) (h0 : D 0 = SysState.init sys env)
  (hrun : ∀ k, (D k).run env (B k) = some (D (k + 1)))

include hrun in
theorem exists_run : ∃ ss, (sys.sem env).stutter.OmegaExecution ss (block B).flatten ∧
    ∀ k, ss ((block B).cumLen k) = D k :=
  LTS.OmegaExecution.flatten_mTr (ts := ⟨D⟩) (fun k => mTr_block (hrun k)) (block_pos B)

/-- The run that takes the finite runs `B` one after the other, and stutters after each. -/
noncomputable def ofBlocks : sys.Run env where
  state := (exists_run D B hrun).choose
  event := (block B).flatten
  init := by simpa [h0] using (exists_run D B hrun).choose_spec.2 0
  exec := (exists_run D B hrun).choose_spec.1

theorem ofBlocks_start (k : ℕ) : (ofBlocks D B h0 hrun).state ((block B).cumLen k) = D k :=
  (exists_run D B hrun).choose_spec.2 k

theorem ofBlocks_event {k j : ℕ} (hj : j ≤ (B k).length) :
    (ofBlocks D B h0 hrun).event ((block B).cumLen k + j) = (B k)[j]? := by
  have := flatten_get_add (block B) (n := k) (k := j) (by simp [block_apply]; omega) (block_pos B)
  simp only [ofBlocks, this, block_apply]
  rcases Nat.lt_or_ge j (B k).length with h | h
  · simp [h]
  · obtain rfl : j = (B k).length := by omega
    simp

theorem ofBlocks_take (k : ℕ) :
    (ofBlocks D B h0 hrun).event.take ((block B).cumLen (k + 1))
      = (ofBlocks D B h0 hrun).event.take ((block B).cumLen k) ++ ((B k).map some ++ [none]) := by
  simp only [ofBlocks, ← flatten_take (block_pos B), take_succ', List.flatten_append,
    List.flatten_singleton]
  rfl

theorem ofBlocks_state {k j : ℕ} (hj : j ≤ (B k).length) :
    (D k).run env ((B k).take j) = some ((ofBlocks D B h0 hrun).state ((block B).cumLen k + j)) := by
  induction j with
  | zero => simp [SysState.run, ofBlocks_start]
  | succ j ih =>
    have hlt : j < (B k).length := by omega
    have hstep := System.Run.step_some (r := ofBlocks D B h0 hrun) (n := (block B).cumLen k + j)
      (ev := (B k)[j]) (by rw [ofBlocks_event D B h0 hrun hlt.le, List.getElem?_eq_getElem hlt])
    rw [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some, SysState.run_append,
      ih hlt.le]
    simp [SysState.run, hstep, Nat.add_assoc]

end Experiment
