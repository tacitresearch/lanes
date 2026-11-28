/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Semantics.FairRuns

/-!
# Liveness up to the last restart

A process restart (`Event.restart`) loses every message in flight, every timer and every actor's
state, so "every request is eventually answered" does not hold where the process may restart:
the request is gone. What holds is the statement from any position after which the process does
not restart (`System.LeadsToUnlessRestart`).

`System.LeadsTo.unlessRestart` gives it for every leads-to proved where the process never
restarts. A run that does not restart after position `n` is, from `n` on, a run without restarts:
the state at `n` is reachable without restarts (`System.reachable_withoutRestarts`), so a run
without restarts reaches it (`Run.fairAfter`), and the run from `n` follows (`Run.splice`). Both
are fair together, since fairness only looks at what happens from some position on.

## Main definitions

- `System.LeadsToUnlessRestart`: in every fair run, a state satisfying `P` is followed by one
  satisfying `Q`, if the process does not restart in between or after.
- `System.Run.splice`: a run without restarts to a state, then a run from that state on.

## Main statements

- `System.LeadsTo.unlessRestart`: what leads to what without restarts, does so with restarts,
  from any position after which the process does not restart.
-/

@[expose] public section

namespace Lanes

variable {σ : Signature} {sys : System σ} {env : EnvModel σ}

namespace System

/-- `P` leads to `Q` unless the process restarts: in every fair run, at every position where `P`
holds and after which no restart is taken, `Q` holds at that position or a later one. -/
def LeadsToUnlessRestart (sys : System σ) (env : EnvModel σ) (P Q : SysState sys → Prop) :
    Prop :=
  ∀ r : sys.Run env, r.Fair → ∀ n, P (r.state n) → (∀ m, n ≤ m → r.event m ≠ some .restart) →
    ∃ m, n ≤ m ∧ Q (r.state m)

namespace Run

variable {r : sys.Run env} {n : Nat} {evs : List (Event σ)}

/-- The run without restarts that takes `evs` to the state of `r` at `n`, and then the steps of
`r` from `n` on. -/
def splice (r : sys.Run env) (n : Nat) (evs : List (Event σ))
    (hrun : (SysState.init sys env.withoutRestarts).run env.withoutRestarts evs = some (r.state n))
    (hno : ∀ m, n ≤ m → r.event m ≠ some .restart) : sys.Run env.withoutRestarts where
  state k := if k < evs.length then (Run.fairAfter sys env.withoutRestarts evs).state k
    else r.state (n + (k - evs.length))
  event k := if k < evs.length then (Run.fairAfter sys env.withoutRestarts evs).event k
    else r.event (n + (k - evs.length))
  init := by
    split
    · exact (Run.fairAfter sys env.withoutRestarts evs).init
    · next h =>
      obtain rfl : evs = [] := List.eq_nil_of_length_eq_zero (by omega)
      simpa [SysState.run] using hrun.symm
  exec k := by
    have hfa := (Run.fairAfter sys env.withoutRestarts evs).exec k
    by_cases hk : k + 1 < evs.length
    · simpa [hk, show k < evs.length by omega] using hfa
    · by_cases hk' : k < evs.length
      · rw [show k + 1 = evs.length by omega, Run.fairAfter_state hrun] at hfa
        simpa [hk, hk', show k + 1 - evs.length = 0 by omega] using hfa
      · simp only [hk, hk', ↓reduceIte]
        have hr := r.exec (n + (k - evs.length))
        rw [show n + (k + 1 - evs.length) = n + (k - evs.length) + 1 by omega]
        cases hev : r.event (n + (k - evs.length)) with
        | none => simpa [Spec.stutter, hev] using hr
        | some ev =>
          have hne : ev ≠ .restart := fun h => hno _ (by omega) (h ▸ hev)
          simp only [Spec.stutter, System.sem, hev] at hr ⊢
          rw [SysState.step_withoutRestarts hne]
          exact hr

variable {hrun : (SysState.init sys env.withoutRestarts).run env.withoutRestarts evs = some (r.state n)}
  {hno : ∀ m, n ≤ m → r.event m ≠ some .restart}

theorem splice_state {k : Nat} (hk : evs.length ≤ k) :
    (r.splice n evs hrun hno).state k = r.state (n + (k - evs.length)) := by
  simp [splice, show ¬k < evs.length by omega]

theorem splice_event {k : Nat} (hk : evs.length ≤ k) :
    (r.splice n evs hrun hno).event k = r.event (n + (k - evs.length)) := by
  simp [splice, show ¬k < evs.length by omega]

/-- The splice of a fair run is fair: from its junction on it is the run it splices. -/
theorem splice_fair (hfair : r.Fair) : (r.splice n evs hrun hno).Fair := by
  refine fair_iff.mpr fun ob k hdue => ?_
  have hpos (m : Nat) (hm : n + (k - evs.length) ≤ m) :
      (r.splice n evs hrun hno).state (evs.length + (m - n)) = r.state m ∧
        (r.splice n evs hrun hno).event (evs.length + (m - n)) = r.event m := by
    rw [splice_state (by omega), splice_event (by omega),
      show n + (evs.length + (m - n) - evs.length) = m by omega]
    exact ⟨rfl, rfl⟩
  obtain ⟨m, hm, hev⟩ := fair_iff.mp hfair ob (n + (k - evs.length)) fun m hm => by
    obtain ⟨hstate, hevent⟩ := hpos m hm
    obtain ⟨hd, hq⟩ := hdue (evs.length + (m - n)) (by omega)
    refine ⟨hstate ▸ hd, fun ⟨ev, hev, hrestarted⟩ => hq ⟨ev, ?_, ?_⟩⟩
    · rw [hevent]; exact hev
    · rw [hstate]; exact hrestarted
  exact ⟨evs.length + (m - n), by omega, (hpos m hm).2.trans hev⟩

end Run

/-- What leads to what where the process never restarts, does so where it may, from any position
after which it does not restart. -/
theorem LeadsTo.unlessRestart {P Q : SysState sys → Prop}
    (h : sys.LeadsTo env.withoutRestarts P Q) : sys.LeadsToUnlessRestart env P Q := by
  intro r hfair n hP hno
  obtain ⟨evs, hrun⟩ := (reachable_withoutRestarts.mpr (r.reachable n)).exists_run
  obtain ⟨m, hm, hQ⟩ := h (r.splice n evs hrun hno) (Run.splice_fair hfair) evs.length
    (by rw [Run.splice_state (Nat.le_refl _), Nat.sub_self, Nat.add_zero]; exact hP)
  exact ⟨n + (m - evs.length), by omega, by rwa [Run.splice_state hm] at hQ⟩

end System

end Lanes
