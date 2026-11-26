/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Actors.Inspect
public import Lanes.Check.Equiv

/-!
The comparison the checker runs, `SysState.equiv`, decides the relation `SysState.Equiv` that
`Equiv.step` shows is safe to merge on.
-/

public section

namespace Lanes

variable {σ : Signature} {sys : System σ}

theorem sameLink_eq_onLink {e : Envelope σ} {src : Option σ.Id} {dst : σ.Id}
    (h : onLink src dst e = true) : e.sameLink = onLink src dst := by
  simp only [onLink, Bool.and_eq_true, decide_eq_true_eq] at h
  funext x
  simp only [Envelope.sameLink, onLink, h.1, h.2]
  congr 1 <;> exact decide_eq_decide.mpr eq_comm

theorem netEquiv_iff (env : EnvModel σ) (a b : List (Envelope σ)) :
    SysState.netEquiv env a b = true ↔ NetEquiv env a b := by
  simp only [SysState.netEquiv, Bool.and_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨ha, hb⟩
    have key : ∀ src dst,
        (if (env.link src dst).ordered then a.filter (onLink src dst) = b.filter (onLink src dst)
          else (a.filter (onLink src dst)).Perm (b.filter (onLink src dst))) := by
      intro src dst
      by_cases hex : ∃ e, (e ∈ a ∨ e ∈ b) ∧ onLink src dst e = true
      · obtain ⟨e, hmem, hon⟩ := hex
        have he := hmem.elim (ha e) (hb e)
        have hlink := sameLink_eq_onLink hon
        simp only [onLink, Bool.and_eq_true, decide_eq_true_eq] at hon
        rw [hlink, hon.1, hon.2] at he
        split at he
        · next ho => simpa [ho] using he
        · next ho => simpa [ho, List.isPerm_iff] using he
      · have hnil : ∀ l : List (Envelope σ), (∀ e ∈ l, e ∈ a ∨ e ∈ b) →
            l.filter (onLink src dst) = [] := by
          intro l hl
          rw [List.filter_eq_nil_iff]
          intro e he hon
          exact hex ⟨e, hl e he, hon⟩
        rw [hnil a (fun _ h => .inl h), hnil b (fun _ h => .inr h)]
        split <;> simp
    refine ⟨fun src dst => ?_, fun src dst ho => ?_⟩
    · have := key src dst
      split at this
      · rw [this]
      · exact this
    · simpa [ho] using key src dst
  · intro h
    have same : ∀ e : Envelope σ,
        (if (env.link e.src e.dst).ordered then a.filter e.sameLink == b.filter e.sameLink
          else (a.filter e.sameLink).isPerm (b.filter e.sameLink)) = true := by
      intro e
      have hlink : e.sameLink = onLink e.src e.dst := sameLink_eq_onLink (by simp [onLink])
      rw [hlink]
      split
      · next ho => simp [h.ordered e.src e.dst ho]
      · exact List.isPerm_iff.mpr (h.perm e.src e.dst)
    exact ⟨fun e _ => same e, fun e _ => same e⟩

/-- The checker's comparison is exactly the relation it is safe to merge on. It needs equality
of actor states to be real equality. -/
theorem SysState.equiv_iff [σ.Inspect] [sys.Inspect] [∀ i, LawfulBEq (sys.State i)]
    (env : EnvModel σ) (a b : SysState sys) : a.equiv env b = true ↔ SysState.Equiv env a b := by
  simp only [SysState.equiv, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, netEquiv_iff,
    List.isPerm_iff]
  constructor
  · rintro ⟨⟨hall, hnet⟩, hout⟩
    exact ⟨funext fun i => (hall i (Enum.complete i)).1.1,
      funext fun i => (hall i (Enum.complete i)).1.2,
      funext fun i => (hall i (Enum.complete i)).2, hnet, hout⟩
  · intro h
    exact ⟨⟨fun i _ => ⟨⟨congrFun h.state i, congrFun h.up i⟩, congrFun h.timers i⟩, h.net⟩,
      h.outbox⟩

end Lanes
