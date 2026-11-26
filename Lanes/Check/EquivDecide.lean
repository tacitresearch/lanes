/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Actors.Inspect
public import Lanes.Actors.Equiv

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

theorem NetEquiv.nil_iff {env : EnvModel σ} {b : List (Envelope σ)} :
    NetEquiv env [] b ↔ b = [] := by
  refine ⟨fun h => ?_, fun h => h ▸ .refl env []⟩
  cases b with
  | nil => rfl
  | cons x b => simpa [onLink] using h.perm x.src x.dst

theorem NetEquiv.cons {env : EnvModel σ} {a b : List (Envelope σ)} (h : NetEquiv env a b)
    (e : Envelope σ) : NetEquiv env (e :: a) (e :: b) := by
  refine ⟨fun src dst => ?_, fun src dst ho => ?_⟩
  · by_cases hon : onLink src dst e = true
    · simpa [hon] using h.perm src dst
    · simpa [hon] using h.perm src dst
  · by_cases hon : onLink src dst e = true
    · simpa [hon] using h.ordered src dst ho
    · simpa [hon] using h.ordered src dst ho

/-- Whether `e` may be matched with a message of `b`: `SysState.netEquiv` takes it out next. -/
def Matches (env : EnvModel σ) (e : Envelope σ) (b : List (Envelope σ)) : Prop :=
  (if (env.link e.src e.dst).ordered then b.find? e.sameLink == some e else b.contains e) = true

theorem Matches.mem {env : EnvModel σ} {e : Envelope σ} {b : List (Envelope σ)}
    (h : Matches env e b) : e ∈ b := by
  unfold Matches at h
  split at h
  · exact List.mem_of_find?_eq_some (by simpa using h)
  · simpa using h

/-- Putting a matched message back in front gives the same traffic. -/
theorem Matches.netEquiv {env : EnvModel σ} {e : Envelope σ} {b : List (Envelope σ)}
    (h : Matches env e b) : NetEquiv env (e :: b.erase e) b := by
  have hmem := h.mem
  have hfilter : ∀ src dst, onLink src dst e = false →
      (e :: b.erase e).filter (onLink src dst) = b.filter (onLink src dst) := by
    intro src dst hon
    simp [hon, filter_erase_of_neg _ _ hon]
  refine ⟨fun src dst => ?_, fun src dst ho => ?_⟩
  · by_cases hon : onLink src dst e = true
    · simp only [List.filter_cons, hon, ↓reduceIte, filter_erase_of_pos _ _ hon]
      exact (List.perm_cons_erase (List.mem_filter.mpr ⟨hmem, hon⟩)).symm
    · rw [hfilter src dst (by simpa using hon)]
  · by_cases hon : onLink src dst e = true
    · have hlink := sameLink_eq_onLink hon
      simp only [onLink, Bool.and_eq_true, decide_eq_true_eq] at hon
      unfold Matches at h
      rw [hon.1, hon.2, ho, hlink] at h
      have hhead : (b.filter (onLink src dst)).head? = some e := by
        rw [List.head?_filter]
        simpa using h
      have hon' : onLink src dst e = true := by simp [onLink, hon.1, hon.2]
      simp only [List.filter_cons, hon', ↓reduceIte, filter_erase_of_pos _ _ hon']
      cases hl : b.filter (onLink src dst) with
      | nil => simp [hl] at hhead
      | cons x l =>
        obtain rfl : x = e := by simpa [hl] using hhead
        simp
    · rw [hfilter src dst (by simpa using hon)]

theorem NetEquiv.matches {env : EnvModel σ} {e : Envelope σ} {a b : List (Envelope σ)}
    (h : NetEquiv env (e :: a) b) : Matches env e b := by
  have hself : onLink e.src e.dst e = true := by simp [onLink]
  unfold Matches
  split
  · next ho =>
    have hhead := congrArg List.head? (h.ordered e.src e.dst ho)
    rw [List.filter_cons_of_pos hself, List.head?_cons, List.head?_filter] at hhead
    simp [sameLink_eq_onLink hself, ← hhead]
  · simpa using (h.mem_iff e).mp (by simp)

theorem netEquiv_iff (env : EnvModel σ) (a b : List (Envelope σ)) :
    SysState.netEquiv env a b = true ↔ NetEquiv env a b := by
  induction a generalizing b with
  | nil => simp [SysState.netEquiv, NetEquiv.nil_iff]
  | cons e a ih =>
    simp only [SysState.netEquiv, Bool.and_eq_true, ih]
    refine ⟨fun ⟨hmatch, hrest⟩ => (hrest.cons e).trans (Matches.netEquiv hmatch),
      fun h => ⟨h.matches, ?_⟩⟩
    simpa using h.erase e

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
