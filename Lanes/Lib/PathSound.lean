/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Lib.Path

/-!
What `Lanes.Path` is proved to do: `clean` is idempotent (`Path.clean_clean`), and what `under`
returns is the cleaned root followed by names, none of them `.`, `..` or empty, none holding `/`
or NUL (`Path.under_names`).
-/

@[expose] public section

namespace Lanes.Path

/-- `..` -/
abbrev dd : List Char := ['.', '.']

/-- What `names` keeps but `..`. -/
def Good (n : List Char) : Prop := n ≠ [] ∧ n ≠ ['.'] ∧ n ≠ dd ∧ '/' ∉ n

/-- Names as `names` leaves them: some `..` (none in a rooted path), then good names. -/
def Normal (rooted : Bool) (ns : List (List Char)) : Prop :=
  ∃ k gs, ns = List.replicate k dd ++ gs ∧ (rooted = true → k = 0) ∧ ∀ g ∈ gs, Good g

theorem mem_splitOn {p : List Char} : ∀ {s}, s ∈ p.splitOn '/' → ∀ c ∈ s, c ∈ p ∧ c ≠ '/' := by
  induction p with
  | nil => intro s hs c hc; simp [List.splitOn_nil] at hs; simp [hs] at hc
  | cons x xs ih =>
    intro s hs c hc
    rw [List.splitOn_cons_eq_ite_modifyHead] at hs
    split at hs
    · simp only [List.mem_cons] at hs
      rcases hs with rfl | hs
      · simp at hc
      · exact ⟨List.mem_cons_of_mem _ (ih hs c hc).1, (ih hs c hc).2⟩
    · rename_i hx
      have hne := List.splitOn_ne_nil '/' xs
      generalize e : xs.splitOn '/' = ls at hs ih hne
      cases ls with
      | nil => exact absurd rfl hne
      | cons h t =>
        simp only [List.modifyHead_cons, List.mem_cons] at hs
        rcases hs with rfl | hs
        · simp only [List.mem_cons] at hc
          rcases hc with rfl | hc
          · exact ⟨List.mem_cons_self, by simpa using hx⟩
          · exact ⟨List.mem_cons_of_mem _ (ih (by simp) c hc).1, (ih (by simp) c hc).2⟩
        · exact ⟨List.mem_cons_of_mem _ (ih (by simp [hs]) c hc).1, (ih (by simp [hs]) c hc).2⟩

/-- The names kept so far, last first: good names on top of some `..`. -/
def Kept (rooted : Bool) (acc : List (List Char)) : Prop :=
  ∃ k gs, acc = gs ++ List.replicate k dd ∧ (rooted = true → k = 0) ∧ ∀ g ∈ gs, Good g

theorem kept_push {rooted : Bool} {acc : List (List Char)} (h : Kept rooted acc) {seg : List Char}
    (hs : '/' ∉ seg) : Kept rooted (push rooted acc seg) := by
  obtain ⟨k, gs, rfl, hk, hg⟩ := h
  unfold push
  split
  · exact ⟨k, gs, rfl, hk, hg⟩
  · rename_i h1
    simp only [Bool.or_eq_true, List.isEmpty_iff, beq_iff_eq, not_or] at h1
    split
    · rename_i hd
      simp only [beq_iff_eq] at hd
      subst hd
      split
      · rename_i top rest e
        split
        · rename_i ht
          simp only [beq_iff_eq] at ht
          subst ht
          cases gs with
          | nil =>
            refine ⟨k + 1, [], ?_, ?_, by simp⟩
            · simp [List.replicate_succ]
            · intro hr; have := hk hr; subst this; simp at e
          | cons g gs' =>
            simp only [List.cons_append, List.cons.injEq] at e
            exact absurd e.1 (hg g (by simp)).2.2.1
        · rename_i ht
          cases gs with
          | nil =>
            cases k with
            | zero => simp at e
            | succ k =>
              simp only [List.nil_append, List.replicate_succ, List.cons.injEq] at e
              simp [← e.1] at ht
          | cons g gs' =>
            simp only [List.cons_append, List.cons.injEq] at e
            exact ⟨k, gs', e.2.symm, hk, fun g' hg' => hg g' (by simp [hg'])⟩
      · rename_i e
        split
        · exact ⟨0, [], by simp, by simp, by simp⟩
        · rename_i hr
          refine ⟨1, [], by simp, by simp [hr], by simp⟩
    · rename_i hd
      simp only [beq_iff_eq] at hd
      exact ⟨k, seg :: gs, rfl, hk, fun g hg' => by
        simp only [List.mem_cons] at hg'
        rcases hg' with rfl | hg'
        · exact ⟨h1.1, h1.2, hd, hs⟩
        · exact hg g hg'⟩

theorem names_normal (rooted : Bool) (p : List Char) : Normal rooted (names rooted p) := by
  have : ∀ (segs : List (List Char)) (acc : List (List Char)), (∀ s ∈ segs, '/' ∉ s) →
      Kept rooted acc → Kept rooted (segs.foldl (push rooted) acc) := by
    intro segs
    induction segs with
    | nil => intro acc _ h; exact h
    | cons s segs ih =>
      intro acc hs h
      exact ih _ (fun s' h' => hs s' (by simp [h'])) (kept_push h (hs s (by simp)))
  obtain ⟨k, gs, e, hk, hg⟩ := this (p.splitOn '/') [] (fun s hs h => (mem_splitOn hs '/' h).2 rfl)
    ⟨0, [], by simp, by simp, by simp⟩
  refine ⟨k, gs.reverse, ?_, hk, fun g h => hg g (by simpa using h)⟩
  simp [names, e]

theorem foldl_dots {rooted : Bool} : ∀ {j k : Nat}, (rooted = true → j + k = 0) →
    (List.replicate k dd).foldl (push rooted) (List.replicate j dd) = List.replicate (j + k) dd := by
  intro j k
  induction k generalizing j with
  | zero => intro; simp
  | succ k ih =>
    intro hr
    rw [List.replicate_succ, List.foldl_cons]
    have : push rooted (List.replicate j dd) dd = List.replicate (j + 1) dd := by
      cases j with
      | zero =>
        have : rooted = false := by cases rooted <;> simp_all
        simp [push, this]
      | succ j => simp [push, List.replicate_succ]
    rw [this, ih (fun h => by have := hr h; omega)]
    congr 1
    omega

theorem foldl_good {rooted : Bool} : ∀ {gs : List (List Char)}, (∀ g ∈ gs, Good g) →
    ∀ acc, gs.foldl (push rooted) acc = gs.reverse ++ acc := by
  intro gs
  induction gs with
  | nil => intros; simp
  | cons g gs ih =>
    intro hg acc
    have ⟨h1, h2, h3, _⟩ := hg g (by simp)
    have : push rooted acc g = g :: acc := by simp [push, h1, h2, h3]
    rw [List.foldl_cons, this, ih (fun g' h' => hg g' (by simp [h'])) _]
    simp

theorem foldl_normal {rooted : Bool} {ns : List (List Char)} (h : Normal rooted ns) :
    ns.foldl (push rooted) [] = ns.reverse := by
  obtain ⟨k, gs, rfl, hk, hg⟩ := h
  rw [List.foldl_append, show ([] : List (List Char)) = List.replicate 0 dd from rfl,
    foldl_dots (by simpa using hk), foldl_good hg]
  simp

theorem not_slash_of_normal {rooted : Bool} {ns : List (List Char)} (h : Normal rooted ns) :
    ∀ n ∈ ns, '/' ∉ n := by
  obtain ⟨k, gs, rfl, _, hg⟩ := h
  intro n hn
  simp only [List.mem_append, List.mem_replicate] at hn
  rcases hn with ⟨_, rfl⟩ | hn
  · decide
  · exact (hg n hn).2.2.2

theorem names_of_normal {rooted : Bool} {ns : List (List Char)} (h : Normal rooted ns)
    (hne : ns ≠ []) : names rooted (['/'].intercalate ns) = ns := by
  simp [names, List.splitOn_intercalate '/' (not_slash_of_normal h) hne, foldl_normal h]

theorem head_ne_slash {rooted : Bool} {ns : List (List Char)} (h : Normal rooted ns) (hne : ns ≠ []) :
    isRooted (['/'].intercalate ns) = false := by
  obtain ⟨k, gs, rfl, _, hg⟩ := h
  cases k with
  | succ k =>
    rw [List.replicate_succ, List.cons_append]
    cases List.replicate k dd ++ gs <;> simp [isRooted, List.intercalate_cons_cons]
  | zero =>
    cases gs with
    | nil => simp at hne
    | cons g gs =>
      have ⟨h1, _, _, h4⟩ := hg g (by simp)
      cases g with
      | nil => exact absurd rfl h1
      | cons c cs =>
        have : c ≠ '/' := fun e => h4 (by simp [e])
        cases gs <;> simp [isRooted, List.intercalate, this]

/-- `clean` is idempotent. -/
theorem cleanChars_cleanChars (p : List Char) : cleanChars (cleanChars p) = cleanChars p := by
  have hn := names_normal (isRooted p) p
  generalize e : names (isRooted p) p = ns at hn
  unfold cleanChars
  simp only [e]
  by_cases hr : isRooted p
  · simp only [hr, ite_true]
    have hr' : isRooted ('/' :: ['/'].intercalate ns) = true := by simp [isRooted]
    have : names true ('/' :: ['/'].intercalate ns) = ns := by
      rw [names, List.splitOn_cons_eq_ite_modifyHead]
      simp only [beq_self_eq_true, ite_true, List.foldl_cons]
      rw [show push true [] [] = [] by simp [push]]
      cases ns with
      | nil => simp [push]
      | cons n ns' =>
        rw [hr] at hn
        rw [List.splitOn_intercalate '/' (not_slash_of_normal hn) (by simp), foldl_normal hn]
        simp
    simp [hr', this]
  · simp only [hr, Bool.false_eq_true, ite_false]
    rw [Bool.not_eq_true] at hr
    rw [hr] at hn
    by_cases he : ns.isEmpty
    · simp only [he, ite_true]
      simp [isRooted, names, push, List.splitOn_cons_eq_ite_modifyHead, List.splitOn_nil]
    · have hne : ns ≠ [] := by simpa using he
      simp only [he, Bool.false_eq_true, ite_false, head_ne_slash hn hne, names_of_normal hn hne]

theorem clean_clean (p : String) : clean (clean p) = clean p := by
  simp [clean, cleanChars_cleanChars]

theorem mem_push {rooted : Bool} {acc : List (List Char)} {seg n : List Char}
    (h : n ∈ push rooted acc seg) : n = seg ∨ n ∈ acc := by
  unfold push at h
  repeat' split at h
  all_goals simp_all

theorem mem_names {rooted : Bool} {p n : List Char} (h : n ∈ names rooted p) :
    n ∈ p.splitOn '/' := by
  have : ∀ (segs acc : List (List Char)), n ∈ segs.foldl (push rooted) acc → n ∈ segs ∨ n ∈ acc := by
    intro segs
    induction segs with
    | nil => intro acc h; exact .inr h
    | cons s segs ih =>
      intro acc h
      rcases ih _ h with h | h
      · exact .inl (List.mem_cons_of_mem _ h)
      · rcases mem_push h with rfl | h
        · exact .inl List.mem_cons_self
        · exact .inr h
  simpa using this _ [] (by simpa [names] using h)

theorem isName_of_good {n : List Char} (h : Good n) (h0 : '\x00' ∉ n) : isName n := by
  have ⟨h1, h2, h3, h4⟩ := h
  simp [isName, h1, h2, h3, h4, h0]

/-- What `under` returns is the cleaned root followed by names. -/
theorem under_names {root rel p : String} (h : under root rel = some p) :
    ∃ ns : List (List Char), (∀ n ∈ ns, isName n) ∧ p = String.ofList (below root.toList ns) := by
  simp only [under, Option.map_eq_some_iff] at h
  obtain ⟨ns, hb, rfl⟩ := h
  simp only [namesBelow, Bool.or_eq_true, beq_iff_eq] at hb
  split at hb
  · cases hb
  · rename_i hc
    simp only [not_or] at hc
    simp only [Option.some.injEq] at hb
    subst hb
    refine ⟨_, fun n hn => ?_, rfl⟩
    obtain ⟨k, gs, e, _, hg⟩ := names_normal false rel.toList
    rw [e] at hn hc
    cases k with
    | succ k => simp [List.replicate_succ] at hc
    | zero =>
      simp only [List.replicate_zero, List.nil_append] at hn
      refine isName_of_good (hg n hn) fun h0 => ?_
      have hm : n ∈ names false rel.toList := by rw [e]; simpa using hn
      exact hc.2 (by simpa using (mem_splitOn (mem_names hm) _ h0).1)

end Lanes.Path
