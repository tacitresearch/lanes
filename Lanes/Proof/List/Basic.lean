/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
Facts about lists that fit none of the other files of `Lanes/Proof/List/`.
-/

public section

namespace Lanes

variable {α β : Type}

theorem find?_congr {p q : α → Bool} {l : List α} (h : ∀ x ∈ l, p x = q x) :
    l.find? p = l.find? q := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.find?_cons, h x List.mem_cons_self]
    rw [ih fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem mapM_some {f : α → Option β} {g : α → β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = some (g x)) → l.mapM f = some (l.map g)
  | [], _ => rfl
  | x :: l, h => by
    rw [List.mapM_cons, h x List.mem_cons_self,
      mapM_some fun y hy => h y (List.mem_cons_of_mem _ hy)]
    rfl

theorem dropWhile_of_head_any {p : α → Bool} : ∀ {l : List α}, l.head?.any p = false →
    l.dropWhile p = l
  | [], _ => rfl
  | c :: l, h => List.dropWhile_cons_of_neg (by simpa using h)

theorem flatMap_singletons {γ : Type} (f : α → β) (g : β → γ) (l : List α) :
    (l.flatMap fun a => [f a]).flatMap (fun b => [g b]) = l.map fun a => g (f a) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, ih]

/-- Replacing one element changes a sum by the difference. -/
theorem sum_map_set (f : α → Int) {l : List α} {i : Nat} {a : α} (v : α) (h : l[i]? = some a) :
    ((l.set i v).map f).sum + f a = (l.map f).sum + f v := by
  induction l generalizing i with
  | nil => simp at h
  | cons x l ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp only [List.set_cons_zero, List.map_cons, List.sum_cons]
      omega
    | succ i =>
      simp only [List.getElem?_cons_succ] at h
      have := ih h
      simp only [List.set_cons_succ, List.map_cons, List.sum_cons]
      omega

theorem mapM_ok {ε : Type} {f : α → Except ε β} {g : α → β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = .ok (g x)) → l.mapM f = .ok (l.map g)
  | [], _ => rfl
  | x :: l, h => by
    rw [List.mapM_cons, h x List.mem_cons_self, mapM_ok fun y hy => h y (List.mem_cons_of_mem _ hy)]
    rfl

theorem forall_mem_intercalate {p : α → Prop} {sep : List α} (hsep : ∀ x ∈ sep, p x) :
    ∀ {ls : List (List α)}, (∀ l ∈ ls, ∀ x ∈ l, p x) → ∀ x ∈ sep.intercalate ls, p x
  | [], _, x, hx => by simp at hx
  | [l], h, x, hx => by simp only [List.intercalate_singleton] at hx; exact h l (by simp) x hx
  | l :: l' :: ls, h, x, hx => by
    rw [List.intercalate_cons_cons] at hx
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_append.mp hx with hx | hx
      · exact h l (by simp) x hx
      · exact hsep x hx
    · exact forall_mem_intercalate hsep (ls := l' :: ls) (fun y hy => h y (by simp_all)) x hx

theorem mapM_ok_mem {ε : Type} {f : α → Except ε β} :
    ∀ {l : List α} {r : List β}, l.mapM f = .ok r → ∀ x ∈ l, ∃ y, f x = .ok y
  | [], _, _, x, hx => by simp at hx
  | x :: l, r, h, y, hy => by
    rw [List.mapM_cons] at h
    cases hx : f x with
    | error e => simp [hx, bind, Except.bind] at h
    | ok v =>
      cases hl : l.mapM f with
      | error e => simp [hx, hl, bind, Except.bind] at h
      | ok vs =>
        rcases List.mem_cons.mp hy with rfl | hy
        · exact ⟨v, hx⟩
        · exact mapM_ok_mem hl y hy

theorem forall_mem_takeWhile {p : α → Bool} : ∀ {l : List α}, ∀ x ∈ l.takeWhile p, p x = true
  | [], x, hx => by simp at hx
  | y :: l, x, hx => by
    rw [List.takeWhile_cons] at hx
    split at hx
    · rcases List.mem_cons.mp hx with rfl | hx
      · assumption
      · exact forall_mem_takeWhile x hx
    · simp at hx

theorem dropWhile_head {p : α → Bool} : ∀ {l : List α} {x : α} {rest : List α},
    l.dropWhile p = x :: rest → p x = false
  | [], _, _, h => by simp at h
  | y :: l, x, rest, h => by
    rw [List.dropWhile_cons] at h
    split at h
    · exact dropWhile_head h
    · rename_i hy
      simp only [List.cons.injEq] at h
      rw [← h.1]
      simpa using hy

theorem takeWhile_getElem {p : α → Bool} : ∀ {l : List α} {i : Nat},
    i < (l.takeWhile p).length → (hl : i < l.length) → p l[i] = true
  | [], _, _, hl => by simp at hl
  | x :: l, i, hi, hl => by
    rw [List.takeWhile_cons] at hi
    split at hi
    · rename_i hx
      cases i with
      | zero => simpa using hx
      | succ i => exact takeWhile_getElem (l := l) (i := i) (by simpa using hi) (by simpa using hl)
    · simp at hi

theorem takeWhile_stop {p : α → Bool} : ∀ {l : List α}
    (hi : (l.takeWhile p).length < l.length), p (l[(l.takeWhile p).length]'hi) = false
  | [], hi => by simp at hi
  | x :: l, hi => by
    by_cases hx : p x
    · have hlen : ((x :: l).takeWhile p).length = (l.takeWhile p).length + 1 := by
        simp [hx]
      have := takeWhile_stop (p := p) (l := l) (by simp [hlen] at hi; omega)
      simp only [hlen, List.getElem_cons_succ]
      exact this
    · have hlen : ((x :: l).takeWhile p).length = 0 := by simp [hx]
      simp only [hlen, List.getElem_cons_zero]
      simpa using hx

theorem forall_of_takeWhile_length {p : α → Bool} : ∀ {l : List α},
    (l.takeWhile p).length = l.length → ∀ x ∈ l, p x = true
  | [], _, x, hx => by simp at hx
  | y :: l, h, x, hx => by
    by_cases hy : p y
    · simp only [List.takeWhile_cons, hy, ↓reduceIte, List.length_cons,
        Nat.add_right_cancel_iff] at h
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hy
      · exact forall_of_takeWhile_length h x hx
    · simp [hy] at h
theorem mem_intercalate {sep : List α} {ls : List (List α)} {x : α}
    (h : x ∈ sep.intercalate ls) : x ∈ sep ∨ ∃ l ∈ ls, x ∈ l := by
  match ls with
  | [] => cases h
  | [l] => exact .inr ⟨l, by simp, by simpa using h⟩
  | l :: l' :: rest =>
    rw [List.intercalate_cons_cons] at h
    simp only [List.mem_append] at h
    rcases h with (h | h) | h
    · exact .inr ⟨l, by simp, h⟩
    · exact .inl h
    · rcases mem_intercalate h with h | ⟨m, hm, hx⟩
      · exact .inl h
      · exact .inr ⟨m, List.mem_cons_of_mem _ hm, hx⟩

theorem mem_intercalate_of_two_le {sep : List α} {ls : List (List α)} {x : α} (hx : x ∈ sep)
    (h : 2 ≤ ls.length) : x ∈ sep.intercalate ls := by
  match ls, h with
  | l :: l' :: rest, _ => rw [List.intercalate_cons_cons]; simp [hx]

theorem takeWhile_beq_eq_replicate [BEq α] [LawfulBEq α] (a : α) (l : List α) :
    l.takeWhile (· == a) = List.replicate (l.takeWhile (· == a)).length a := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    by_cases h : x = a
    · subst h; simp only [List.takeWhile_cons, beq_self_eq_true, ite_true, List.length_cons,
        List.replicate_succ]
      exact congrArg _ ih
    · simp [h]

theorem takeWhile_append_of_forall {p : α → Bool} {l₁ l₂ : List α} (h : ∀ x ∈ l₁, p x = true) :
    (l₁ ++ l₂).takeWhile p = l₁ ++ l₂.takeWhile p := by
  induction l₁ with
  | nil => rfl
  | cons x l ih =>
    simp [h x (by simp), ih fun y hy => h y (by simp [hy])]

theorem dropWhile_append_of_forall {p : α → Bool} {l₁ l₂ : List α} (h : ∀ x ∈ l₁, p x = true) :
    (l₁ ++ l₂).dropWhile p = l₂.dropWhile p := by
  induction l₁ with
  | nil => rfl
  | cons x l ih =>
    simp [h x (by simp), ih fun y hy => h y (by simp [hy])]

theorem eq_of_mem_of_nodup_map {f : α → β} {l : List α} (h : (l.map f).Nodup) {x y : α}
    (hx : x ∈ l) (hy : y ∈ l) (hxy : f x = f y) : x = y := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at h
    simp only [List.mem_cons] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact hx.trans hy.symm
    · subst hx; exact absurd hxy.symm (h.1 y hy)
    · subst hy; exact absurd hxy (h.1 x hx)
    · exact ih h.2 hx hy

theorem getElem?_append_singleton {l : List α} {x y : α} {n : Nat}
    (h : (l ++ [x])[n]? = some y) : l[n]? = some y ∨ (n = l.length ∧ y = x) := by
  rw [List.getElem?_append] at h
  split at h
  · exact .inl h
  · next hn =>
    rw [List.getElem?_singleton] at h
    split at h
    · next h0 => exact .inr ⟨by omega, (Option.some.inj h).symm⟩
    · simp at h

theorem getElem?_append_of_map {l m : List α} {g : α → β} {n : Nat} {b : β}
    (h : (l[n]?).map g = some b) : (l ++ m)[n]? = l[n]? := by
  have : n < l.length := by
    cases hn : l[n]? with
    | none => simp [hn] at h
    | some _ => exact (List.getElem?_eq_some_iff.mp hn).1
  exact List.getElem?_append_left this

theorem map_insertIdx (f : α → β) (x : α) :
    ∀ (i : Nat) (l : List α), (l.insertIdx i x).map f = (l.map f).insertIdx i (f x)
  | 0, l => by simp [List.insertIdx_zero]
  | _ + 1, [] => rfl
  | i + 1, y :: l => by simp [List.insertIdx_succ_cons, map_insertIdx f x i l]

theorem filterMap_insertIdx {f : α → Option β} {x : α} (hx : f x = none) :
    ∀ (i : Nat) (l : List α), (l.insertIdx i x).filterMap f = l.filterMap f
  | 0, l => by simp [List.insertIdx_zero, hx]
  | _ + 1, [] => rfl
  | i + 1, y :: l => by
    simp only [List.insertIdx_succ_cons, List.filterMap_cons, filterMap_insertIdx hx i l]

theorem idxOf?_getElem [BEq α] [LawfulBEq α] {l : List α} (h : l.Nodup) {i : Nat}
    (hi : i < l.length) : l.idxOf? l[i] = some i :=
  List.idxOf?_eq_some_iff.mpr ⟨hi, rfl, fun j hj e => by
    have := (h.getElem_inj (hi := by omega) (hj := hi)).mp e
    omega⟩

theorem filterMap_eq_range {f : α → Option Nat} {l : List α}
    (h : ∀ j (hj : j < l.length), f l[j] = some j) : l.filterMap f = List.range l.length := by
  have hm : l.map f = (List.range l.length).map some := by
    apply List.ext_getElem (by simp)
    intro j h1 _
    simp only [List.getElem_map, List.getElem_range]
    exact h j (by simpa using h1)
  simpa [List.filterMap_map] using congrArg (List.filterMap id) hm

end Lanes
