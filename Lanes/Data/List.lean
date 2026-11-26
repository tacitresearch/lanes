/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
Facts about lists that proofs about systems share: what `erase` does under `map`, `filter`,
`filterMap` and `countP`. Messages in flight, timers and outputs waiting are lists, and an event
takes one element out, so every proof that reads a state through a map or a filter needs these.
Then `take` and `drop` of a log and of a start of it. Then strings and byte arrays as lists of
bytes: what UTF-8 makes of a character below 128, and the bytes of a byte array cut short or put
after another, through which the proofs about the HTTP reader read what it reads. And a log read by a monitor that may reject it (`foldlM` into `Option`).
-/

public section

namespace Lanes

variable {α β : Type}

theorem filter_erase_of_pos [DecidableEq α] (p : α → Bool) (l : List α) {a : α}
    (_ : p a = true) : (l.erase a).filter p = (l.filter p).erase a :=
  List.erase_filter.symm

theorem filter_erase_of_neg [DecidableEq α] (p : α → Bool) (l : List α) {a : α}
    (h : p a = false) : (l.erase a).filter p = l.filter p := by
  rw [← List.erase_filter, List.erase_of_not_mem]
  simp [h]

/-- `f` need only tell `a` from the other elements of `l`. -/
theorem map_erase [DecidableEq α] [DecidableEq β] {f : α → β} {l : List α} {a : α}
    (inj : ∀ x ∈ l, f x = f a → x = a) : (l.erase a).map f = (l.map f).erase (f a) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    have ih := ih fun y hy => inj y (List.mem_cons_of_mem _ hy)
    by_cases hx : x = a
    · subst hx
      simp
    · have hfx : f x ≠ f a := fun h => hx (inj x List.mem_cons_self h)
      simp [hx, hfx, ih]

theorem filterMap_erase [DecidableEq α] [DecidableEq β] {f : α → Option β} {a : α} {b : β}
    (h : ∀ x, f x = some b ↔ x = a) (l : List α) :
    (l.erase a).filterMap f = (l.filterMap f).erase b := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    by_cases hx : x = a
    · subst hx
      simp [(h x).mpr rfl]
    · cases hfx : f x with
      | none => simp [hx, hfx, ih]
      | some y =>
        have hy : y ≠ b := fun hyb => hx ((h x).mp (hyb ▸ hfx))
        simp [hx, hfx, ih, hy]

theorem filterMap_erase_of_none [DecidableEq α] {f : α → Option β} {a : α} (h : f a = none)
    (l : List α) : (l.erase a).filterMap f = l.filterMap f := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    by_cases hx : x = a
    · subst hx
      simp [h]
    · cases hfx : f x <;> simp [hx, hfx, ih]

theorem filterMap_erase_perm [DecidableEq α] [DecidableEq β] {f : α → Option β} {l : List α}
    {a : α} {b : β} (ha : a ∈ l) (hb : f a = some b) :
    ((l.filterMap f).erase b).Perm ((l.erase a).filterMap f) := by
  have h := ((List.perm_cons_erase ha).filterMap f).erase b
  rwa [List.filterMap_cons_some hb, List.erase_cons_head] at h

theorem filterMap_perm_erase [DecidableEq α] {f : α → Option β} {l : List α} {a : α}
    (ha : a ∈ l) : (l.filterMap f).Perm ((f a).toList ++ (l.erase a).filterMap f) := by
  have h := (List.perm_cons_erase ha).filterMap f
  cases hfa : f a <;> simp_all

/-- Erasing `b` from what `f` shows of `l` is erasing from `l` the first element shown as `b`. -/
theorem exists_filterMap_erase [DecidableEq α] [DecidableEq β] {f : α → Option β} {b : β} :
    ∀ l : List α, b ∈ l.filterMap f →
      ∃ a ∈ l, f a = some b ∧ (l.erase a).filterMap f = (l.filterMap f).erase b := by
  intro l
  induction l with
  | nil => exact fun h => absurd h (by simp)
  | cons x l ih =>
    intro h
    cases hfx : f x with
    | none =>
      rw [List.filterMap_cons_none hfx] at h
      obtain ⟨a, ha, hfa, heq⟩ := ih h
      have hx : x ≠ a := fun hxa => by simp [hxa, hfa] at hfx
      exact ⟨a, List.mem_cons_of_mem _ ha, hfa, by simp [hx, hfx, heq]⟩
    | some y =>
      by_cases hy : y = b
      · subst hy
        exact ⟨x, List.mem_cons_self, hfx, by simp [hfx]⟩
      · rw [List.filterMap_cons_some hfx] at h
        obtain ⟨a, ha, hfa, heq⟩ := ih ((List.mem_cons.mp h).resolve_left fun hb => hy hb.symm)
        have hx : x ≠ a := fun hxa => hy (by simpa [hxa, hfa] using hfx.symm)
        exact ⟨a, List.mem_cons_of_mem _ ha, hfa, by simp [hx, hfx, heq, hy]⟩

theorem filterMap_cons_toList (f : α → Option β) (a : α) (l : List α) :
    (a :: l).filterMap f = (f a).toList ++ l.filterMap f := by
  cases h : f a <;> simp [h]

theorem filterMap_concat (f : α → Option β) (l : List α) (a : α) :
    (l ++ [a]).filterMap f = l.filterMap f ++ (f a).toList := by
  cases h : f a <;> simp [h]

theorem filterMap_filter_of_none {f : α → Option β} {p : α → Bool}
    (h : ∀ x, p x = false → f x = none) (l : List α) :
    (l.filter p).filterMap f = l.filterMap f := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    cases hp : p x with
    | true => cases hfx : f x <;> simp [hp, hfx, ih]
    | false => simp [hp, ih, h x hp]

theorem countP_erase_add [BEq α] [LawfulBEq α] (p : α → Bool) {l : List α} {a : α}
    (h : a ∈ l) : (l.erase a).countP p + (p a).toNat = l.countP p := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    by_cases hb : b = a
    · subst hb
      cases hp : p b <;> simp [hp]
    · have := ih (by simpa [Ne.symm hb] using h)
      simp only [List.erase_cons, beq_iff_eq, hb, ↓reduceIte, List.countP_cons]
      omega

theorem find?_congr {p q : α → Bool} {l : List α} (h : ∀ x ∈ l, p x = q x) :
    l.find? p = l.find? q := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.find?_cons, h x List.mem_cons_self]
    rw [ih fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem take_of_prefix {a b : List α} (h : a <+: b) {n : Nat} (hn : n ≤ a.length) :
    b.take n = a.take n := by
  obtain ⟨rest, rfl⟩ := h
  exact List.take_append_of_le_length hn

theorem drop_take_of_le (l : List α) {a b : Nat} (h : a ≤ b) : (l.take a).drop b = [] :=
  List.drop_eq_nil_of_le (by rw [List.length_take]; omega)

/-- A start of what follows `n` in `l` is what follows `n` in a start of `l`. -/
theorem drop_take_of_prefix {l part : List α} {n : Nat} (h : part <+: l.drop n) :
    (l.take (n + part.length)).drop n = part := by
  rw [List.drop_take, Nat.add_sub_cancel_left]
  exact (List.prefix_iff_eq_take.mp h).symm

theorem append_singleton_eq_append_cons {l before after : List α} {a b : α}
    (h : l ++ [a] = before ++ b :: after) :
    (before = l ∧ b = a ∧ after = []) ∨ ∃ rest, l = before ++ b :: rest ∧ after = rest ++ [a] := by
  rcases List.eq_nil_or_concat after with rfl | ⟨rest, c, rfl⟩
  · obtain ⟨hl, hab⟩ := List.append_inj' h rfl
    exact .inl ⟨hl.symm, (List.singleton_inj.mp hab).symm, rfl⟩
  · rw [List.concat_eq_append, ← List.cons_append, ← List.append_assoc] at h
    obtain ⟨hl, hac⟩ := List.append_inj' h rfl
    exact .inr ⟨rest, hl, by rw [List.concat_eq_append, List.singleton_inj.mp hac]⟩

theorem getElem?_of_prefix {a b : List α} (h : a <+: b) {k : Nat} {x : α}
    (hx : a[k]? = some x) : b[k]? = some x := by
  obtain ⟨rest, rfl⟩ := h
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hx).1]
  exact hx

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

theorem utf8EncodeChar_ascii {c : Char} {b : UInt8} (hb : b ∈ String.utf8EncodeChar c)
    (h : b.toNat < 128) : b.toNat = c.toNat := by
  simp only [String.utf8EncodeChar] at hb
  split at hb
  · simp only [List.mem_singleton] at hb
    subst hb
    rename_i hv
    rw [UInt8.toNat_ofNat']
    show _ = c.val.toNat
    omega
  · split at hb
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl <;> simp [UInt8.toNat_ofNat'] at h <;> omega
    · split at hb
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl | rfl <;> simp [UInt8.toNat_ofNat'] at h <;> omega
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl | rfl | rfl <;> simp [UInt8.toNat_ofNat'] at h <;> omega

theorem data_toList_toByteArray (s : String) :
    s.toByteArray.data.toList = s.toList.flatMap String.utf8EncodeChar := by
  rw [← String.utf8Encode_toList, List.utf8Encode_eq_toByteArray, List.data_toByteArray]

theorem fromUTF8?_toByteArray (s : String) : String.fromUTF8? s.toByteArray = some s := by
  simp [String.fromUTF8?, s.isValidUTF8, String.fromUTF8]

theorem length_flatMap_utf8EncodeChar (s : String) :
    (s.toList.flatMap String.utf8EncodeChar).length = s.utf8ByteSize := by
  rw [← data_toList_toByteArray, Array.length_toList]
  rfl

theorem extract_append_front (a b rest : ByteArray) :
    (a ++ (b ++ rest)).extract a.size (a.size + b.size) = b := by
  have := ByteArray.extract_append_size_add (a := a) (b := b ++ rest) (i := 0) (j := b.size)
  rw [Nat.add_zero] at this
  rw [this]
  exact ByteArray.extract_append_eq_left rfl

theorem size_extract_zero (bytes : ByteArray) (n : Nat) :
    (bytes.extract 0 n).size = min n bytes.size := by
  simp [ByteArray.size_extract]

theorem getElem_extract_zero {bytes : ByteArray} {n i : Nat}
    (h : i < (bytes.extract 0 n).size) :
    (bytes.extract 0 n)[i] = bytes[i]'(by rw [size_extract_zero] at h; omega) := by
  simp [ByteArray.getElem_extract]

theorem getElem?_extract_zero (bytes : ByteArray) (n i : Nat) :
    (bytes.extract 0 n)[i]? = if i < n then bytes[i]? else none := by
  by_cases h : i < (bytes.extract 0 n).size
  · have h' := h
    rw [size_extract_zero] at h'
    rw [getElem?_pos (bytes.extract 0 n) i h, getElem_extract_zero h,
      getElem?_pos bytes i (show i < bytes.size by omega)]
    simp only [show i < n by omega, ↓reduceIte]
  · rw [size_extract_zero] at h
    rw [getElem?_neg _ _ (by rw [size_extract_zero]; omega)]
    by_cases hn : i < n
    · simp only [hn, ↓reduceIte]
      rw [getElem?_neg _ _ (by omega)]
    · simp [hn]

theorem toList_extract_zero (bytes : ByteArray) (n : Nat) :
    (bytes.extract 0 n).data.toList = bytes.data.toList.take n := by
  simp [ByteArray.data_extract, Array.toList_extract, List.extract]

theorem extract_extract_zero {bytes : ByteArray} {n i j : Nat} (h : j ≤ n) :
    (bytes.extract 0 n).extract i j = bytes.extract i j := by
  rw [ByteArray.extract_extract, Nat.zero_add, Nat.zero_add, Nat.min_eq_left h]

theorem getElem?_data (b : ByteArray) (i : Nat) : b[i]? = b.data.toList[i]? := by
  by_cases h : i < b.size
  · rw [getElem?_pos b i h, Array.getElem?_toList, getElem?_pos b.data i h,
      ByteArray.getElem_eq_getElem_data]
  · rw [getElem?_neg b i h, Array.getElem?_toList, getElem?_neg b.data i h]

theorem getElem?_append_front (pre bytes : ByteArray) (i : Nat) :
    (pre ++ bytes)[pre.size + i]? = bytes.data.toList[i]? := by
  rw [getElem?_data, ByteArray.data_append, Array.toList_append,
    List.getElem?_append_right (by simp)]
  congr 1
  simp only [Array.length_toList]
  have : pre.data.size = pre.size := rfl
  omega

theorem getElem_of_getElem? {bytes : ByteArray} {q : Nat} {b : UInt8}
    (h : bytes[q]? = some b) : ∃ hq : q < bytes.size, bytes[q] = b := by
  by_cases hq : q < bytes.size
  · rw [getElem?_pos bytes q hq] at h
    exact ⟨hq, Option.some.inj h⟩
  · rw [getElem?_neg bytes q hq] at h
    cases h

theorem foldl_append_bytes (acc : ByteArray) (cs : List ByteArray) :
    cs.foldl (· ++ ·) acc = acc ++ cs.foldl (· ++ ·) .empty := by
  induction cs generalizing acc with
  | nil => simp
  | cons c cs ih =>
    rw [List.foldl_cons, List.foldl_cons, ih, ih (.empty ++ c), ByteArray.empty_append,
      ByteArray.append_assoc]

theorem foldlM_append_some {M : Type} {f : M → α → Option M} {l₁ l₂ : List α} {m t : M}
    (h : (l₁ ++ l₂).foldlM f m = some t) :
    ∃ m', l₁.foldlM f m = some m' ∧ l₂.foldlM f m' = some t := by
  rw [List.foldlM_append] at h
  cases h₁ : l₁.foldlM f m with
  | none => simp [h₁] at h
  | some m' => exact ⟨m', rfl, by simpa [h₁] using h⟩

theorem foldlM_cons_some {M : Type} {f : M → α → Option M} {x : α} {l : List α} {m t : M}
    (h : (x :: l).foldlM f m = some t) : ∃ m', f m x = some m' ∧ l.foldlM f m' = some t := by
  simp only [List.foldlM_cons] at h
  cases h₁ : f m x with
  | none => simp [h₁] at h
  | some m' => exact ⟨m', rfl, by simpa [h₁] using h⟩

/-- What each accepted element keeps, a whole accepted list keeps. -/
theorem foldlM_some_inv {M : Type} {f : M → α → Option M} {l : List α} {m t : M} (P : M → Prop)
    (hstep : ∀ m x m', x ∈ l → P m → f m x = some m' → P m') (hm : P m)
    (h : l.foldlM f m = some t) : P t := by
  induction l generalizing m with
  | nil => simp only [List.foldlM_nil] at h; exact Option.some.inj h ▸ hm
  | cons x l ih =>
    obtain ⟨m', hx, hl⟩ := foldlM_cons_some h
    exact ih (fun m y m'' hy => hstep m y m'' (List.mem_cons_of_mem _ hy))
      (hstep m x m' List.mem_cons_self hm hx) hl

/-- What follows the first `a` in `l`, if `a` is in it. -/
@[expose] def afterFirst [DecidableEq α] (a : α) : List α → Option (List α)
  | [] => none
  | x :: xs => if x = a then some xs else afterFirst a xs

theorem eq_of_afterFirst [DecidableEq α] {a : α} {l rest : List α}
    (h : afterFirst a l = some rest) : ∃ skipped, l = skipped ++ a :: rest := by
  induction l with
  | nil => simp [afterFirst] at h
  | cons x xs ih =>
    simp only [afterFirst] at h
    split at h
    · next hx => exact ⟨[], by simp [hx, Option.some.inj h]⟩
    · obtain ⟨skipped, rfl⟩ := ih h
      exact ⟨x :: skipped, rfl⟩

/-- Taking the first `a` out of a list that `a :: l` is a sublist of leaves one that `l` is a
sublist of. -/
theorem afterFirst_of_cons_sublist [DecidableEq α] {a : α} {l p : List α} (h : (a :: l).Sublist p) :
    ∃ rest, afterFirst a p = some rest ∧ l.Sublist rest := by
  induction p with
  | nil => simp at h
  | cons x xs ih =>
    simp only [afterFirst]
    split
    · next hx =>
      subst hx
      exact ⟨xs, rfl, (List.cons_sublist_cons.mp h)⟩
    · next hx =>
      rcases h with _ | ⟨_, h⟩ | ⟨_, h⟩
      · exact ih ‹_›
      · exact absurd rfl hx

/-- `List.mem_of_mem_erase` for the `BEq` that a `DecidableEq` gives, which is not the one
instance search finds for a sum or a product. -/
theorem mem_of_mem_erase [DecidableEq α] {l : List α} {a x : α} (h : x ∈ l.erase a) : x ∈ l :=
  List.mem_of_mem_erase h

theorem flatMap_singletons {γ : Type} (f : α → β) (g : β → γ) (l : List α) :
    (l.flatMap fun a => [f a]).flatMap (fun b => [g b]) = l.map fun a => g (f a) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, ih]

end Lanes
