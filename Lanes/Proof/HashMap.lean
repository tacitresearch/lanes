/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std.Data.DHashMap
import all Std.Data.DHashMap.Basic
import all Std.Data.DHashMap.Internal.Defs
import all Std.Data.DHashMap.Internal.Model
import all Std.Data.DHashMap.Internal.AssocList.Basic

/-!
A hash map in which a key is written twice is the map in which it is written once, value for
value and not only key for key. The kernel takes an actor's state out of its table before the
step and puts the new one back, and this is why that is the kernel that writing it once gives.

Writes to two keys that are already there can be made in either order, and so can a write to one
and the removal of another: neither moves an entry. A wave writes an actor's state once its steps
are known, after other actors' cells were written, and this is why that is the kernel that
writing each state at its step gives.
-/

public section

namespace Lanes

open Std Std.DHashMap.Internal

variable {α : Type} {β : α → Type} [BEq α] [Hashable α] [LawfulBEq α]

omit [Hashable α] in
private theorem replace_replace (l : AssocList α β) (a : α) (b c : β a) :
    (l.replace a b).replace a c = l.replace a c := by
  induction l with
  | nil => rfl
  | cons k v l ih =>
    by_cases h : (k == a) = true
    · simp [AssocList.replace, h]
    · simp [AssocList.replace, h, ih]

omit [Hashable α] in
private theorem contains_replace (l : AssocList α β) (a : α) (b : β a) :
    (l.replace a b).contains a = l.contains a := by
  induction l with
  | nil => rfl
  | cons k v l ih =>
    by_cases h : (k == a) = true
    · simp [AssocList.replace, AssocList.contains, h]
    · simp [AssocList.replace, AssocList.contains, h]

omit [BEq α] [LawfulBEq α] in
private theorem updateBucket_updateBucket (bs : Array (AssocList α β)) (h : 0 < bs.size) (a : α)
    (f g : AssocList α β → AssocList α β) (h' : 0 < (updateBucket bs h a f).size) :
    updateBucket (updateBucket bs h a f) h' a g = updateBucket bs h a (g ∘ f) := by
  unfold updateBucket mkIdx
  simp

private theorem raw_insert_insert {m : Raw₀ α β} {a : α} (h : m.containsₘ a = true)
    (b c : β a) : (m.insert a b).insert a c = m.insert a c := by
  have hb : (m.replaceₘ a b).containsₘ a = true := by
    simp only [Raw₀.containsₘ, Raw₀.replaceₘ, bucket_updateBucket, contains_replace]
    exact h
  rw [Raw₀.insert_eq_insertₘ, Raw₀.insert_eq_insertₘ, Raw₀.insert_eq_insertₘ]
  simp only [Raw₀.insertₘ, h, hb, ite_true]
  apply Subtype.ext
  simp only [Raw₀.replaceₘ, updateBucket_updateBucket]
  have hf : ((fun l => AssocList.replace a c l) ∘ fun l => AssocList.replace a b l)
      = fun l => AssocList.replace a c l := funext fun l => replace_replace l a b c
  rw [hf]

theorem DHashMap.insert_insert_of_contains {m : DHashMap α β} {a : α} (h : m.contains a = true)
    (b c : β a) : (m.insert a b).insert a c = m.insert a c := by
  have h' : Raw₀.containsₘ ⟨m.1, m.2.size_buckets_pos⟩ a = true := by
    rw [← Raw₀.contains_eq_containsₘ]; exact h
  have := congrArg Subtype.val (raw_insert_insert h' b c)
  cases m
  unfold DHashMap.insert
  congr 1

private theorem set_set_comm {γ : Type} (bs : Array γ) (i j : Nat) (hi : i < bs.size) (hj : j < bs.size)
    (f g : γ → γ) (hfg : ∀ l, f (g l) = g (f l)) (h₁ : j < (bs.set i (f bs[i]) hi).size)
    (h₂ : i < (bs.set j (g bs[j]) hj).size) :
    (bs.set i (f bs[i]) hi).set j (g (bs.set i (f bs[i]) hi)[j]) h₁ =
      (bs.set j (g bs[j]) hj).set i (f (bs.set j (g bs[j]) hj)[i]) h₂ := by
  apply Array.ext
  · simp
  · intro k hk _
    simp only [Array.getElem_set]
    by_cases hik : i = k <;> by_cases hjk : j = k <;> by_cases hij : i = j <;> simp_all

omit [BEq α] [LawfulBEq α] in
private theorem updateBucket_comm (bs : Array (AssocList α β)) (h : 0 < bs.size) (a b : α)
    (f g : AssocList α β → AssocList α β) (hfg : ∀ l, f (g l) = g (f l))
    (h₁ : 0 < (updateBucket bs h a f).size) (h₂ : 0 < (updateBucket bs h b g).size) :
    updateBucket (updateBucket bs h a f) h₁ b g = updateBucket (updateBucket bs h b g) h₂ a f := by
  unfold updateBucket mkIdx
  simp only [Array.uset, Array.size_set, Array.ugetElem_eq_getElem]
  exact set_set_comm _ _ _ _ _ _ _ hfg _ _

omit [Hashable α] in
private theorem contains_replace' (l : AssocList α β) (a c : α) (b : β a) :
    (l.replace a b).contains c = l.contains c := by
  induction l with
  | nil => rfl
  | cons k v l ih =>
    by_cases h : (k == a) = true
    · have := eq_of_beq h; subst this; simp [AssocList.replace, AssocList.contains]
    · simp [AssocList.replace, AssocList.contains, h]

omit [Hashable α] in
private theorem replace_comm (l : AssocList α β) {a b : α} (hab : a ≠ b) (x : β a) (y : β b) :
    (l.replace a x).replace b y = (l.replace b y).replace a x := by
  induction l with
  | nil => rfl
  | cons k v l ih =>
    by_cases ha : (k == a) = true
    · have := eq_of_beq ha; subst this
      have hb : (k == b) = false := by simpa using hab
      simp [AssocList.replace, hb]
    · by_cases hb : (k == b) = true
      · have := eq_of_beq hb; subst this
        have : (k == a) = false := by simpa using fun h => hab h.symm
        simp [AssocList.replace, this]
      · simp [AssocList.replace, ha, hb, ih]

omit [Hashable α] in
private theorem erase_replace_comm (l : AssocList α β) {a b : α} (hab : a ≠ b) (x : β a) :
    (l.replace a x).erase b = (l.erase b).replace a x := by
  induction l with
  | nil => rfl
  | cons k v l ih =>
    by_cases ha : (k == a) = true
    · have := eq_of_beq ha; subst this
      have hb : (k == b) = false := by simpa using hab
      simp [AssocList.replace, AssocList.erase, hb]
    · by_cases hb : (k == b) = true
      · have := eq_of_beq hb; subst this
        simp [AssocList.replace, AssocList.erase, ha]
      · simp [AssocList.replace, AssocList.erase, ha, hb, ih]

omit [Hashable α] in
private theorem erase_replace_self (l : AssocList α β) (a : α) (x : β a) :
    (l.replace a x).erase a = l.erase a := by
  induction l with
  | nil => rfl
  | cons k v l ih =>
    by_cases ha : (k == a) = true
    · simp [AssocList.replace, AssocList.erase, ha]
    · simp [AssocList.replace, AssocList.erase, ha, ih]

omit [BEq α] [LawfulBEq α] in
private theorem bucket_updateBucket' (bs : Array (AssocList α β)) (h : 0 < bs.size) (a c : α)
    (f : AssocList α β → AssocList α β) (h' : 0 < (updateBucket bs h a f).size) :
    bucket (updateBucket bs h a f) h' c = bucket bs h c ∨
      bucket (updateBucket bs h a f) h' c = f (bucket bs h c) := by
  unfold bucket updateBucket mkIdx
  simp only [Array.uset, Array.size_set, Array.ugetElem_eq_getElem, Array.getElem_set]
  split <;> simp_all

private theorem containsₘ_replaceₘ (m : Raw₀ α β) (a c : α) (b : β a) :
    (m.replaceₘ a b).containsₘ c = m.containsₘ c := by
  unfold Raw₀.containsₘ Raw₀.replaceₘ
  rcases bucket_updateBucket' m.1.buckets m.2 a c (fun l => l.replace a b) (by simpa using m.2)
    with h | h <;> simp only [h, contains_replace']

omit [Hashable α] in
private theorem contains_erase_ne (l : AssocList α β) {a b : α} (hab : a ≠ b) :
    (l.erase b).contains a = l.contains a := by
  induction l with
  | nil => rfl
  | cons k v l ih =>
    by_cases hb : (k == b) = true
    · have := eq_of_beq hb; subst this
      have : (k == a) = false := by simpa using fun h => hab h.symm
      simp [AssocList.erase, AssocList.contains, this]
    · have hb' : (k == b) = false := by simpa using hb
      simp only [AssocList.erase, hb', Bool.cond_false, AssocList.contains, ih]

private theorem containsₘ_eraseₘaux (m : Raw₀ α β) {a b : α} (hab : a ≠ b) :
    (m.eraseₘaux b).containsₘ a = m.containsₘ a := by
  unfold Raw₀.containsₘ Raw₀.eraseₘaux
  rcases bucket_updateBucket' m.1.buckets m.2 b a (fun l => l.erase b) (by simpa using m.2)
    with h | h <;> simp only [h, contains_erase_ne _ hab]

omit [LawfulBEq α] in
private theorem raw_insert_of_containsₘ {m : Raw₀ α β} {a : α} (h : m.containsₘ a = true)
    (b : β a) : m.insert a b = m.replaceₘ a b := by
  rw [Raw₀.insert_eq_insertₘ]
  simp only [Raw₀.insertₘ, h, ↓reduceIte]

omit [LawfulBEq α] in
private theorem raw_erase_of_containsₘ {m : Raw₀ α β} {a : α} (h : m.containsₘ a = true) :
    m.erase a = m.eraseₘaux a := by
  rw [Raw₀.erase_eq_eraseₘ]
  simp only [Raw₀.eraseₘ, h, ↓reduceIte]

omit [LawfulBEq α] in
private theorem raw_erase_of_not_containsₘ {m : Raw₀ α β} {a : α} (h : m.containsₘ a = false) :
    m.erase a = m := by
  rw [Raw₀.erase_eq_eraseₘ]
  simp only [Raw₀.eraseₘ, h, Bool.false_eq_true, ↓reduceIte]

private theorem raw_insert_comm {m : Raw₀ α β} {a b : α} (ha : m.containsₘ a = true)
    (hb : m.containsₘ b = true) (hab : a ≠ b) (x : β a) (y : β b) :
    (m.insert a x).insert b y = (m.insert b y).insert a x := by
  rw [raw_insert_of_containsₘ ha, raw_insert_of_containsₘ hb,
    raw_insert_of_containsₘ (by rwa [containsₘ_replaceₘ]),
    raw_insert_of_containsₘ (by rwa [containsₘ_replaceₘ])]
  apply Subtype.ext
  simp only [Raw₀.replaceₘ]
  congr 1
  exact updateBucket_comm _ _ _ _ _ _ (fun l => (replace_comm l hab x y).symm) _ _

private theorem raw_erase_insert_comm {m : Raw₀ α β} {a b : α} (ha : m.containsₘ a = true)
    (hab : a ≠ b) (x : β a) : (m.insert a x).erase b = (m.erase b).insert a x := by
  cases hb : m.containsₘ b with
  | false =>
    rw [raw_erase_of_not_containsₘ hb, raw_insert_of_containsₘ ha,
      raw_erase_of_not_containsₘ (by rwa [containsₘ_replaceₘ])]
  | true =>
    rw [raw_insert_of_containsₘ ha, raw_erase_of_containsₘ hb,
      raw_erase_of_containsₘ (by rwa [containsₘ_replaceₘ]),
      raw_insert_of_containsₘ (by rwa [containsₘ_eraseₘaux _ hab])]
    apply Subtype.ext
    simp only [Raw₀.replaceₘ, Raw₀.eraseₘaux]
    congr 1
    exact updateBucket_comm _ _ _ _ _ _ (fun l => (erase_replace_comm l hab x).symm) _ _

private theorem raw_erase_insert_self {m : Raw₀ α β} {a : α} (ha : m.containsₘ a = true)
    (x : β a) : (m.insert a x).erase a = m.erase a := by
  rw [raw_insert_of_containsₘ ha, raw_erase_of_containsₘ ha,
    raw_erase_of_containsₘ (by rwa [containsₘ_replaceₘ])]
  apply Subtype.ext
  simp only [Raw₀.replaceₘ, Raw₀.eraseₘaux]
  congr 1
  rw [updateBucket_updateBucket]
  congr 1
  funext l
  exact erase_replace_self l a x

omit [LawfulBEq α] in
private theorem containsₘ_of {m : DHashMap α β} {a : α} (h : m.contains a = true) :
    Raw₀.containsₘ ⟨m.1, m.2.size_buckets_pos⟩ a = true := by
  rw [← Raw₀.contains_eq_containsₘ]; exact h

/-- Values written at two keys already there can be written in either order. -/
theorem DHashMap.insert_comm_of_contains {m : DHashMap α β} {a b : α} (ha : m.contains a = true)
    (hb : m.contains b = true) (hab : a ≠ b) (x : β a) (y : β b) :
    (m.insert a x).insert b y = (m.insert b y).insert a x := by
  have := congrArg Subtype.val (raw_insert_comm (containsₘ_of ha) (containsₘ_of hb) hab x y)
  cases m
  unfold DHashMap.insert
  congr 1

theorem DHashMap.erase_insert_comm_of_contains {m : DHashMap α β} {a b : α}
    (ha : m.contains a = true) (hab : a ≠ b) (x : β a) :
    (m.insert a x).erase b = (m.erase b).insert a x := by
  have := congrArg Subtype.val (raw_erase_insert_comm (containsₘ_of ha) hab x)
  cases m
  unfold DHashMap.insert DHashMap.erase
  congr 1

theorem DHashMap.erase_insert_of_contains {m : DHashMap α β} {a : α} (ha : m.contains a = true)
    (x : β a) : (m.insert a x).erase a = m.erase a := by
  have := congrArg Subtype.val (raw_erase_insert_self (containsₘ_of ha) x)
  cases m
  unfold DHashMap.insert DHashMap.erase
  congr 1

end Lanes
