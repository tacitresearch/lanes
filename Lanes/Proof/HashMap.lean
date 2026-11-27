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

end Lanes
