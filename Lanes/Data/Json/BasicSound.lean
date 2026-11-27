/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Data.Json.Basic

/-! What the accessors of `Json` return: each succeeds exactly on the shape it names. -/

@[expose] public section

namespace Lanes.Json

theorem isNull_iff {j : Json} : j.isNull = true ↔ j = .null := by
  cases j <;> simp [isNull]

theorem getBool?_eq_ok {j : Json} {b : Bool} : j.getBool? = .ok b ↔ j = .bool b := by
  cases j <;> simp [getBool?]

theorem getStr?_eq_ok {j : Json} {s : String} : j.getStr? = .ok s ↔ j = .str s := by
  cases j <;> simp [getStr?]

theorem getNum?_eq_ok {j : Json} {n : JsonNumber} : j.getNum? = .ok n ↔ j = .num n := by
  cases j <;> simp [getNum?]

theorem getArr?_eq_ok {j : Json} {elems : Array Json} : j.getArr? = .ok elems ↔ j = .arr elems := by
  cases j <;> simp [getArr?]

theorem getObj?_eq_ok {j : Json} {fields : Array (String × Json)} :
    j.getObj? = .ok fields ↔ j = .obj fields := by
  cases j <;> simp [getObj?]

theorem getInt?_eq_ok {j : Json} {i : Int} : j.getInt? = .ok i ↔ j = .num i := by
  cases j with
  | num n =>
    obtain ⟨m, e, normal⟩ := n
    simp only [getInt?, JsonNumber.toInt?, num.injEq]
    constructor
    · intro h
      split at h <;> simp_all [JsonNumber.fromInt]
    · intro h
      simp only [JsonNumber.fromInt, JsonNumber.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp
  | _ => simp [getInt?]

theorem getNat?_eq_ok {j : Json} {n : Nat} : j.getNat? = .ok n ↔ j = .num n := by
  cases j with
  | num x =>
    obtain ⟨m, e, normal⟩ := x
    simp only [getNat?, JsonNumber.toNat?, num.injEq]
    constructor
    · intro h
      split at h
      · rename_i k hk
        split at hk
        · rename_i hc
          simp only [Option.some.injEq, Except.ok.injEq] at hk h
          subst hk h
          simp only [JsonNumber.fromNat, JsonNumber.fromInt, JsonNumber.mk.injEq]
          omega
        · simp at hk
      · simp at h
    · intro h
      simp only [JsonNumber.fromNat, JsonNumber.fromInt, JsonNumber.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp
  | _ => simp [getNat?]

theorem getArrVal?_eq_ok {j : Json} {i : Nat} {v : Json} :
    j.getArrVal? i = .ok v ↔ ∃ elems, j = .arr elems ∧ elems[i]? = some v := by
  cases j with
  | arr elems =>
    simp only [getArrVal?, arr.injEq, exists_eq_left']
    split <;> simp_all
  | _ => simp [getArrVal?]

/-- The value of the first field with the key. -/
theorem getObjVal?_eq_ok {j : Json} {key : String} {v : Json} :
    j.getObjVal? key = .ok v ↔
      ∃ fields, j = .obj fields ∧ (fields.find? (·.1 == key)).map (·.2) = some v := by
  cases j with
  | obj fields =>
    simp only [getObjVal?, obj.injEq, exists_eq_left']
    split
    · rename_i f hf
      simp [hf]
    · rename_i hf
      simp [hf]
  | _ => simp [getObjVal?]

/-! ### Objects built by `mkObj` -/

theorem find?_dedupFields {key : String} : ∀ {l : List (String × Json)},
    l.Pairwise (fun a b => a.1 ≤ b.1) →
    (dedupFields l).find? (·.1 == key) = (l.filter (·.1 == key)).getLast?
  | [], _ => rfl
  | [a], _ => by
    by_cases hk : a.1 = key <;> simp [dedupFields, hk]
  | a :: b :: rest, h => by
    have ih := find?_dedupFields (key := key) (l := b :: rest) (List.pairwise_cons.mp h).2
    by_cases hab : a.1 = b.1
    · simp only [dedupFields, hab, ↓reduceIte]
      rw [ih]
      by_cases hk : b.1 = key <;> simp [hab, hk]
    · simp only [dedupFields, hab, ↓reduceIte, List.find?_cons]
      by_cases hk : a.1 = key
      · have hnone : (b :: rest).filter (·.1 == key) = [] := by
          rw [List.filter_eq_nil_iff]
          intro c hc hck
          simp only [beq_iff_eq] at hck
          have hab' : a.1 ≤ b.1 := (List.pairwise_cons.mp h).1 b (by simp)
          rcases List.mem_cons.mp hc with rfl | hc
          · exact hab (hk.trans hck.symm)
          · have hbc : b.1 ≤ c.1 := (List.pairwise_cons.mp (List.pairwise_cons.mp h).2).1 c hc
            exact hab (Std.le_antisymm hab' (by rw [hk, ← hck]; exact hbc))
        have : (a :: b :: rest).filter (·.1 == key) = [a] := by
          rw [List.filter_cons, hnone]; simp [hk]
        simp [hk, this]
      · have hk' : (a.1 == key) = false := by simpa using hk
        simp [hk', ih, List.filter_cons]

theorem filter_sortFields (key : String) (l : List (String × Json)) :
    (sortFields l).filter (·.1 == key) = l.filter (·.1 == key) := by
  have trans : ∀ a b c : String × Json, decide (a.1 ≤ b.1) → decide (b.1 ≤ c.1) →
      decide (a.1 ≤ c.1) := by
    intro a b c h1 h2
    simp only [decide_eq_true_eq] at *
    exact Std.le_trans h1 h2
  have total : ∀ a b : String × Json, (decide (a.1 ≤ b.1) || decide (b.1 ≤ a.1)) := by
    intro a b
    rcases Std.le_total (a := a.1) (b := b.1) with h | h <;> simp [h]
  have hpw : (l.filter (·.1 == key)).Pairwise (fun a b => decide (a.1 ≤ b.1)) := by
    refine List.Pairwise.imp_of_mem ?_ (List.pairwise_of_forall (R := fun _ _ => True) (by simp))
    intro a b ha hb _
    simp only [List.mem_filter, beq_iff_eq] at ha hb
    rw [ha.2, hb.2]
    simp
  have hsub := (List.sublist_mergeSort trans total hpw List.filter_sublist).filter
    (fun a : String × Json => a.1 == key)
  rw [List.filter_filter] at hsub
  simp only [Bool.and_self] at hsub
  have hlen : ((sortFields l).filter (·.1 == key)).length = (l.filter (·.1 == key)).length :=
    ((List.mergeSort_perm l _).filter _).length_eq
  exact (hsub.eq_of_length hlen.symm).symm

/-- `mkObj` keeps, of the fields with one key, the last. -/
theorem getObjVal?_mkObj {fields : List (String × Json)} {key : String} {v : Json} :
    (mkObj fields).getObjVal? key = .ok v ↔
      ((fields.filter (·.1 == key)).getLast?).map (·.2) = some v := by
  have hpw : (sortFields fields).Pairwise (fun a b => a.1 ≤ b.1) := by
    have := List.pairwise_mergeSort (le := fun a b : String × Json => decide (a.1 ≤ b.1))
      (fun a b c h1 h2 => by simp only [decide_eq_true_eq] at *; exact Std.le_trans h1 h2)
      (fun a b => by rcases Std.le_total (a := a.1) (b := b.1) with h | h <;> simp [h]) fields
    exact this.imp (by simp)
  rw [mkObj, getObjVal?_eq_ok]
  simp only [obj.injEq, exists_eq_left', List.find?_toArray, find?_dedupFields hpw,
    filter_sortFields]

end Lanes.Json
