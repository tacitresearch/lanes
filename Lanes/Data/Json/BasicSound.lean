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

end Lanes.Json
