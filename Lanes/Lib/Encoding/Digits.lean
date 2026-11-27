/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
Numbers written in a base up to 16, most significant digit first: as few digits as it takes
(`digits`, never a leading zero) or a fixed number of them (`split`), and read back (`join`,
`ofChars?`). The text formats in `Lanes/Data/` write and read their numbers through these.
-/

@[expose] public section

namespace Lanes.Digits

def join (b : Nat) (ds : List Nat) : Nat := ds.foldl (fun acc d => acc * b + d) 0

theorem foldl_join (b a : Nat) (ds : List Nat) :
    ds.foldl (fun acc d => acc * b + d) a = a * b ^ ds.length + join b ds := by
  induction ds generalizing a with
  | nil => simp [join]
  | cons d ds ih =>
    simp only [List.foldl_cons, join, List.length_cons] at ih ⊢
    rw [ih, ih (0 * b + d), Nat.pow_succ]
    simp only [Nat.zero_mul, Nat.zero_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm b, Nat.add_assoc]

theorem join_cons (b d : Nat) (ds : List Nat) : join b (d :: ds) = d * b ^ ds.length + join b ds := by
  simp only [join, List.foldl_cons, Nat.zero_mul, Nat.zero_add]
  exact foldl_join b d ds

theorem join_append (b : Nat) (ds : List Nat) (d : Nat) : join b (ds ++ [d]) = join b ds * b + d := by
  simp [join, List.foldl_append]

theorem join_lt {b : Nat} {ds : List Nat} (h : ∀ d ∈ ds, d < b) : join b ds < b ^ ds.length := by
  induction ds with
  | nil => simp [join]
  | cons d ds ih =>
    rw [join_cons, List.length_cons, Nat.pow_succ]
    have hd := h d (by simp)
    have := ih fun x hx => h x (by simp [hx])
    have : d * b ^ ds.length + b ^ ds.length ≤ b ^ ds.length * b := by
      rw [Nat.mul_comm (b ^ ds.length) b, ← Nat.succ_mul]
      exact Nat.mul_le_mul_right _ hd
    omega

/-- The last `width` digits of `n`. -/
def split (b : Nat) : (width : Nat) → Nat → List Nat
  | 0, _ => []
  | w + 1, n => split b w (n / b) ++ [n % b]

theorem length_split (b w n : Nat) : (split b w n).length = w := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih => simp [split, ih]

theorem join_split (b w n : Nat) : join b (split b w n) = n % b ^ w := by
  induction w generalizing n with
  | zero => simp [split, join, Nat.mod_one]
  | succ w ih =>
    rw [split, join_append, ih, Nat.pow_succ, Nat.mul_comm (b ^ w) b, Nat.mod_mul]
    rw [Nat.mul_comm b]; omega

theorem split_add (b w k n : Nat) : split b (w + k) n = split b w (n / b ^ k) ++ split b k n := by
  induction k generalizing n with
  | zero => simp [split]
  | succ k ih =>
    rw [← Nat.add_assoc, split, ih, split, Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm b,
      List.append_assoc]

theorem lt_of_mem_split {b w n d : Nat} (hb : 0 < b) (h : d ∈ split b w n) : d < b := by
  induction w generalizing n with
  | zero => cases h
  | succ w ih =>
    simp only [split, List.mem_append, List.mem_singleton] at h
    rcases h with h | rfl
    · exact ih h
    · exact Nat.mod_lt _ hb

/-- `n` in base `b`, in as few digits as it takes. -/
def digits (b n : Nat) : List Nat :=
  if _h : n < b ∨ b ≤ 1 then [n] else digits b (n / b) ++ [n % b]
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

theorem join_digits {b : Nat} (n : Nat) : join b (digits b n) = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [digits]
    split
    · simp [join]
    · rw [join_append, ih (n / b) (Nat.div_lt_self (by omega) (by omega))]
      exact Nat.div_add_mod' n b

theorem lt_of_mem_digits {b n d : Nat} (hb : 2 ≤ b) (h : d ∈ digits b n) : d < b := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [digits] at h
    split at h
    · simp only [List.mem_singleton] at h; omega
    · simp only [List.mem_append, List.mem_singleton] at h
      rcases h with h | rfl
      · exact ih (n / b) (Nat.div_lt_self (by omega) (by omega)) h
      · exact Nat.mod_lt _ (by omega)

theorem head_digits {b n d : Nat} (hb : 2 ≤ b) (h : (digits b n).head? = some d) (hd : d = 0) :
    n = 0 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [digits] at h
    split at h
    · simp_all
    · rename_i hn
      have hne : digits b (n / b) ≠ [] := by rw [digits]; split <;> simp
      obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil hne
      rw [hx, List.cons_append, List.head?_cons, Option.some.injEq] at h
      have := ih (n / b) (Nat.div_lt_self (by omega) (by omega)) (by rw [hx, h]; rfl)
      have := Nat.div_pos (show b ≤ n by omega) (show 0 < b by omega)
      omega

theorem length_digits_le {b n k : Nat} (hb : 2 ≤ b) (hk : 1 ≤ k) (h : n < b ^ k) :
    (digits b n).length ≤ k := by
  induction n using Nat.strongRecOn generalizing k with
  | ind n ih =>
    rw [digits]
    split
    · simpa using hk
    · rename_i hn
      obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have hk' : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with rfl | hpos
        · simp at h; omega
        · exact hpos
      have : n / b < b ^ k := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]; rwa [← Nat.pow_succ]
      simpa using ih (n / b) (Nat.div_lt_self (by omega) (by omega)) hk' this

def char (d : Nat) : Char := if d < 10 then Char.ofNat (48 + d) else Char.ofNat (87 + d)

/-- Hex digits are read in either case. -/
def valueOf (c : Char) : Nat :=
  if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then c.toNat - 48
  else if 97 ≤ c.toNat ∧ c.toNat ≤ 102 then c.toNat - 87
  else if 65 ≤ c.toNat ∧ c.toNat ≤ 70 then c.toNat - 55
  else 16

def value? (b : Nat) (c : Char) : Option Nat := if valueOf c < b then some (valueOf c) else none

theorem value?_char {b d : Nat} (hb : b ≤ 16) (hd : d < b) : value? b (char d) = some d := by
  have : ∀ b, b ≤ 16 → ∀ d, d < b → value? b (char d) = some d := by decide
  exact this b hb d hd

theorem value?_lt {b : Nat} {c : Char} {v : Nat} (h : value? b c = some v) : v < b := by
  unfold value? at h
  split at h
  · simp only [Option.some.injEq] at h; omega
  · cases h

/-- What `char` writes: a lowercase hex digit. -/
def lower : List Char := "0123456789abcdef".toList

theorem char_mem_lower {d : Nat} (hd : d < 16) : char d ∈ lower := by
  have : ∀ d, d < 16 → char d ∈ lower := by decide
  exact this d hd

def values? (b : Nat) : List Char → Option (List Nat)
  | [] => some []
  | c :: cs => do return (← value? b c) :: (← values? b cs)

theorem values?_map_char {b : Nat} (hb : b ≤ 16) {ds : List Nat} (h : ∀ d ∈ ds, d < b) :
    values? b (ds.map char) = some ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp [values?, value?_char hb (h d (by simp)), ih fun x hx => h x (by simp [hx])]

theorem lt_of_values? {b : Nat} {cs : List Char} {ds : List Nat} (h : values? b cs = some ds) :
    ∀ d ∈ ds, d < b := by
  induction cs generalizing ds with
  | nil => cases h; simp
  | cons c cs ih =>
    simp only [values?, Option.bind_eq_bind, Option.bind_eq_some_iff, pure,
      Option.some.injEq] at h
    obtain ⟨v, hv, vs, hvs, rfl⟩ := h
    intro d hd
    simp only [List.mem_cons] at hd
    rcases hd with rfl | hd
    · exact value?_lt hv
    · exact ih hvs d hd

theorem length_values? {b : Nat} {cs : List Char} {ds : List Nat} (h : values? b cs = some ds) :
    ds.length = cs.length := by
  induction cs generalizing ds with
  | nil => cases h; rfl
  | cons c cs ih =>
    simp only [values?, Option.bind_eq_bind, Option.bind_eq_some_iff, pure,
      Option.some.injEq] at h
    obtain ⟨v, hv, vs, hvs, rfl⟩ := h
    simp [ih hvs]

def ofChars? (b : Nat) (cs : List Char) : Option Nat := (values? b cs).map (join b)

/-- `n` in base `b` with no leading zero, in lowercase. -/
def toChars (b n : Nat) : List Char := (digits b n).map char

theorem ofChars?_toChars {b : Nat} (hb : 2 ≤ b) (hb' : b ≤ 16) (n : Nat) :
    ofChars? b (toChars b n) = some n := by
  simp [ofChars?, toChars, values?_map_char hb' fun d hd => lt_of_mem_digits hb hd, join_digits]

theorem mem_toChars {b n : Nat} {c : Char} (hb : 2 ≤ b) (hb' : b ≤ 16) (h : c ∈ toChars b n) :
    c ∈ lower := by
  simp only [toChars, List.mem_map] at h
  obtain ⟨d, hd, rfl⟩ := h
  exact char_mem_lower (by have := lt_of_mem_digits hb hd; omega)

theorem toChars_ne_nil (b n : Nat) : toChars b n ≠ [] := by
  rw [toChars, digits]; split <;> simp

theorem length_toChars_le {b n k : Nat} (hb : 2 ≤ b) (hk : 1 ≤ k) (h : n < b ^ k) :
    (toChars b n).length ≤ k := by
  simpa [toChars] using length_digits_le hb hk h

theorem char_eq_zero {d : Nat} (hd : d < 16) (h : char d = '0') : d = 0 := by
  have : ∀ d, d < 16 → char d = '0' → d = 0 := by decide
  exact this d hd h

/-- No leading zero (RFC 5952 §4.1): a number other than zero does not start with `0`. -/
theorem head_toChars {b n : Nat} (hb : 2 ≤ b) (hb' : b ≤ 16) (h : (toChars b n).head? = some '0') :
    n = 0 := by
  simp only [toChars, List.head?_map, Option.map_eq_some_iff] at h
  obtain ⟨d, hd, hc⟩ := h
  have hlt := lt_of_mem_digits hb (List.mem_of_head? hd)
  exact head_digits hb hd (char_eq_zero (by omega) hc)

/-- `n` in exactly `width` digits, zeros in front. -/
def fixed (b width n : Nat) : List Char := (split b width n).map char

theorem length_fixed (b w n : Nat) : (fixed b w n).length = w := by
  simp [fixed, length_split]

theorem ofChars?_fixed {b : Nat} (hb : 0 < b) (hb' : b ≤ 16) (w n : Nat) :
    ofChars? b (fixed b w n) = some (n % b ^ w) := by
  simp [ofChars?, fixed, values?_map_char hb' fun d hd => lt_of_mem_split hb hd, join_split]

theorem ofChars?_lt {b : Nat} {cs : List Char} {n : Nat} (h : ofChars? b cs = some n) :
    n < b ^ cs.length := by
  simp only [ofChars?, Option.map_eq_some_iff] at h
  obtain ⟨ds, hds, rfl⟩ := h
  rw [← length_values? hds]
  exact join_lt (lt_of_values? hds)

end Lanes.Digits
