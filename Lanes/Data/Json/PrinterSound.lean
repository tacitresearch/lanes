/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Data.Json.Grammar
public import Lanes.Data.Json.Printer
public import Lanes.Data.Utf8

/-!
What the printers write: for every value, `compress` and `pretty` write a JSON text that means
that value (`text_compress`, `text_pretty`), which is valid UTF-8. That the meaning is the value
covers escaping: in `Grammar.Chars` a quote, a backslash or a control character appears only
escaped.
-/

@[expose] public section

namespace Lanes.Json

open Grammar

theorem escapeChar_toList (acc : String) (c : Char) :
    (escapeChar acc c).toList = acc.toList ++ (escapeChar "" c).toList := by
  unfold escapeChar
  repeat' split
  all_goals simp [String.toList_append]

theorem escapeChar_of_not_needsEscape {c : Char} (h : needsEscape c = false) :
    (escapeChar "" c).toList = [c] := by
  simp only [needsEscape, Bool.or_eq_false_iff, beq_eq_false_iff_ne, decide_eq_false_iff_not] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  unfold escapeChar
  repeat' split
  all_goals first
    | simp; done
    | (rename_i h; simp only [beq_iff_eq] at h; subst h
       first | exact absurd rfl h1 | exact absurd rfl h2 | exact absurd (by decide) h3)

theorem flatMap_escapeChar {cs : List Char} (h : ∀ c ∈ cs, needsEscape c = false) :
    cs.flatMap (fun c => (escapeChar "" c).toList) = cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [List.flatMap_cons, escapeChar_of_not_needsEscape (h c (by simp)),
      ih fun c hc => h c (by simp [hc])]
    rfl

theorem escape_toList (s acc : String) :
    (escape s acc).toList = acc.toList ++ s.toList.flatMap fun c => (escapeChar "" c).toList := by
  unfold escape
  split
  · rw [String.foldl_eq_foldl_toList]
    induction s.toList generalizing acc with
    | nil => simp
    | cons c cs ih =>
      simp only [List.foldl_cons, List.flatMap_cons]
      rw [ih, escapeChar_toList, List.append_assoc]
  · rename_i h
    rw [String.contains_bool_eq] at h
    simp only [List.any_eq_true, not_exists, not_and, Bool.not_eq_true] at h
    rw [String.toList_append, flatMap_escapeChar h]

theorem hexDigit?_digitChar : ∀ k < 16, Parser.hexDigit? (Nat.digitChar k) = some k
  | 0, _ => by rw [Nat.digitChar_eq_zero.mpr rfl]; decide
  | 1, _ => by rw [Nat.digitChar_eq_one.mpr rfl]; decide
  | 2, _ => by rw [Nat.digitChar_eq_two.mpr rfl]; decide
  | 3, _ => by rw [Nat.digitChar_eq_three.mpr rfl]; decide
  | 4, _ => by rw [Nat.digitChar_eq_four.mpr rfl]; decide
  | 5, _ => by rw [Nat.digitChar_eq_five.mpr rfl]; decide
  | 6, _ => by rw [Nat.digitChar_eq_six.mpr rfl]; decide
  | 7, _ => by rw [Nat.digitChar_eq_seven.mpr rfl]; decide
  | 8, _ => by rw [Nat.digitChar_eq_eight.mpr rfl]; decide
  | 9, _ => by rw [Nat.digitChar_eq_nine.mpr rfl]; decide
  | 10, _ => by rw [Nat.digitChar_eq_a.mpr rfl]; decide
  | 11, _ => by rw [Nat.digitChar_eq_b.mpr rfl]; decide
  | 12, _ => by rw [Nat.digitChar_eq_c.mpr rfl]; decide
  | 13, _ => by rw [Nat.digitChar_eq_d.mpr rfl]; decide
  | 14, _ => by rw [Nat.digitChar_eq_e.mpr rfl]; decide
  | 15, _ => by rw [Nat.digitChar_eq_f.mpr rfl]; decide
  | _ + 16, h => absurd h (by omega)

theorem chars_escapeChar {c : Char} {cs ds : List Char} (h : Chars cs ds) :
    Chars ((escapeChar "" c).toList ++ cs) (c :: ds) := by
  by_cases h1 : c = '"'
  · subst h1; simpa [escapeChar] using Chars.escape .quote h
  by_cases h2 : c = '\\'
  · subst h2; simpa [escapeChar] using Chars.escape .backslash h
  by_cases h3 : c = '\n'
  · subst h3; simpa [escapeChar] using Chars.escape .lineFeed h
  by_cases h4 : c = '\r'
  · subst h4; simpa [escapeChar] using Chars.escape .carriageReturn h
  by_cases h5 : c = '\t'
  · subst h5; simpa [escapeChar] using Chars.escape .tab h
  by_cases h6 : c = '\x08'
  · subst h6; simpa [escapeChar] using Chars.escape .backspace h
  by_cases h7 : c = '\x0c'
  · subst h7; simpa [escapeChar] using Chars.escape .formFeed h
  by_cases h8 : c.val < 0x20
  · have hc : c.toNat < 32 := h8
    have hx := hexDigit?_digitChar (c.toNat / 16) (by omega)
    have hy := hexDigit?_digitChar (c.toNat % 16) (by omega)
    have hex : Hex4 ['0', '0', Nat.digitChar (c.toNat / 16), Nat.digitChar (c.toNat % 16)]
        c.toNat := by
      have := Hex4.mk (a := '0') (b := '0') (x := 0) (y := 0) rfl rfl hx hy
      rwa [show 4096 * 0 + 256 * 0 + 16 * (c.toNat / 16) + c.toNat % 16 = c.toNat by omega]
        at this
    have := Chars.escape (Escape.unicode hex (.inl (by omega))) h
    rw [Char.ofNat_toNat] at this
    simpa [escapeChar, h1, h2, h3, h4, h5, h6, h7, h8, String.toList_push,
      String.toList_append] using this
  · simpa [escapeChar, h1, h2, h3, h4, h5, h6, h7, h8, String.toList_push] using
      Chars.plain ⟨UInt32.not_lt.mp h8, h1, h2⟩ h

theorem chars_escape (cs : List Char) :
    Chars (cs.flatMap fun c => (escapeChar "" c).toList) cs := by
  induction cs with
  | nil => exact .nil
  | cons c cs ih => exact chars_escapeChar ih

theorem renderString_toList (s acc : String) :
    (renderString s acc).toList =
      acc.toList ++ '"' :: (s.toList.flatMap fun c => (escapeChar "" c).toList) ++ ['"'] := by
  simp [renderString, String.toList_push, escape_toList]

/-! ### Numbers -/

theorem isDigit_of_mem_toDigits {n : Nat} {c : Char} (h : c ∈ Nat.toDigits 10 n) : IsDigit c := by
  have := Nat.isDigit_of_mem_toDigits (by decide) (by decide) h
  simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at this
  exact ⟨Char.le_def.mpr this.1, Char.le_def.mpr this.2⟩

theorem toDigits_head {n : Nat} (h : 0 < n) :
    ∃ d rest, Nat.toDigits 10 n = d :: rest ∧ d ≠ '0' := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [Nat.toDigits_eq_ite (by decide)]
    split
    · exact ⟨_, [], rfl, fun e => absurd (Nat.digitChar_eq_zero.mp e) (by omega)⟩
    · obtain ⟨d, rest, e, hd⟩ := ih (n / 10) (by omega) (by omega)
      exact ⟨d, rest ++ _, by rw [e]; rfl, hd⟩

theorem intPart_toDigits (n : Nat) : IntPart (Nat.toDigits 10 n) := by
  refine ⟨⟨Nat.toDigits_ne_nil, fun _ => isDigit_of_mem_toDigits⟩, fun h => ?_⟩
  cases n with
  | zero => exact Nat.toDigits_zero 10
  | succ n =>
    obtain ⟨d, rest, e, hd⟩ := toDigits_head (n := n + 1) (by omega)
    rw [e] at h
    exact absurd (Option.some.inj h) hd

theorem Grammar.Number.congr {md : Nat} {t t' : List Char} {v v' : JsonNumber} (h : Number md t v)
    (ht : t = t') (hv : v = v') : Number md t' v' := ht ▸ hv ▸ h

theorem ofScientific_mantissa (n : JsonNumber) :
    JsonNumber.ofScientific n.mantissa (-(n.exponent : Int)) = n := by
  obtain ⟨m, e, normal⟩ := n
  cases e with
  | zero => simp [JsonNumber.ofScientific, JsonNumber.fromInt]
  | succ e =>
    have : m % 10 ≠ 0 := normal.resolve_left (by omega)
    have hlt : -(((e + 1 : Nat) : Int)) < 0 := by omega
    simp only [JsonNumber.ofScientific, hlt, ↓reduceIte,
      show (-(((e + 1 : Nat) : Int))).natAbs = e + 1 by omega]
    simp [JsonNumber.ofDecimal, this]

theorem toList_toString_int (m : Int) :
    (toString m).toList = (if m < 0 then ['-'] else []) ++ Nat.toDigits 10 m.natAbs := by
  rw [Int.toString_eq_repr, Int.repr_eq_ite]
  split
  · have : ¬m < 0 := by omega
    simp only [this, ↓reduceIte, Nat.toList_repr, show m.toNat = m.natAbs by omega]; rfl
  · have : m < 0 := by omega
    simp only [this, ↓reduceIte, String.toList_append, Nat.toList_repr,
      show (-m).toNat = m.natAbs by omega]
    rfl

theorem signed_natAbs (m : Int) :
    (if decide (m < 0) then -(m.natAbs : Int) else m.natAbs) = m := by
  split <;> simp_all <;> omega

theorem toList_sign (p : Prop) [Decidable p] :
    (if p then "-" else "").toList = if decide p then ['-'] else [] := by
  split <;> simp_all

theorem number_of {md : Nat} {n : JsonNumber} {int frac fd exp ed : List Char} {e : Int}
    (hi : IntPart int) (hf : Frac frac fd) (hx : Exp exp e ed)
    (hd : Nat.ofDigitChars 10 (int ++ fd) 0 = n.mantissa.natAbs)
    (he : e - fd.length = -(n.exponent : Int))
    (h1 : (int ++ fd).length ≤ md) (h2 : ed.length ≤ md) (h3 : e.natAbs ≤ md) :
    Number md ((if decide (n.mantissa < 0) then ['-'] else []) ++ int ++ frac ++ exp) n :=
  (Number.mk _ hi hf hx h1 h2 h3).congr rfl
    (by rw [hd, signed_natAbs, he, ofScientific_mantissa])

theorem intPart_cons {d : Char} {rest : List Char} (hd : d ≠ '0')
    (h : ∀ c ∈ d :: rest, IsDigit c) : IntPart (d :: rest) :=
  ⟨⟨List.cons_ne_nil _ _, h⟩, fun e => absurd (Option.some.inj e) hd⟩

theorem digits_of_mem {l : List Char} (hne : l ≠ []) {m : List Char} (h : ∀ c ∈ m, IsDigit c)
    (hs : ∀ c ∈ l, c ∈ m) : Digits l :=
  ⟨hne, fun c hc => h c (hs c hc)⟩

theorem toDigits_length_le (p : Nat) : (Nat.toDigits 10 p).length ≤ max p 1 := by
  rw [Nat.length_toDigits_le_iff (by decide) (by omega)]
  have := Nat.lt_pow_self (n := max p 1) (a := 10) (by decide)
  omega

theorem number_toString {md : Nat} (n : JsonNumber) (h : n.digits ≤ md) :
    Number md n.toString.toList n := by
  have hD := intPart_toDigits n.mantissa.natAbs
  have hval := Nat.ofDigitChars_ten_toDigits (n := n.mantissa.natAbs)
  simp only [JsonNumber.digits] at h
  unfold JsonNumber.toString
  generalize hDdef : Nat.toDigits 10 n.mantissa.natAbs = D at hD h hval
  have hlen : 0 < D.length := List.length_pos_iff.mpr hD.1.1
  split
  · rename_i he
    rw [toList_toString_int, hDdef]
    exact (number_of (frac := []) (exp := []) hD .none .none (by simpa using hval)
      (by simp [he]) (by simp; omega) (by simp) (by simp)).congr (by simp) rfl
  rename_i he
  have hm : n.mantissa % 10 ≠ 0 := n.normal.resolve_left he
  obtain ⟨d, rest, hdr, hd0⟩ := toDigits_head (n := n.mantissa.natAbs) (by omega)
  rw [hDdef] at hdr
  subst hdr
  have hdig : ∀ c ∈ d :: rest, IsDigit c := hD.1.2
  have hl : (d :: rest).length = rest.length + 1 := rfl
  dsimp only
  by_cases hlt : n.exponent < (d :: rest).length
  · simp only [hlt, ↓reduceIte, String.toList_append, String.toList_ofList, toList_sign]
    obtain ⟨k, hk⟩ : ∃ k, (d :: rest).length - n.exponent = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos
      (by omega)).symm⟩
    rw [hk, List.take_succ_cons, List.drop_succ_cons]
    have hdrop : rest.drop k ≠ [] := by
      intro e
      have := congrArg List.length e
      simp at this hk
      omega
    refine (number_of (int := d :: rest.take k) (frac := '.' :: rest.drop k) (exp := [])
      (intPart_cons hd0 fun c hc => hdig c (by
        simp only [List.mem_cons] at hc ⊢
        exact hc.imp id List.mem_of_mem_take))
      (.some (digits_of_mem hdrop hdig fun c hc =>
        List.mem_cons_of_mem _ (List.mem_of_mem_drop hc)))
      .none ?_ ?_ ?_ (by simp) (by simp)).congr (by simp) rfl
    · rw [List.cons_append, List.take_append_drop, hval]
    · simp at hk ⊢; omega
    · rw [List.cons_append, List.take_append_drop]; omega
  by_cases hz : n.exponent - (d :: rest).length ≤ JsonNumber.maxLeadingZeros
  · simp only [hlt, hz, ↓reduceIte, String.toList_append, String.toList_ofList, toList_sign]
    refine (number_of (int := ['0'])
      (frac := '.' :: (List.replicate (n.exponent - (d :: rest).length) '0' ++ d :: rest))
      (exp := []) ⟨⟨by simp, by simp [IsDigit]⟩, fun _ => rfl⟩
      (.some (digits_of_mem (by simp) (m := '0' :: d :: rest) (by simpa [IsDigit] using hdig)
        fun c hc => by
          simp only [List.mem_append, List.mem_replicate, List.mem_cons] at hc ⊢
          rcases hc with ⟨_, rfl⟩ | hc
          · exact .inl rfl
          · exact .inr hc))
      .none ?_ ?_ ?_ (by simp) (by simp)).congr (by simp) rfl
    · rw [Nat.ofDigitChars_append, Nat.ofDigitChars_append, Nat.ofDigitChars_replicate_zero,
        show Nat.ofDigitChars 10 ['0'] 0 = 0 by simp [Nat.ofDigitChars_cons], Nat.mul_zero, hval]
    · simp; omega
    · simp; omega
  simp only [hlt, hz, ↓reduceIte, String.toList_append, String.toList_ofList, toList_sign,
    toList_toString_int]
  have hneg : ((d :: rest).length : Int) - 1 - n.exponent < 0 := by omega
  obtain ⟨P, hP⟩ : ∃ P, (((d :: rest).length : Int) - 1 - n.exponent).natAbs = P := ⟨_, rfl⟩
  have hPv : P = n.exponent - rest.length := by omega
  simp only [hneg, ↓reduceIte, hP, List.take_succ_cons, List.take_zero,
    List.drop_succ_cons, List.drop_zero]
  have hexp : Exp ('e' :: ['-'] ++ Nat.toDigits 10 P) (-(P : Int)) (Nat.toDigits 10 P) := by
    have := Exp.some (e := 'e') (ds := Nat.toDigits 10 P) ['-'] (.inl rfl) (.inr (.inr rfl))
      ⟨Nat.toDigits_ne_nil, fun _ => isDigit_of_mem_toDigits⟩
    simpa [Nat.ofDigitChars_ten_toDigits] using this
  have hlenP := toDigits_length_le P
  by_cases hr : rest = []
  · subst hr
    simp only [List.length_nil, List.length_cons] at *
    exact (number_of (int := [d]) (frac := []) (exp := 'e' :: ['-'] ++ Nat.toDigits 10 P)
      (intPart_cons hd0 hdig) .none hexp (by simpa using hval) (by simp; omega) (by simp; omega)
      (by omega) (by simp; omega)).congr (by simp) rfl
  · exact (number_of (int := [d]) (frac := '.' :: rest) (exp := 'e' :: ['-'] ++ Nat.toDigits 10 P)
      (intPart_cons (rest := []) hd0 fun c hc => hdig c (by simp at hc; simp [hc]))
      (.some (digits_of_mem hr hdig fun c hc => List.mem_cons_of_mem _ hc)) hexp
      (by simpa using hval) (by omega) (by simp; omega) (by omega)
      (by simp; omega)).congr (by simp [hr]) rfl

/-! ### Arrays and objects -/

theorem intercalate_cons_eq {α : Type} (sep y : List α) (ys : List (List α)) :
    sep.intercalate (y :: ys) = y ++ (ys.map (sep ++ ·)).flatten := by
  induction ys generalizing y with
  | nil => simp
  | cons z zs ih => simp [ih]

theorem foldl_separate {α : Type} (f : String × Bool → α → String × Bool) (g : α → List Char)
    (l : List α) (hf : ∀ x ∈ l, ∀ state,
      (f state x).1.toList = (separate state.1 state.2).toList ++ g x ∧ (f state x).2 = false)
    (acc : String) (first : Bool) :
    (l.foldl f (acc, first)).1.toList = acc.toList ++
      if first then [','].intercalate (l.map g) else (l.map (',' :: g ·)).flatten := by
  induction l generalizing acc first with
  | nil => cases first <;> simp
  | cons x xs ih =>
    obtain ⟨h1, h2⟩ := hf x (by simp) (acc, first)
    rw [List.foldl_cons, ← Prod.eta (f (acc, first) x), h2,
      ih (fun y hy => hf y (by simp [hy])), h1]
    cases first <;> simp [separate, String.toList_push, intercalate_cons_eq] <;> rfl

theorem compressTo_toList (acc : String) : (j : Json) →
    (compressTo acc j).toList = acc.toList ++ (compress j).toList
  | .null | .bool true | .bool false | .num _ => by
    simp [compress, compressTo, String.toList_append]
  | .str s => by simp [compress, compressTo, renderString_toList]
  | .arr elems => by
    rw [compress, compressTo, compressTo]
    simp only [String.toList_push, ← Array.foldl_toList]
    rw [foldl_separate _ (fun e => (compress e).toList) _
        (fun e he state => ⟨compressTo_toList _ e, rfl⟩),
      foldl_separate _ (fun e => (compress e).toList) _
        (fun e he state => ⟨compressTo_toList _ e, rfl⟩)]
    simp
  | .obj fields => by
    rw [compress, compressTo, compressTo]
    simp only [String.toList_push, ← Array.foldl_toList]
    have hf : ∀ field ∈ fields.toList, ∀ state : String × Bool,
        (compressTo ((renderString field.1 (separate state.1 state.2)).push ':') field.2,
          false).1.toList = (separate state.1 state.2).toList ++
            ((renderString field.1 "").toList ++ ':' :: (compress field.2).toList) ∧
        (compressTo ((renderString field.1 (separate state.1 state.2)).push ':') field.2,
          false).2 = false := fun field hfield state =>
      ⟨by simp [compressTo_toList _ field.2, renderString_toList, String.toList_push], rfl⟩
    rw [foldl_separate _ _ _ hf, foldl_separate _ _ _ hf]
    simp
termination_by j => j
decreasing_by
  all_goals first
    | (have := Array.sizeOf_lt_of_mem (Array.mem_toList_iff.mp ‹_›)
       simp only [arr.sizeOf_spec]; omega)
    | (have := sizeOf_field_lt (Array.mem_toList_iff.mp ‹_›)
       simp only [obj.sizeOf_spec]; omega)

theorem compress_arr (elems : Array Json) :
    (compress (.arr elems)).toList =
      '[' :: [','].intercalate (elems.toList.map fun e => (compress e).toList) ++ [']'] := by
  rw [compress, compressTo]
  simp only [String.toList_push, ← Array.foldl_toList]
  rw [foldl_separate _ (fun e => (compress e).toList) _
    (fun e _ state => ⟨compressTo_toList _ e, rfl⟩)]
  simp

theorem compress_obj (fields : Array (String × Json)) :
    (compress (.obj fields)).toList =
      '{' :: [','].intercalate (fields.toList.map fun field =>
        (renderString field.1 "").toList ++ ':' :: (compress field.2).toList) ++ ['}'] := by
  rw [compress, compressTo]
  simp only [String.toList_push, ← Array.foldl_toList]
  rw [foldl_separate _
    (fun field => (renderString field.1 "").toList ++ ':' :: (compress field.2).toList) _
    (fun field _ state =>
      ⟨by simp [compressTo_toList _ field.2, renderString_toList, String.toList_push], rfl⟩)]
  simp

theorem le_foldl_max {α : Type} (f : α → Nat) (l : List α) (init : Nat) :
    init ≤ l.foldl (fun d x => max d (f x)) init := by
  induction l generalizing init with
  | nil => exact Nat.le_refl _
  | cons x xs ih => exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

theorem le_foldl_max_of_mem {α : Type} (f : α → Nat) {x : α} {l : List α} (h : x ∈ l)
    (init : Nat) : f x ≤ l.foldl (fun d x => max d (f x)) init := by
  induction l generalizing init with
  | nil => cases h
  | cons y ys ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_trans (Nat.le_max_right _ _) (le_foldl_max f ys _)
    · exact ih h _

theorem depth_le_of_mem {elems : Array Json} {e : Json} (h : e ∈ elems) :
    e.depth + 1 ≤ (Json.arr elems).depth := by
  rw [depth, ← Array.foldl_toList]
  exact Nat.succ_le_succ (le_foldl_max_of_mem depth (Array.mem_toList_iff.mpr h) 0)

theorem digits_le_of_mem {elems : Array Json} {e : Json} (h : e ∈ elems) :
    e.digits ≤ (Json.arr elems).digits := by
  rw [digits.eq_def (Json.arr elems)]
  simp only [← Array.foldl_toList]
  exact le_foldl_max_of_mem Json.digits (Array.mem_toList_iff.mpr h) 0

theorem depth_le_of_field {fields : Array (String × Json)} {f : String × Json} (h : f ∈ fields) :
    f.2.depth + 1 ≤ (Json.obj fields).depth := by
  rw [depth, ← Array.foldl_toList]
  exact Nat.succ_le_succ
    (le_foldl_max_of_mem (fun f : String × Json => f.2.depth) (Array.mem_toList_iff.mpr h) 0)

theorem digits_le_of_field {fields : Array (String × Json)} {f : String × Json}
    (h : f ∈ fields) : f.2.digits ≤ (Json.obj fields).digits := by
  rw [digits.eq_def (Json.obj fields)]
  simp only [← Array.foldl_toList]
  exact le_foldl_max_of_mem (fun f : String × Json => f.2.digits) (Array.mem_toList_iff.mpr h) 0

/-- The text `compress` writes is a JSON value that means the value written. -/
theorem value_compress : (j : Json) → ∀ {maxDigits depth : Nat}, j.depth ≤ depth →
    j.digits ≤ maxDigits → Value maxDigits depth (compress j).toList j
  | .null, _, _, _, _ => by simpa [compress, compressTo] using Value.null _
  | .bool true, _, _, _, _ => by simpa [compress, compressTo] using Value.true _
  | .bool false, _, _, _, _ => by simpa [compress, compressTo] using Value.false _
  | .num n, _, _, _, hm => by
    simpa [compress, compressTo] using Value.num _ (number_toString n (by simpa [digits] using hm))
  | .str s, _, _, _, _ => by
    simpa [compress, compressTo, renderString_toList] using Value.str _ (chars_escape s.toList)
  | .arr elems, md, d, hd, hm => by
    rw [compress_arr]
    obtain ⟨d, rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by simp [depth] at hd; omega⟩
    by_cases he : elems.toList = []
    · rw [he, show elems = #[] from Array.toList_eq_nil_iff.mp he]
      exact Value.emptyArr d (w := []) nofun
    · have := Value.arr (maxDigits := md) d
        (elems.toList.map fun e => (({ before := [], text := (compress e).toList, after := [] } :
          Spaced), e)) (close := []) (by simpa using he) (by simp [Spaced.Ws, Ws])
        (by
          simp only [List.mem_map, Array.mem_toList_iff]
          rintro _ ⟨e, he, rfl⟩
          exact value_compress e (by have := depth_le_of_mem he; omega)
            (Nat.le_trans (digits_le_of_mem he) hm)) nofun
      simpa [Function.comp_def] using this
  | .obj fields, md, d, hd, hm => by
    rw [compress_obj]
    obtain ⟨d, rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by simp [depth] at hd; omega⟩
    by_cases he : fields.toList = []
    · rw [he, show fields = #[] from Array.toList_eq_nil_iff.mp he]
      exact Value.emptyObj d (w := []) nofun
    · have := Value.obj (maxDigits := md) d
        (fields.toList.map fun f => ({
          key := { before := [], text := (renderString f.1 "").toList, after := [] },
          name := f.1.toList,
          value := { before := [], text := (compress f.2).toList, after := [] },
          json := f.2 } : Member)) (close := []) (by simpa using he)
        (by simp only [List.mem_map]; rintro _ ⟨f, _, rfl⟩; simp [Spaced.Ws, Ws])
        (by
          simp only [List.mem_map, Array.mem_toList_iff]
          rintro _ ⟨f, hf, rfl⟩
          exact ⟨_, by simp [renderString_toList], chars_escape f.1.toList⟩)
        (by
          simp only [List.mem_map, Array.mem_toList_iff]
          rintro _ ⟨f, hf, rfl⟩
          exact value_compress f.2 (by have := depth_le_of_field hf; omega)
            (Nat.le_trans (digits_le_of_field hf) hm)) nofun
      simpa [Function.comp_def] using this
termination_by j => j
decreasing_by
  · have := Array.sizeOf_lt_of_mem he
    simp only [arr.sizeOf_spec]; omega
  · have := sizeOf_field_lt hf
    simp only [obj.sizeOf_spec]; omega

/-! ### Pretty printing -/

theorem toList_pushn (s : String) (c : Char) (n : Nat) :
    (s.pushn c n).toList = s.toList ++ List.replicate n c := by
  induction n with
  | zero => rw [String.pushn_eq_repeat_push, Nat.repeat, List.replicate_zero, List.append_nil]
  | succ n ih =>
    rw [String.pushn_eq_repeat_push] at ih ⊢
    rw [Nat.repeat, String.toList_push, ih, List.replicate_succ', List.append_assoc]

theorem ws_newline (indent level : Nat) : Ws (newline indent level).toList := by
  simp only [newline, toList_pushn, Ws, IsWs, List.mem_append, List.mem_replicate]
  rintro c (h | ⟨_, rfl⟩) <;> simp_all

theorem prettyTo_compressTo (indent level : Nat) (acc : String) {j : Json}
    (h : ∀ elems, j ≠ .arr elems) (h' : ∀ fields, j ≠ .obj fields) :
    prettyTo indent level acc j = compressTo acc j := by
  cases j
  case arr elems => exact absurd rfl (h elems)
  case obj fields => exact absurd rfl (h' fields)
  all_goals rw [prettyTo] <;> nofun

theorem prettyTo_toList (indent level : Nat) (acc : String) : (j : Json) →
    (prettyTo indent level acc j).toList = acc.toList ++ (prettyTo indent level "" j).toList
  | .arr elems => by
    rw [prettyTo, prettyTo]
    split
    · simp [String.toList_append]
    · simp only [String.toList_push, String.toList_append, ← Array.foldl_toList]
      have hf : ∀ e ∈ elems.toList, ∀ state : String × Bool,
          (prettyTo indent (level + 1) (separate state.1 state.2 ++ newline indent (level + 1)) e,
            false).1.toList = (separate state.1 state.2).toList ++
              ((newline indent (level + 1)).toList ++ (prettyTo indent (level + 1) "" e).toList) ∧
          (prettyTo indent (level + 1) (separate state.1 state.2 ++ newline indent (level + 1)) e,
            false).2 = false := fun e _ state =>
        ⟨by rw [prettyTo_toList _ _ _ e, String.toList_append, List.append_assoc], rfl⟩
      rw [foldl_separate _ _ _ hf, foldl_separate _ _ _ hf]
      simp
  | .obj fields => by
    rw [prettyTo, prettyTo]
    split
    · simp [String.toList_append]
    · simp only [String.toList_push, String.toList_append, ← Array.foldl_toList]
      have hf : ∀ field ∈ fields.toList, ∀ state : String × Bool,
          (prettyTo indent (level + 1)
            (renderString field.1 (separate state.1 state.2 ++ newline indent (level + 1)) ++ ": ")
            field.2, false).1.toList = (separate state.1 state.2).toList ++
              ((newline indent (level + 1)).toList ++ (renderString field.1 "").toList ++
                ':' :: ' ' :: (prettyTo indent (level + 1) "" field.2).toList) ∧
          (prettyTo indent (level + 1)
            (renderString field.1 (separate state.1 state.2 ++ newline indent (level + 1)) ++ ": ")
            field.2, false).2 = false := fun field _ state =>
        ⟨by
          rw [prettyTo_toList _ _ _ field.2, String.toList_append, renderString_toList]
          simp [String.toList_append, renderString_toList], rfl⟩
      rw [foldl_separate _ _ _ hf, foldl_separate _ _ _ hf]
      simp
  | .null => by
    rw [prettyTo_compressTo (j := .null) _ _ _ (fun _ e => nomatch e) (fun _ e => nomatch e),
      prettyTo_compressTo (j := .null) _ _ _ (fun _ e => nomatch e) (fun _ e => nomatch e),
      compressTo_toList, compressTo_toList]
    simp
  | .bool b => by
    rw [prettyTo_compressTo (j := .bool b) _ _ _ (fun _ e => nomatch e) (fun _ e => nomatch e),
      prettyTo_compressTo (j := .bool b) _ _ _ (fun _ e => nomatch e) (fun _ e => nomatch e),
      compressTo_toList, compressTo_toList]
    simp
  | .num n => by
    rw [prettyTo_compressTo (j := .num n) _ _ _ (fun _ e => nomatch e) (fun _ e => nomatch e),
      prettyTo_compressTo (j := .num n) _ _ _ (fun _ e => nomatch e) (fun _ e => nomatch e),
      compressTo_toList, compressTo_toList]
    simp
  | .str t => by
    rw [prettyTo_compressTo (j := .str t) _ _ _ (fun _ e => nomatch e) (fun _ e => nomatch e),
      prettyTo_compressTo (j := .str t) _ _ _ (fun _ e => nomatch e) (fun _ e => nomatch e),
      compressTo_toList, compressTo_toList]
    simp
termination_by j => j
decreasing_by
  all_goals first
    | (have := Array.sizeOf_lt_of_mem (Array.mem_toList_iff.mp ‹_›)
       simp only [arr.sizeOf_spec]; omega)
    | (have := sizeOf_field_lt (Array.mem_toList_iff.mp ‹_›)
       simp only [obj.sizeOf_spec]; omega)

/-- The text `prettyTo` writes is a JSON value that means the value written. -/
theorem value_prettyTo (indent : Nat) : (j : Json) → ∀ {maxDigits depth : Nat} (level : Nat),
    j.depth ≤ depth → j.digits ≤ maxDigits →
      Value maxDigits depth (prettyTo indent level "" j).toList j
  | .arr elems, md, d, level, hd, hm => by
    obtain ⟨d, rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by simp [depth] at hd; omega⟩
    rw [prettyTo]
    split
    · rename_i he
      rw [Array.isEmpty_iff.mp he]
      exact Value.emptyArr d (w := []) nofun
    · rename_i he
      simp only [String.toList_push, String.toList_append, ← Array.foldl_toList]
      rw [foldl_separate _ (fun e => (newline indent (level + 1)).toList ++
          (prettyTo indent (level + 1) "" e).toList) _
        (fun e _ state => ⟨by rw [prettyTo_toList, String.toList_append, List.append_assoc], rfl⟩)]
      have := Value.arr (maxDigits := md) d
        (elems.toList.map fun e => ((⟨(newline indent (level + 1)).toList,
          (prettyTo indent (level + 1) "" e).toList, []⟩ : Spaced), e))
        (close := (newline indent level).toList) (by simpa using he)
        (by
          simp only [List.mem_map]
          rintro _ ⟨e, _, rfl⟩
          exact ⟨ws_newline _ _, nofun⟩)
        (by
          simp only [List.mem_map, Array.mem_toList_iff]
          rintro _ ⟨e, he, rfl⟩
          exact value_prettyTo indent e (level + 1) (by have := depth_le_of_mem he; omega)
            (Nat.le_trans (digits_le_of_mem he) hm)) (ws_newline _ _)
      simpa [Function.comp_def] using this
  | .obj fields, md, d, level, hd, hm => by
    obtain ⟨d, rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by simp [depth] at hd; omega⟩
    rw [prettyTo]
    split
    · rename_i he
      rw [Array.isEmpty_iff.mp he]
      exact Value.emptyObj d (w := []) nofun
    · rename_i he
      simp only [String.toList_push, String.toList_append, ← Array.foldl_toList]
      rw [foldl_separate _ (fun field => (newline indent (level + 1)).toList ++
          (renderString field.1 "").toList ++ ':' :: ' ' ::
            (prettyTo indent (level + 1) "" field.2).toList) _
        (fun field _ state => ⟨by
          rw [prettyTo_toList, String.toList_append, renderString_toList]
          simp [String.toList_append, renderString_toList], rfl⟩)]
      have := Value.obj (maxDigits := md) d
        (fields.toList.map fun f => (⟨⟨(newline indent (level + 1)).toList,
          (renderString f.1 "").toList, []⟩, f.1.toList,
          ⟨[' '], (prettyTo indent (level + 1) "" f.2).toList, []⟩, f.2⟩ : Member))
        (close := (newline indent level).toList) (by simpa using he)
        (by
          simp only [List.mem_map]
          rintro _ ⟨f, _, rfl⟩
          exact ⟨⟨ws_newline _ _, nofun⟩, by simp [Ws, IsWs], nofun⟩)
        (by
          simp only [List.mem_map, Array.mem_toList_iff]
          rintro _ ⟨f, hf, rfl⟩
          exact ⟨_, by simp [renderString_toList], chars_escape f.1.toList⟩)
        (by
          simp only [List.mem_map, Array.mem_toList_iff]
          rintro _ ⟨f, hf, rfl⟩
          exact value_prettyTo indent f.2 (level + 1) (by have := depth_le_of_field hf; omega)
            (Nat.le_trans (digits_le_of_field hf) hm)) (ws_newline _ _)
      simpa [Function.comp_def] using this
  | .null, _, _, level, hd, hm => by
    rw [prettyTo_compressTo (j := .null) _ _ _ (fun _ e => nomatch e) (fun _ e => nomatch e)]
    exact value_compress _ hd hm
  | .bool b, _, _, level, hd, hm => by
    rw [prettyTo_compressTo (j := .bool b) _ _ _ (fun _ e => nomatch e) (fun _ e => nomatch e)]
    exact value_compress _ hd hm
  | .num n, _, _, level, hd, hm => by
    rw [prettyTo_compressTo (j := .num n) _ _ _ (fun _ e => nomatch e) (fun _ e => nomatch e)]
    exact value_compress _ hd hm
  | .str t, _, _, level, hd, hm => by
    rw [prettyTo_compressTo (j := .str t) _ _ _ (fun _ e => nomatch e) (fun _ e => nomatch e)]
    exact value_compress _ hd hm
termination_by j => j
decreasing_by
  · have := Array.sizeOf_lt_of_mem he
    simp only [arr.sizeOf_spec]; omega
  · have := sizeOf_field_lt hf
    simp only [obj.sizeOf_spec]; omega

/-! ### The printers' output -/

/-- `compress` writes a JSON text (RFC 8259) that means the value, fields in their stored order. -/
theorem text_compress (j : Json) : Text j.depth j.digits (compress j).toList j :=
  ⟨[], _, [], by simp, nofun, nofun, value_compress j (Nat.le_refl _) (Nat.le_refl _)⟩

/-- `pretty` writes a JSON text (RFC 8259) that means the value, fields in their stored order. -/
theorem text_pretty (j : Json) (indent : Nat) : Text j.depth j.digits (j.pretty indent).toList j :=
  ⟨[], _, [], by simp [pretty], nofun, nofun,
    value_prettyTo indent j 0 (Nat.le_refl _) (Nat.le_refl _)⟩

/-- A `String` is valid UTF-8 by construction, so the printers' output is too, for every value. -/
theorem fromUTF8?_compress (j : Json) :
    String.fromUTF8? (compress j).toByteArray = some (compress j) :=
  fromUTF8?_toByteArray _

theorem fromUTF8?_pretty (j : Json) (indent : Nat) :
    String.fromUTF8? (j.pretty indent).toByteArray = some (j.pretty indent) :=
  fromUTF8?_toByteArray _

end Lanes.Json
