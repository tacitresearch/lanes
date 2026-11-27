/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Lib.Net.Url

/-!
What `Lanes.Url` is proved to do: `print` writes what `parse` reads back (`parse_print`),
`removeDots` leaves no dot segment and changes no path that has none (`dotFree_removeDots`,
`removeDots_of_dotFree`), resolution keeps an absolute reference and leaves no dot segment
(`resolve_of_absolute`, `dotFree_resolve`), and `normalize` is idempotent
(`normalize_normalize`). §5.4's examples are evaluated in `Tests/Oracle/Url.lean`.
-/

@[expose] public section

namespace Lanes.Url

/-! ### Dot segments -/

/-- A segment that is not `.` or `..`. -/
def NonDot (s : List Char) : Prop := s ≠ ['.'] ∧ s ≠ ['.', '.']

/-- A path none of whose segments is `.` or `..`. -/
def DotFree (p : String) : Prop := ∀ s ∈ p.toList.splitOn '/', NonDot s

def Good (x : Bool × List Char) : Prop := NonDot x.2 ∧ '/' ∉ x.2

/-- The output of `dots`: good pieces, all but the first written (the last of the list) after
a `/`. -/
def Stack (out : List (Bool × List Char)) : Prop :=
  (∀ x ∈ out, Good x) ∧ ∀ x ∈ out.dropLast, x.1 = true

def AccOk (acc : List Char) : Prop := acc ≠ [] ∧ NonDot acc ∧ '/' ∉ acc

def Inv : Dots → List (Bool × List Char) → Prop
  | .start, out => out = []
  | .slash, out => Stack out
  | .seg b acc, out => Stack out ∧ (b = false → out = []) ∧ AccOk acc

theorem nonDot_reverse {s : List Char} (h : NonDot s) : NonDot s.reverse := by
  refine ⟨fun e => h.1 ?_, fun e => h.2 ?_⟩
  · simpa using congrArg List.reverse e
  · simpa using congrArg List.reverse e

theorem stack_push {out : List (Bool × List Char)} {s : List Char} (h : Stack out)
    (hs : Good (true, s)) : Stack ((true, s) :: out) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hs
    · exact h.1 x hx
  · intro x hx
    cases out with
    | nil => simp at hx
    | cons y ys =>
      rw [List.dropLast_cons_cons] at hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · rfl
      · exact h.2 x hx

theorem stack_tail {out : List (Bool × List Char)} (h : Stack out) : Stack out.tail := by
  refine ⟨fun x hx => h.1 x (List.mem_of_mem_tail hx), fun x hx => ?_⟩
  cases out with
  | nil => simp at hx
  | cons y ys =>
    cases ys with
    | nil => simp at hx
    | cons z zs =>
      apply h.2 x
      rw [List.dropLast_cons_cons]
      exact List.mem_cons_of_mem _ hx

theorem stack_nil : Stack [] := ⟨by simp, by simp⟩

theorem stack_one {s : List Char} {b : Bool} (h : Good (b, s)) : Stack [(b, s)] :=
  ⟨by simpa using h, by simp⟩

theorem good_empty : Good (true, []) := ⟨⟨by simp, by simp⟩, by simp⟩

theorem accOk_cons {c : Char} {acc : List Char} (h : AccOk acc) (hc : c ≠ '/') :
    AccOk (c :: acc) := by
  obtain ⟨h1, ⟨h2, h3⟩, h4⟩ := h
  refine ⟨by simp, ⟨?_, ?_⟩, ?_⟩
  · intro e
    simp only [List.cons.injEq] at e
    exact h1 e.2
  · intro e
    simp only [List.cons.injEq] at e
    exact h2 e.2
  · simp [Ne.symm hc, h4]

theorem good_of_accOk {b : Bool} {acc : List Char} (h : AccOk acc) : Good (b, acc.reverse) :=
  ⟨nonDot_reverse h.2.1, by simpa using h.2.2⟩

theorem stack_push' {out : List (Bool × List Char)} {b : Bool} {s : List Char} (h : Stack out)
    (hb : b = false → out = []) (hs : Good (b, s)) : Stack ((b, s) :: out) := by
  cases b with
  | true => exact stack_push h hs
  | false => rw [hb rfl]; exact stack_one hs

theorem accOk_three {c : Char} (hc : c ≠ '/') : AccOk [c, '.', '.'] :=
  ⟨by simp, ⟨by simp, by simp⟩, by simp [Ne.symm hc]⟩

theorem accOk_two {c : Char} (hc : c ≠ '/') (hd : c ≠ '.') : AccOk [c, '.'] :=
  ⟨by simp, ⟨by simp, by simp [hd]⟩, by simp [Ne.symm hc]⟩

theorem accOk_one {c : Char} (hc : c ≠ '/') (hd : c ≠ '.') : AccOk [c] :=
  ⟨by simp, ⟨by simp [hd], by simp⟩, by simp [Ne.symm hc]⟩

theorem not_dot {c : Char} {rest : List Char} (h1 : c = '.' → rest = [] → False)
    (h2 : ∀ (d : Char) (r : List Char), c = '.' → rest = d :: r → False) : c ≠ '.' := by
  intro e
  cases rest with
  | nil => exact h1 e rfl
  | cons d r => exact h2 d r e rfl

theorem stack_dots (m : Dots) (cs : List Char) (out : List (Bool × List Char)) (h : Inv m out) :
    Stack (dots m cs out) := by
  fun_induction dots m cs out <;> simp only [Inv] at h
  case case1 ih | case2 ih | case10 ih => exact ih h
  case case3 | case4 | case5 => exact h ▸ stack_nil
  case case6 ih => exact ih (h ▸ stack_nil)
  case case7 hc ih => exact ih ⟨h ▸ stack_nil, fun _ => h, accOk_three hc⟩
  case case8 ih => exact ih ⟨h ▸ stack_nil, fun _ => h, accOk_two (by assumption) (not_dot (by assumption) (by assumption))⟩
  case case9 ih => exact ih ⟨h ▸ stack_nil, fun _ => h, accOk_one (by assumption) (not_dot (by assumption) (by assumption))⟩
  case case11 | case14 => exact stack_push h good_empty
  case case12 ih => exact ih (stack_tail h)
  case case13 => exact stack_push (stack_tail h) good_empty
  case case15 ih => exact ih (stack_push h good_empty)
  case case16 hc ih => exact ih ⟨h, nofun, accOk_three hc⟩
  case case17 ih => exact ih ⟨h, nofun, accOk_two (by assumption) (not_dot (by assumption) (by assumption))⟩
  case case18 ih => exact ih ⟨h, nofun, accOk_one (by assumption) (not_dot (by assumption) (by assumption))⟩
  case case19 ih => exact ih (stack_push' h.1 h.2.1 (good_of_accOk h.2.2))
  case case20 hc ih => exact ih ⟨h.1, h.2.1, accOk_cons h.2.2 hc⟩
  case case21 => exact stack_push' h.1 h.2.1 (good_of_accOk h.2.2)

/-- The segments of a stack, bottom first, as `join` writes them between slashes. -/
def segs : List (Bool × List Char) → List (List Char)
  | [] => [[]]
  | (false, s) :: rest => s :: rest.map (·.2)
  | (true, s) :: rest => [] :: s :: rest.map (·.2)

theorem flatten_slashes (a : List Char) (ss : List (List Char)) :
    a ++ (ss.map ('/' :: ·)).flatten = ['/'].intercalate (a :: ss) := by
  induction ss generalizing a with
  | nil => simp
  | cons s ss ih => simp [List.intercalate_cons_cons, ← ih]

theorem map_piece {rest : List (Bool × List Char)} (h : ∀ x ∈ rest, x.1 = true) :
    rest.map piece = (rest.map (·.2)).map ('/' :: ·) := by
  induction rest with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨b, s⟩ := x
    have hb : b = true := h (b, s) (by simp)
    subst hb
    simp [piece, ih fun y hy => h y (by simp [hy])]

theorem flatten_eq_intercalate {L : List (Bool × List Char)} (h : ∀ x ∈ L.tail, x.1 = true) :
    (L.map piece).flatten = ['/'].intercalate (segs L) := by
  match L with
  | [] => simp [segs]
  | (false, s) :: rest =>
    simp only [List.tail_cons] at h
    rw [List.map_cons, List.flatten_cons, map_piece h, segs, flatten_slashes]
    rfl
  | (true, s) :: rest =>
    simp only [List.tail_cons] at h
    rw [List.map_cons, List.flatten_cons, map_piece h, segs, ← flatten_slashes]
    simp [piece]

theorem join_eq_intercalate {out : List (Bool × List Char)} (h : Stack out) :
    join out = ['/'].intercalate (segs out.reverse) := by
  apply flatten_eq_intercalate
  intro x hx
  rw [List.tail_reverse, List.mem_reverse] at hx
  exact h.2 x hx

theorem good_segs {out : List (Bool × List Char)} (h : Stack out) :
    ∀ s ∈ segs out.reverse, NonDot s ∧ '/' ∉ s := by
  have hg : ∀ x ∈ out.reverse, Good x := fun x hx => h.1 x (List.mem_reverse.mp hx)
  have empty : NonDot [] ∧ '/' ∉ ([] : List Char) := ⟨⟨by simp, by simp⟩, by simp⟩
  generalize out.reverse = L at hg
  intro s hs
  match L, hs with
  | [], hs => simp [segs] at hs; exact hs ▸ empty
  | (false, t) :: rest, hs =>
    simp only [segs, List.mem_cons, List.mem_map] at hs
    rcases hs with rfl | ⟨x, hx, rfl⟩
    · exact hg (false, s) (by simp)
    · exact hg x (by simp [hx])
  | (true, t) :: rest, hs =>
    simp only [segs, List.mem_cons, List.mem_map] at hs
    rcases hs with rfl | rfl | ⟨x, hx, rfl⟩
    · exact empty
    · exact hg (true, s) (by simp)
    · exact hg x (by simp [hx])

theorem segs_ne_nil (L : List (Bool × List Char)) : segs L ≠ [] := by
  match L with
  | [] | (false, _) :: _ | (true, _) :: _ => simp [segs]

theorem dotFree_join {out : List (Bool × List Char)} (h : Stack out) :
    ∀ s ∈ (join out).splitOn '/', NonDot s := by
  rw [join_eq_intercalate h, List.splitOn_intercalate '/' (fun l hl => (good_segs h l hl).2)
    (segs_ne_nil _)]
  exact fun s hs => (good_segs h s hs).1

theorem dotFree_removeDots (p : String) : DotFree (removeDots p) := by
  simp only [DotFree, removeDots, removeDotsChars, String.toList_ofList]
  exact dotFree_join (stack_dots .start p.toList [] rfl)

theorem dots_seg_append (b : Bool) (acc s tail : List Char) (out : List (Bool × List Char))
    (h : '/' ∉ s) : dots (.seg b acc) (s ++ tail) out = dots (.seg b (s.reverse ++ acc)) tail out := by
  induction s generalizing acc with
  | nil => rfl
  | cons c s ih =>
    have hc : c ≠ '/' := fun e => h (e ▸ List.mem_cons_self)
    rw [List.cons_append, dots, ih _ (fun hm => h (List.mem_cons_of_mem _ hm))]
    · simp
    · exact hc

/-- A tail that ends a segment. -/
def Ends (tail : List Char) : Prop := tail = [] ∨ ∃ r, tail = '/' :: r

theorem dots_slash_seg {s : List Char} (tail : List Char) (out : List (Bool × List Char))
    (hs : NonDot s) (h : '/' ∉ s) (hne : s ≠ []) :
    dots .slash (s ++ tail) out = dots (.seg true s.reverse) tail out := by
  obtain ⟨c, s', rfl⟩ := List.exists_cons_of_ne_nil hne
  have hc : c ≠ '/' := fun e => h (e ▸ List.mem_cons_self)
  have h' : '/' ∉ s' := fun hm => h (List.mem_cons_of_mem _ hm)
  by_cases hd : c = '.'
  · subst hd
    cases s' with
    | nil => exact absurd rfl hs.1
    | cons d s'' =>
      have hd' : d ≠ '/' := fun e => h' (e ▸ List.mem_cons_self)
      have h'' : '/' ∉ s'' := fun hm => h' (List.mem_cons_of_mem _ hm)
      by_cases hdd : d = '.'
      · subst hdd
        cases s'' with
        | nil => exact absurd rfl hs.2
        | cons e s3 =>
          have he : e ≠ '/' := fun e' => h'' (e' ▸ List.mem_cons_self)
          rw [List.cons_append, List.cons_append, List.cons_append, dots,
            dots_seg_append _ _ _ _ _ (fun hm => h'' (List.mem_cons_of_mem _ hm))]
          all_goals simp_all
      · rw [List.cons_append, List.cons_append, dots, dots_seg_append _ _ _ _ _ h'']
        all_goals simp_all
  · rw [List.cons_append, dots, dots_seg_append _ _ _ _ _ h']
    all_goals simp_all

theorem dots_start_seg {s : List Char} (tail : List Char) (out : List (Bool × List Char))
    (hs : NonDot s) (h : '/' ∉ s) (hne : s ≠ []) :
    dots .start (s ++ tail) out = dots (.seg false s.reverse) tail out := by
  obtain ⟨c, s', rfl⟩ := List.exists_cons_of_ne_nil hne
  have hc : c ≠ '/' := fun e => h (e ▸ List.mem_cons_self)
  have h' : '/' ∉ s' := fun hm => h (List.mem_cons_of_mem _ hm)
  by_cases hd : c = '.'
  · subst hd
    cases s' with
    | nil => exact absurd rfl hs.1
    | cons d s'' =>
      have hd' : d ≠ '/' := fun e => h' (e ▸ List.mem_cons_self)
      have h'' : '/' ∉ s'' := fun hm => h' (List.mem_cons_of_mem _ hm)
      by_cases hdd : d = '.'
      · subst hdd
        cases s'' with
        | nil => exact absurd rfl hs.2
        | cons e s3 =>
          have he : e ≠ '/' := fun e' => h'' (e' ▸ List.mem_cons_self)
          rw [List.cons_append, List.cons_append, List.cons_append, dots,
            dots_seg_append _ _ _ _ _ (fun hm => h'' (List.mem_cons_of_mem _ hm))]
          all_goals simp_all
      · rw [List.cons_append, List.cons_append, dots, dots_seg_append _ _ _ _ _ h'']
        all_goals simp_all
  · rw [List.cons_append, dots, dots_seg_append _ _ _ _ _ h']
    all_goals simp_all


theorem breakSlash_spec (cs : List Char) :
    cs = (breakSlash cs).1 ++ (breakSlash cs).2 ∧ '/' ∉ (breakSlash cs).1 ∧ Ends (breakSlash cs).2 := by
  induction cs with
  | nil => simp [breakSlash, Ends]
  | cons c cs ih =>
    by_cases hc : c = '/'
    · subst hc; simp [breakSlash, Ends]
    · rw [breakSlash]
      · obtain ⟨h1, h2, h3⟩ := ih
        exact ⟨by simp [← h1], by simp [Ne.symm hc, h2], h3⟩
      · exact hc

theorem join_cons (x : Bool × List Char) (out : List (Bool × List Char)) :
    join (x :: out) = join out ++ piece x := by
  simp [join]

/-- The first segment of a path and the rest after its `/`, if there is one. -/
theorem split_path (cs : List Char) :
    ∃ s, '/' ∉ s ∧ ((cs = s ∧ cs.splitOn '/' = [s])
      ∨ ∃ r, cs = s ++ '/' :: r ∧ cs.splitOn '/' = s :: r.splitOn '/') := by
  obtain ⟨e, hs, ht⟩ := breakSlash_spec cs
  generalize breakSlash cs = b at e hs ht
  obtain ⟨s, tail⟩ := b
  refine ⟨s, hs, ?_⟩
  rcases ht with ht | ⟨r, ht⟩
  · subst ht
    rw [List.append_nil] at e
    subst e
    exact .inl ⟨rfl, List.splitOn_eq_singleton hs⟩
  · subst ht e
    exact .inr ⟨r, rfl, List.splitOn_append_cons_self_of_not_mem hs r⟩

theorem join_dots_slash (cs : List Char) (out : List (Bool × List Char))
    (h : ∀ s ∈ cs.splitOn '/', NonDot s) : join (dots .slash cs out) = join out ++ '/' :: cs := by
  obtain ⟨s, hs, ⟨e, hsplit⟩ | ⟨r, e, hsplit⟩⟩ := split_path cs
  · have hd : NonDot s := h s (by simp [hsplit])
    subst e
    by_cases hne : cs = []
    · subst hne; simp [dots, join_cons, piece]
    · rw [← List.append_nil cs, dots_slash_seg _ _ hd hs hne, dots, join_cons]
      simp [piece]
  · have hd : NonDot s := h s (by simp [hsplit])
    have hr : ∀ t ∈ r.splitOn '/', NonDot t := fun t ht => h t (by simp [hsplit, ht])
    have : r.length < cs.length := by rw [e]; simp; omega
    subst e
    by_cases hne : s = []
    · subst hne
      rw [List.nil_append, dots, join_dots_slash r _ hr, join_cons]
      simp [piece]
    · rw [dots_slash_seg _ _ hd hs hne, dots, join_dots_slash r _ hr, join_cons]
      simp [piece]
termination_by cs.length

theorem join_dots_start (cs : List Char) (h : ∀ s ∈ cs.splitOn '/', NonDot s) :
    join (dots .start cs []) = cs := by
  obtain ⟨s, hs, ⟨e, hsplit⟩ | ⟨r, e, hsplit⟩⟩ := split_path cs
  · have hd : NonDot s := h s (by simp [hsplit])
    subst e
    by_cases hne : cs = []
    · subst hne; simp [dots, join]
    · rw [← List.append_nil cs, dots_start_seg _ _ hd hs hne, dots]
      simp [join, piece]
  · have hd : NonDot s := h s (by simp [hsplit])
    have hr : ∀ t ∈ r.splitOn '/', NonDot t := fun t ht => h t (by simp [hsplit, ht])
    subst e
    by_cases hne : s = []
    · subst hne
      rw [List.nil_append, dots, join_dots_slash r _ hr]
      simp [join]
    · rw [dots_start_seg _ _ hd hs hne, dots, join_dots_slash r _ hr, join_cons]
      simp [join, piece]

theorem removeDots_of_dotFree {p : String} (h : DotFree p) : removeDots p = p := by
  simp only [removeDots, removeDotsChars, join_dots_start _ h, String.ofList_toList]

theorem removeDots_removeDots (p : String) : removeDots (removeDots p) = removeDots p :=
  removeDots_of_dotFree (dotFree_removeDots p)

/-! ### Resolution -/

/-- §5.2.2: a reference with a scheme is its own target, its dot segments removed. -/
theorem resolve_of_scheme (base : Url) {r : Url} (h : r.scheme.isSome) :
    resolve base r = { r with path := removeDots r.path } := by
  simp [resolve, h]

theorem resolve_of_absolute (base : Url) {r : Url} (h : r.scheme.isSome) (hd : DotFree r.path) :
    resolve base r = r := by
  rw [resolve_of_scheme base h, removeDots_of_dotFree hd]

/-- The target's path has no dot segment, when the base's has none (§5.2.2 takes the base's
path as it is for a reference with an empty path). -/
theorem dotFree_resolve {base : Url} (r : Url) (hb : DotFree base.path) :
    DotFree (resolve base r).path := by
  unfold resolve
  split
  · exact dotFree_removeDots _
  split
  · exact dotFree_removeDots _
  split
  · exact hb
  split
  · exact dotFree_removeDots _
  · exact dotFree_removeDots _

/-! ### Characters -/

theorem toNat_ofNat_small {n : Nat} (h : n < 0xd800) : (Char.ofNat n).toNat = n := by
  have hv : n.isValidChar := Or.inl h
  simp [Char.ofNat, hv, Char.ofNatAux, Char.toNat, UInt32.toNat_ofNatLT]

theorem char_le {a b : Char} : a ≤ b ↔ a.toNat ≤ b.toNat := by
  simp [Char.le_def, UInt32.le_iff_toNat_le]

theorem lowerChar_lowerChar (c : Char) : lowerChar (lowerChar c) = lowerChar c := by
  unfold lowerChar
  by_cases h : 'A' ≤ c && c ≤ 'Z'
  · have hc : 65 ≤ c.toNat ∧ c.toNat ≤ 90 := by
      simp only [Bool.and_eq_true, decide_eq_true_eq, char_le] at h; exact h
    have := toNat_ofNat_small (n := c.toNat + 32) (by omega)
    have hZ : 'Z'.toNat = 90 := rfl
    simp only [h, ite_true]
    rw [ite_eq_right]
    simp only [Bool.and_eq_true, decide_eq_true_eq, char_le, this, hZ]
    omega
  · simp [h]

theorem lowerChar_ne {c : Char} (h : c ≠ '%') : lowerChar c ≠ '%' := by
  unfold lowerChar
  split
  · rename_i hc
    have hc : 65 ≤ c.toNat ∧ c.toNat ≤ 90 := by
      simp only [Bool.and_eq_true, decide_eq_true_eq, char_le] at hc; exact hc
    have := toNat_ofNat_small (n := c.toNat + 32) (by omega)
    intro e
    rw [e] at this
    simp at this
    omega
  · exact h

theorem lower_lower (cs : List Char) : lower (lower cs) = lower cs := by
  simp [lower, Function.comp_def, lowerChar_lowerChar]

def isUpperHex (c : Char) : Bool := isDigit c || ('A' ≤ c && c ≤ 'F')

theorem upperHex_spec {h : Char} (hh : isHex h) :
    isUpperHex (upperHex h) ∧ hexValue (upperHex h) = hexValue h := by
  have hA : 'A'.toNat = 65 := rfl
  have hF : 'F'.toNat = 70 := rfl
  have ha : 'a'.toNat = 97 := rfl
  have hf : 'f'.toNat = 102 := rfl
  have h0 : '0'.toNat = 48 := rfl
  have h9 : '9'.toNat = 57 := rfl
  simp only [isHex, isDigit, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, char_le, h0, h9,
    hA, hF, ha, hf] at hh
  unfold upperHex
  split
  · rename_i hl
    simp only [Bool.and_eq_true, decide_eq_true_eq, char_le, ha, hf] at hl
    have := toNat_ofNat_small (n := h.toNat - 32) (by omega)
    simp only [isUpperHex, isDigit, hexValue, Http.hexValue?, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq, char_le, this, h0, h9, hA, hF, ha, hf]
    refine ⟨by omega, ?_⟩
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
    simp only [Option.getD_some]
    omega
  · rename_i hl
    simp only [Bool.and_eq_true, decide_eq_true_eq, char_le, ha, hf, not_and, Nat.not_le] at hl
    simp only [isUpperHex, isDigit, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, char_le,
      h0, h9, hA, hF]
    exact ⟨by omega, trivial⟩

theorem upperHex_of_isUpperHex {h : Char} (hh : isUpperHex h) : upperHex h = h ∧ isHex h := by
  have hA : 'A'.toNat = 65 := rfl
  have hF : 'F'.toNat = 70 := rfl
  have ha : 'a'.toNat = 97 := rfl
  have h0 : '0'.toNat = 48 := rfl
  have h9 : '9'.toNat = 57 := rfl
  simp only [isUpperHex, isDigit, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, char_le,
    h0, h9, hA, hF] at hh
  refine ⟨?_, ?_⟩
  · unfold upperHex
    rw [ite_eq_right]
    simp only [Bool.and_eq_true, decide_eq_true_eq, char_le, ha]
    omega
  · simp only [isHex, isDigit, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, char_le, h0, h9,
      hA, hF]
    omega

theorem ne_of_isUnreserved {c : Char} (h : isUnreserved c) : c ≠ '%' ∧ c ≠ '/' := by
  constructor <;> rintro rfl <;> simp [isUnreserved, isAlpha, isDigit] at h

/-! ### Percent-encodings -/

/-- Text that `pct` leaves as it is: every `%` starts an encoding, in uppercase, of a byte that
is not unreserved. -/
def pctOk : List Char → Bool
  | '%' :: h :: l :: rest => isUpperHex h && isUpperHex l
      && !isUnreserved (Char.ofNat (hexValue h * 16 + hexValue l)) && pctOk rest
  | '%' :: _ => false
  | _ :: rest => pctOk rest
  | [] => true

theorem pctOk_cons {c : Char} (h : c ≠ '%') (rest : List Char) : pctOk (c :: rest) = pctOk rest := by
  rw [pctOk] <;> intros <;> simp_all

theorem pctOk_pct (x : List Char) : pctOk (pct x) = true := by
  fun_induction pct x
  case case1 h l rest hx hu ih =>
    rw [pctOk_cons (ne_of_isUnreserved hu).1, ih]
  case case2 h l rest hx hu ih =>
    simp only [Bool.and_eq_true] at hx
    obtain ⟨uh, vh⟩ := upperHex_spec hx.1
    obtain ⟨ul, vl⟩ := upperHex_spec hx.2
    simp [pctOk, uh, ul, vh, vl, hu, ih]
  case case3 ih => simp [pctOk, isUpperHex, isDigit, hexValue, Http.hexValue?, isUnreserved, isAlpha, ih]
  case case4 ih => simp [pctOk, isUpperHex, isDigit, hexValue, Http.hexValue?, isUnreserved, isAlpha, ih]
  case case5 c rest _ h2 ih => rw [pctOk_cons h2, ih]
  case case6 => rfl

theorem pct_of_pctOk {x : List Char} (h : pctOk x) : pct x = x := by
  fun_induction pct x
  case case1 hd l rest hx hu ih =>
    simp only [pctOk, Bool.and_eq_true, Bool.not_eq_true'] at h
    simp [h.1.2] at hu
  case case2 hd l rest hx hu ih =>
    simp only [pctOk, Bool.and_eq_true] at h
    rw [(upperHex_of_isUpperHex h.1.1.1).1, (upperHex_of_isUpperHex h.1.1.2).1, ih h.2]
  case case3 hd l rest hx ih =>
    simp only [pctOk, Bool.and_eq_true] at h
    simp [(upperHex_of_isUpperHex h.1.1.1).2, (upperHex_of_isUpperHex h.1.1.2).2] at hx
  case case4 rest h1 ih => cases rest with
    | nil => simp [pctOk] at h
    | cons a r => cases r with
      | nil => simp [pctOk] at h
      | cons b r => exact absurd rfl (h1 a b r)
  case case5 c rest _ h2 ih => rw [pctOk_cons h2] at h; rw [ih h]
  case case6 => rfl

theorem pct_pct (x : List Char) : pct (pct x) = pct x := pct_of_pctOk (pctOk_pct x)

theorem pctOk_append {a : List Char} (b : List Char) {c : Char} (hc : !isUpperHex c ∧ c ≠ '%') :
    pctOk (a ++ c :: b) = (pctOk a && pctOk b) := by
  fun_induction pctOk a
  case case1 h l rest ih => simp [pctOk, ih, Bool.and_assoc]
  case case2 rest h1 =>
    have hu : isUpperHex c = false := by simpa using hc.1
    match rest, h1 with
    | [], _ => cases b <;> simp [pctOk, hu]
    | [x], _ => simp [pctOk, hu]
    | x :: y :: r, h1 => exact absurd rfl (h1 x y r)
  case case3 x rest h1 h2 ih => simp only [List.cons_append, pctOk_cons h2, ih]
  case case4 => simp [pctOk_cons hc.2]

theorem slash_ok : (!isUpperHex '/') ∧ '/' ≠ '%' := by decide

theorem pctOk_slash (a b : List Char) : pctOk (a ++ '/' :: b) = (pctOk a && pctOk b) :=
  pctOk_append b slash_ok

/-- What `dots` has still to read of the segment it is in, and the rest. -/
def pending : Dots → List Char → List Char
  | .seg _ acc, cs => acc.reverse ++ cs
  | _, cs => cs

theorem pctOk_dots (m : Dots) (cs : List Char) (out : List (Bool × List Char))
    (h : pctOk (pending m cs)) (ho : ∀ x ∈ out, pctOk x.2) : ∀ x ∈ dots m cs out, pctOk x.2 := by
  have tail : ∀ {out : List (Bool × List Char)}, (∀ x ∈ out, pctOk x.2) → ∀ x ∈ out.tail, pctOk x.2 :=
    fun ho x hx => ho x (List.mem_of_mem_tail hx)
  have push : ∀ {out : List (Bool × List Char)} {b s}, pctOk s → (∀ x ∈ out, pctOk x.2) →
      ∀ x ∈ (b, s) :: out, pctOk x.2 := by
    intro out b s hs ho x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hs
    · exact ho x hx
  fun_induction dots m cs out <;> simp only [pending] at h
  case case1 ih | case2 ih | case10 ih | case12 ih =>
    simp only [pctOk_cons (show '.' ≠ '%' by decide), pctOk_cons (show '/' ≠ '%' by decide)] at h
    first | exact ih h ho | exact ih h (tail ho)
  case case3 | case4 | case5 => exact ho
  case case6 ih => exact ih (by simpa [pending, pctOk_cons (show '/' ≠ '%' by decide)] using h) ho
  case case11 | case14 => exact push rfl ho
  case case13 => exact push rfl (tail ho)
  case case15 ih =>
    exact ih (by simpa [pending, pctOk_cons (show '/' ≠ '%' by decide)] using h) (push rfl ho)
  case case19 ih =>
    rw [pctOk_slash, Bool.and_eq_true] at h
    exact ih h.2 (push h.1 ho)
  case case20 ih => exact ih (by simpa [pending] using h) ho
  case case21 => exact push (by simpa using h) ho
  all_goals rename_i ih; exact ih (by simpa [pending] using h) ho

theorem pctOk_intercalate (ss : List (List Char)) (h : ∀ s ∈ ss, pctOk s) :
    pctOk (['/'].intercalate ss) := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    cases ss with
    | nil => simpa using h
    | cons t ts =>
      rw [List.intercalate_cons_cons, List.append_assoc, List.singleton_append, pctOk_slash,
        h s (by simp), ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
      rfl

theorem pctOk_removeDots {p : List Char} (h : pctOk p) : pctOk (removeDotsChars p) := by
  have hs := stack_dots .start p [] rfl
  have ho := pctOk_dots .start p [] h (by simp)
  rw [removeDotsChars, join_eq_intercalate hs]
  apply pctOk_intercalate
  generalize hL : (dots .start p []).reverse = L
  have hL' : ∀ x ∈ L, pctOk x.2 := fun x hx => ho x (by rw [← hL] at hx; exact List.mem_reverse.mp hx)
  intro s hs'
  match L, hs' with
  | [], hs' => simp [segs] at hs'; subst hs'; rfl
  | (false, t) :: rest, hs' =>
    simp only [segs, List.mem_cons, List.mem_map] at hs'
    rcases hs' with rfl | ⟨x, hx, rfl⟩
    · exact hL' (false, s) (by simp)
    · exact hL' x (by simp [hx])
  | (true, t) :: rest, hs' =>
    simp only [segs, List.mem_cons, List.mem_map] at hs'
    rcases hs' with rfl | rfl | ⟨x, hx, rfl⟩
    · rfl
    · exact hL' (true, s) (by simp)
    · exact hL' x (by simp [hx])

/-- After a `/`, the output has only pieces written after a `/`, and at least one. -/
theorem dots_slash_true (m : Dots) (cs : List Char) (out : List (Bool × List Char))
    (hm : m = .slash ∨ ∃ acc, m = .seg true acc) (ho : ∀ x ∈ out, x.1 = true) :
    (∀ x ∈ dots m cs out, x.1 = true) ∧ dots m cs out ≠ [] := by
  have push : ∀ {out : List (Bool × List Char)} {s}, (∀ x ∈ out, x.1 = true) →
      ∀ x ∈ (true, s) :: out, x.1 = true := by
    intro out s ho x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · rfl
    · exact ho x hx
  have tail : ∀ {out : List (Bool × List Char)}, (∀ x ∈ out, x.1 = true) →
      ∀ x ∈ out.tail, x.1 = true := fun ho x hx => ho x (List.mem_of_mem_tail hx)
  fun_induction dots m cs out
  case case1 | case2 | case3 | case4 | case5 | case6 | case7 | case8 | case9 =>
    rcases hm with h | ⟨_, h⟩ <;> cases h
  case case11 | case14 => exact ⟨push ho, by simp⟩
  case case13 => exact ⟨push (tail ho), by simp⟩
  case case10 ih => exact ih (.inl rfl) ho
  case case12 ih => exact ih (.inl rfl) (tail ho)
  case case15 ih => exact ih (.inl rfl) (push ho)
  case case16 ih | case17 ih | case18 ih => exact ih (.inr ⟨_, rfl⟩) ho
  case case19 ih =>
    rcases hm with h | ⟨_, h⟩ <;> cases h
    exact ih (.inl rfl) (push ho)
  case case20 ih =>
    rcases hm with h | ⟨_, h⟩ <;> cases h
    exact ih (.inr ⟨_, rfl⟩) ho
  case case21 =>
    rcases hm with h | ⟨_, h⟩ <;> cases h
    exact ⟨push ho, by simp⟩

theorem head_removeDots {rest : List Char} :
    (removeDotsChars ('/' :: rest)).head? = some '/' := by
  have ⟨ht, hne⟩ := dots_slash_true .slash rest [] (.inl rfl) (by simp)
  have e : dots .start ('/' :: rest) [] = dots .slash rest [] := by rw [dots]
  rw [removeDotsChars, e, join]
  generalize dots .slash rest [] = out at ht hne
  obtain ⟨x, L, hx⟩ := List.exists_cons_of_ne_nil (List.reverse_ne_nil_iff.mpr hne)
  obtain ⟨b, t⟩ := x
  have hb : b = true := ht (b, t) (by rw [← List.mem_reverse, hx]; simp)
  subst hb
  simp [hx, piece]

theorem lowerName_spec {y : List Char} (h : pctOk y) :
    pctOk (lowerName y) ∧ lowerName (lowerName y) = lowerName y := by
  fun_induction lowerName y
  case case1 hd l rest ih =>
    simp only [pctOk, Bool.and_eq_true] at h
    have := ih h.2
    refine ⟨?_, ?_⟩
    · simp [pctOk, h.1.1.1, h.1.1.2, h.1.2, this.1]
    · simp [lowerName, this.2]
  case case2 c rest h1 ih =>
    have hc : c ≠ '%' := by
      rintro rfl
      match rest, h1 with
      | [], _ => simp [pctOk] at h
      | [x], _ => simp [pctOk] at h
      | x :: y :: r, h1 => exact h1 x y r rfl rfl
    rw [pctOk_cons hc] at h
    have := ih h
    have hl := lowerChar_ne hc
    refine ⟨by rw [pctOk_cons hl]; exact this.1, ?_⟩
    rw [lowerName, lowerChar_lowerChar, this.2]
    intros; simp_all
  case case3 => exact ⟨rfl, rfl⟩

theorem Host.normalize_normalize (h : Host) : h.normalize.normalize = h.normalize := by
  cases h with
  | ip a => rfl
  | name s =>
    have := lowerName_spec (pctOk_pct s.toList)
    simp [Host.normalize, pct_of_pctOk this.1, this.2]

theorem Authority.normalize_normalize (a : Authority) : a.normalize.normalize = a.normalize := by
  obtain ⟨userinfo, host, port⟩ := a
  cases userinfo <;> simp [Authority.normalize, Host.normalize_normalize, pct_pct]

theorem head_pct (p : List Char) : (pct p).head? = some '/' ↔ p.head? = some '/' := by
  fun_induction pct p
  case case1 hu _ => simp [(ne_of_isUnreserved hu).2]
  case case5 c rest _ _ _ => simp
  all_goals simp

theorem relativePath_normalize (u : Url) : u.normalize.relativePath = u.relativePath := by
  unfold relativePath normalize normalizePath
  by_cases hs : u.scheme.isNone <;> by_cases ha : u.authority.isNone <;> simp [hs, ha]
  · by_cases hp : u.path.toList.head? = some '/'
    · obtain ⟨rest, hr⟩ : ∃ rest, pct u.path.toList = '/' :: rest := by
        have := (head_pct u.path.toList).mpr hp
        cases e : pct u.path.toList with
        | nil => simp [e] at this
        | cons c r => simp [e] at this; exact ⟨r, by rw [this]⟩
      simp [relativePath, hs, ha, hp, hr, head_removeDots]
    · have : (pct u.path.toList).head? ≠ some '/' := fun e => hp ((head_pct _).mp e)
      have hr : u.relativePath = true := by simp [relativePath, hs, ha, hp]
      simp only [hr, ite_true]
      rw [bne_iff_ne.mpr this, bne_iff_ne.mpr hp]

theorem normalizePath_normalize (u : Url) :
    normalizePath u.normalize (normalizePath u u.path.toList) = normalizePath u u.path.toList := by
  rw [normalizePath, relativePath_normalize]
  unfold normalizePath
  split
  · simp [pct_pct]
  · have hok := pctOk_removeDots (pctOk_pct u.path.toList)
    rw [pct_of_pctOk hok]
    have := removeDots_removeDots (String.ofList (pct u.path.toList))
    simpa [removeDots] using congrArg String.toList this

/-- §6.2.2: normalizing twice is normalizing once. -/
theorem normalize_normalize (u : Url) : u.normalize.normalize = u.normalize := by
  have hp := normalizePath_normalize u
  obtain ⟨scheme, authority, path, query, fragment⟩ := u
  simp only [normalize] at hp ⊢
  rw [String.toList_ofList, hp]
  cases scheme <;> cases authority <;> cases query <;> cases fragment <;>
    simp [lower_lower, pct_pct, Authority.normalize_normalize]

/-! ### Printing and parsing -/

theorem mem_encoded {allowed : Char → Bool} {cs : List Char} (h : encoded allowed cs) {c : Char}
    (hc : c ∈ cs) : allowed c ∨ c = '%' ∨ isHex c := by
  fun_induction encoded allowed cs
  case case1 hd l rest ih =>
    simp only [Bool.and_eq_true] at h
    simp only [List.mem_cons] at hc
    rcases hc with rfl | rfl | rfl | hc
    · exact .inr (.inl rfl)
    · exact .inr (.inr h.1.1)
    · exact .inr (.inr h.1.2)
    · exact ih h.2 hc
  case case2 => simp at h
  case case3 x rest _ _ ih =>
    simp only [Bool.and_eq_true] at h
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact .inl h.1
    · exact ih h.2 hc
  case case4 => cases hc

theorem not_mem_encoded {allowed : Char → Bool} {cs : List Char} (h : encoded allowed cs) {d : Char}
    (hd : allowed d = false ∧ d ≠ '%' ∧ isHex d = false) : d ∉ cs := fun hm => by
  rcases mem_encoded h hm with e | e | e
  · rw [hd.1] at e; cases e
  · exact hd.2.1 e
  · rw [hd.2.2] at e; cases e

theorem cut_append {c : Char} {x : List Char} (y : List Char) (h : c ∉ x) :
    cut c (x ++ c :: y) = (x, some y) := by
  induction x with
  | nil => simp [cut]
  | cons a x ih =>
    have ha : a ≠ c := fun e => h (e ▸ List.mem_cons_self)
    simp [cut, ha, ih (fun hm => h (List.mem_cons_of_mem _ hm))]

theorem cut_none {c : Char} {x : List Char} (h : c ∉ x) : cut c x = (x, none) := by
  induction x with
  | nil => simp [cut]
  | cons a x ih =>
    have ha : a ≠ c := fun e => h (e ▸ List.mem_cons_self)
    simp [cut, ha, ih (fun hm => h (List.mem_cons_of_mem _ hm))]

theorem cut_opt {c : Char} {x : List Char} (y : Option String) (h : c ∉ x) :
    cut c (x ++ (y.map (c :: ·.toList)).getD []) = (x, y.map String.toList) := by
  cases y with
  | none => simpa using cut_none h
  | some y => simpa using cut_append y.toList h

theorem schemeEnd_append {s : List Char} (r : List Char) (h1 : ':' ∉ s) (h2 : '/' ∉ s) :
    schemeEnd (s ++ ':' :: r) = some (s, r) := by
  induction s with
  | nil => simp [schemeEnd]
  | cons a s ih =>
    have ha1 : a ≠ ':' := fun e => h1 (e ▸ List.mem_cons_self)
    have ha2 : a ≠ '/' := fun e => h2 (e ▸ List.mem_cons_self)
    rw [List.cons_append, schemeEnd, ih (fun hm => h1 (List.mem_cons_of_mem _ hm))
      (fun hm => h2 (List.mem_cons_of_mem _ hm))]
    · rfl
    · exact ha1
    · exact ha2

theorem schemeEnd_none {x : List Char} (h : ':' ∉ (breakSlash x).1) : schemeEnd x = none := by
  induction x with
  | nil => rfl
  | cons a x ih =>
    by_cases ha : a = '/'
    · subst ha; rfl
    · by_cases hb : a = ':'
      · subst hb; simp [breakSlash] at h
      · rw [schemeEnd, ih]
        · rfl
        · rw [breakSlash] at h
          · exact fun hm => h (List.mem_cons_of_mem _ hm)
          · exact ha
        · exact hb
        · exact ha

theorem breakSlash_append {a p : List Char} (h : '/' ∉ a) (hp : p.head?.all (· == '/')) :
    breakSlash (a ++ p) = (a, p) := by
  induction a with
  | nil =>
    cases p with
    | nil => rfl
    | cons c p =>
      simp at hp
      subst hp
      rfl
  | cons c a ih =>
    have hc : c ≠ '/' := fun e => h (e ▸ List.mem_cons_self)
    rw [List.cons_append, breakSlash, ih (fun hm => h (List.mem_cons_of_mem _ hm))]
    exact hc

/-- The characters that delimit the components after a host: none of them is in a host. -/
def Delim (c : Char) : Prop := c = '#' ∨ c = '?' ∨ c = '/' ∨ c = '@'

theorem delim_not_ip {c : Char} (hc : Delim c) : c ∉ Digits.lower ∧ c ≠ '.' ∧ c ≠ ':' ∧ c ≠ '[' ∧ c ≠ ']' := by
  rcases hc with rfl | rfl | rfl | rfl <;> decide

theorem not_mem_print4 {c : Char} (n : Nat) (hc : c ∉ Digits.lower ∧ c ≠ '.') : c ∉ Ip.print4 n :=
  fun hm => (Ip.mem_print4 hm).elim hc.1 hc.2

theorem not_mem_print6 {c : Char} (n : Fin (2 ^ 128)) (hc : c ∉ Digits.lower ∧ c ≠ '.' ∧ c ≠ ':') :
    c ∉ Ip.print6 n.val := fun hm => by
  have := Ip.mem_print (a := .v6 n) (c := c) (by simpa [Ip.print] using hm)
  rcases this with h | h | h
  · exact hc.1 h
  · exact hc.2.1 h
  · exact hc.2.2 h

theorem not_mem_host {h : Host} (hv : h.valid) {c : Char} (hc : Delim c) : c ∉ h.chars := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := delim_not_ip hc
  match h, hv with
  | .ip (.v4 n), _ => exact not_mem_print4 _ ⟨h1, h2⟩
  | .ip (.v6 n), _ =>
    simp only [Host.chars, List.cons_append, List.mem_cons, List.mem_append, not_or]
    exact ⟨h4, not_mem_print6 n ⟨h1, h2, h3⟩, h5, by simp⟩
  | .name s, hv =>
    simp only [Host.valid, Bool.and_eq_true] at hv
    exact not_mem_encoded hv.1 (by rcases hc with rfl | rfl | rfl | rfl <;> decide)

theorem not_mem_digits {p : List Char} (hp : p.all isDigit) {c : Char} (hc : isDigit c = false) :
    c ∉ p := fun hm => by
  have := List.all_eq_true.mp hp c hm
  rw [hc] at this; cases this

theorem not_mem_port {port : Option String} (hp : port.all (·.toList.all isDigit)) {c : Char}
    (hc : Delim c) : c ∉ (port.map (':' :: ·.toList)).getD [] := by
  have hd : isDigit c = false := by rcases hc with rfl | rfl | rfl | rfl <;> decide
  cases port with
  | none => simp
  | some p =>
    simp only [Option.all_some] at hp
    simp only [Option.map_some, Option.getD_some, List.mem_cons, not_or]
    exact ⟨by rcases hc with rfl | rfl | rfl | rfl <;> decide, not_mem_digits hp hd⟩

theorem not_mem_authority {a : Authority} (hv : a.valid) {c : Char} (hc : c = '#' ∨ c = '?' ∨ c = '/') :
    c ∉ a.chars := by
  obtain ⟨userinfo, host, port⟩ := a
  simp only [Authority.valid, Bool.and_eq_true] at hv
  obtain ⟨⟨hu, hh⟩, hp⟩ := hv
  have hc' : Delim c := by rcases hc with h | h | h <;> simp [Delim, h]
  simp only [Authority.chars, List.mem_append, not_or]
  refine ⟨⟨?_, not_mem_host hh hc'⟩, not_mem_port hp hc'⟩
  cases userinfo with
  | none => simp
  | some u =>
    simp only [Option.all_some] at hu
    have := not_mem_encoded hu (d := c) (by rcases hc with rfl | rfl | rfl <;> decide)
    simp only [Option.map_some, Option.getD_some, List.mem_append, List.mem_singleton, not_or]
    exact ⟨this, by rcases hc with rfl | rfl | rfl <;> decide⟩

theorem parseHost_chars {h : Host} (hv : h.valid) {port : Option String}
    (hp : port.all (·.toList.all isDigit)) :
    parseHost (h.chars ++ (port.map (':' :: ·.toList)).getD []) = some (h, port.map String.toList) := by
  match h, hv with
  | .ip (.v6 n), _ =>
    have hb : ']' ∉ Ip.print6 n.val := not_mem_print6 n (by decide)
    simp only [Host.chars, List.cons_append, List.append_assoc]
    rw [parseHost, cut_append _ hb]
    cases port with
    | none => simp [Ip.parse6_print6]
    | some p => simp [Ip.parse6_print6]
  | .ip (.v4 n), _ =>
    have hc : ':' ∉ Ip.print4 n.val := Ip.not_colon_print4 _
    have hb : '[' ∉ Ip.print4 n.val := not_mem_print4 _ (by decide)
    simp only [Host.chars]
    rw [parseHost, cut_opt _ hc]
    · simp [Ip.parse4_print4]
    · intro rest e
      cases hq : Ip.print4 n.val with
      | nil => exact absurd (Ip.dot_print4 n.val) (by rw [hq]; simp)
      | cons x xs => rw [hq] at e hb; simp at e; exact hb (by simp [e.1])
  | .name s, hv =>
    simp only [Host.valid, Bool.and_eq_true] at hv
    have hc : ':' ∉ s.toList := not_mem_encoded hv.1 (by decide)
    have hb : '[' ∉ s.toList := not_mem_encoded hv.1 (by decide)
    have h4 : Ip.parse4 s.toList = none := by simpa using hv.2
    simp only [Host.chars]
    rw [parseHost, cut_opt _ hc]
    · simp [h4]
    · intro rest e
      cases hq : s.toList with
      | nil =>
        rw [hq] at e
        cases port <;> simp at e
      | cons x xs => rw [hq] at e hb; simp at e; exact hb (by simp [e.1])

theorem parseAuthority_chars {a : Authority} (hv : a.valid) : parseAuthority a.chars = some a := by
  obtain ⟨userinfo, host, port⟩ := a
  simp only [Authority.valid, Bool.and_eq_true] at hv
  obtain ⟨⟨hu, hh⟩, hp⟩ := hv
  have hhp : '@' ∉ host.chars ++ (port.map (':' :: ·.toList)).getD [] := by
    simp only [List.mem_append, not_or]
    exact ⟨not_mem_host hh (by simp [Delim]), not_mem_port hp (by simp [Delim])⟩
  simp only [Authority.chars, List.append_assoc]
  cases userinfo with
  | none =>
    simp only [Option.map_none, Option.getD_none, List.nil_append, parseAuthority, cut_none hhp,
      parseHost_chars hh hp]
    cases port <;> simp
  | some u =>
    simp only [Option.all_some] at hu
    have hat : '@' ∉ u.toList := not_mem_encoded hu (by decide)
    simp only [Option.map_some, Option.getD_some, List.append_assoc, List.singleton_append,
      parseAuthority, cut_append _ hat, parseHost_chars hh hp]
    cases port <;> simp

theorem schemeOk_spec {s : List Char} (h : schemeOk s) :
    (∀ c, (c = '#' ∨ c = '?' ∨ c = ':' ∨ c = '/') → c ∉ s) ∧ lower s = s := by
  match s, h with
  | c :: rest, h =>
    simp only [schemeOk, Bool.and_eq_true, beq_iff_eq] at h
    refine ⟨fun d hd hm => ?_, h.2⟩
    have := List.all_eq_true.mp h.1.2 d hm
    rcases hd with rfl | rfl | rfl | rfl <;> simp [isSchemeChar, isAlpha, isDigit] at this

theorem pathChars_eq {u : Url} (h : u.pathFits) : u.pathChars = u.path.toList := by
  unfold pathChars
  split
  · rename_i hc
    simp only [pathFits] at h
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, beq_iff_eq] at hc
    rw [hc.1] at h
    simp [hc.2] at h
  · rfl

theorem not_mem_schemePart {scheme : Option String} (hs : scheme.all (schemeOk ·.toList))
    {c : Char} (hc : c = '#' ∨ c = '?') : c ∉ (scheme.map (·.toList ++ [':'])).getD [] := by
  cases scheme with
  | none => simp
  | some s =>
    simp only [Option.all_some] at hs
    simp only [Option.map_some, Option.getD_some, List.mem_append, List.mem_singleton, not_or]
    exact ⟨(schemeOk_spec hs).1 c (by rcases hc with h | h <;> simp [h]),
      by rcases hc with rfl | rfl <;> decide⟩

theorem not_mem_authorityPart {authority : Option Authority} (ha : authority.all Authority.valid)
    {c : Char} (hc : c = '#' ∨ c = '?') : c ∉ (authority.map ('/' :: '/' :: ·.chars)).getD [] := by
  cases authority with
  | none => simp
  | some a =>
    simp only [Option.all_some] at ha
    simp only [Option.map_some, Option.getD_some, List.mem_cons, not_or]
    exact ⟨by rcases hc with rfl | rfl <;> decide, by rcases hc with rfl | rfl <;> decide,
      not_mem_authority ha (by rcases hc with h | h <;> simp [h])⟩

theorem parseRaw_chars {u : Url} (hv : u.valid) : parseRaw u.chars = some u := by
  have hfit : u.pathFits := by simp only [valid, Bool.and_eq_true] at hv; exact hv.2
  have hpc := pathChars_eq hfit
  obtain ⟨scheme, authority, path, query, fragment⟩ := u
  simp only [valid, Bool.and_eq_true] at hv
  obtain ⟨⟨⟨⟨⟨hs, ha⟩, hp⟩, hq⟩, hf⟩, -⟩ := hv
  simp only [chars, hpc]
  have hF : '#' ∉ (scheme.map (·.toList ++ [':'])).getD [] ++ (authority.map ('/' :: '/' :: ·.chars)).getD []
      ++ path.toList ++ (query.map ('?' :: ·.toList)).getD [] := by
    simp only [List.mem_append, not_or]
    refine ⟨⟨⟨not_mem_schemePart hs (.inl rfl), not_mem_authorityPart ha (.inl rfl)⟩,
      not_mem_encoded hp (by decide)⟩, ?_⟩
    cases query with
    | none => simp
    | some q =>
      simp only [Option.all_some] at hq
      simp only [Option.map_some, Option.getD_some, List.mem_cons, not_or]
      exact ⟨by decide, not_mem_encoded hq (by decide)⟩
  have hQ : '?' ∉ (scheme.map (·.toList ++ [':'])).getD [] ++ (authority.map ('/' :: '/' :: ·.chars)).getD []
      ++ path.toList := by
    simp only [List.mem_append, not_or]
    exact ⟨⟨not_mem_schemePart hs (.inr rfl), not_mem_authorityPart ha (.inr rfl)⟩,
      not_mem_encoded hp (by decide)⟩
  simp only [parseRaw, cut_opt _ hF, cut_opt _ hQ]
  simp only [pathFits] at hfit
  cases scheme with
  | some sc =>
    simp only [Option.all_some] at hs
    obtain ⟨hsc, hlow⟩ := schemeOk_spec hs
    cases authority with
    | some a =>
      simp only [Option.all_some] at ha
      simp only [] at hfit
      have e := schemeEnd_append (s := sc.toList) ('/' :: '/' :: (a.chars ++ path.toList))
        (hsc ':' (by simp)) (hsc '/' (by simp))
      simp only [Option.map_some, Option.getD_some, List.append_assoc, List.cons_append]
      have hb := breakSlash_append (not_mem_authority ha (by simp)) hfit
      cases query <;> cases fragment <;> simp [Function.comp_def, hlow, e, hb, parseAuthority_chars ha]
    | none =>
      simp only [] at hfit
      have e := schemeEnd_append (s := sc.toList) path.toList (hsc ':' (by simp)) (hsc '/' (by simp))
      simp only [Option.map_some, Option.map_none, Option.getD_some, Option.getD_none,
        List.append_assoc, List.singleton_append, e]
      split
      · rename_i heq
        simp only [Bool.and_eq_true, bne_iff_ne] at hfit
        exact absurd (by simp [heq]) hfit.1
      · cases query <;> cases fragment <;> simp [hlow]
  | none =>
    cases authority with
    | some a =>
      simp only [Option.all_some] at ha
      simp only [] at hfit
      simp only [Option.map_some, Option.map_none, Option.getD_some, Option.getD_none,
        List.nil_append, List.cons_append, schemeEnd,
        breakSlash_append (not_mem_authority ha (by simp)) hfit, parseAuthority_chars ha,
        Option.map_some]
      cases query <;> cases fragment <;> simp
    | none =>
      simp only [Option.isSome_none, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true',
        List.contains_eq_mem, decide_eq_false_iff_not, bne_iff_ne] at hfit
      simp only [Option.map_none, Option.getD_none, List.nil_append, schemeEnd_none hfit.2]
      split
      · rename_i heq
        exact absurd (by simp [heq]) hfit.1
      · cases query <;> cases fragment <;> simp

theorem parse_print_of_valid {u : Url} (h : u.valid) : parse u.print = some u := by
  simp [parse, print, parseRaw_chars h, h]

theorem valid_of_parse {s : String} {u : Url} (h : parse s = some u) : u.valid := by
  simp only [parse, Option.filter_eq_some_iff] at h
  exact h.2

/-- What `parse` reads, `print` writes so that it reads back the same. -/
theorem parse_print {s : String} {u : Url} (h : parse s = some u) : parse u.print = some u :=
  parse_print_of_valid (valid_of_parse h)

end Lanes.Url
