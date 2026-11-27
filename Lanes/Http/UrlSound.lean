/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Http.Url

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

end Lanes.Url
