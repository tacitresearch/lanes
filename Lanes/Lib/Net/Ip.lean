/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Lib.Encoding.Digits
public import Lanes.Proof.List.Basic

/-!
IP addresses and prefixes as Go's `net/netip` reads and writes them: IPv4 in dotted decimal with
no leading zeros, IPv6 in the text forms of RFC 4291 §2.2 (hex groups of one to four digits in
either case, one `::`, an IPv4 address in place of the last two groups), CIDR prefixes
(RFC 4632), and which addresses are the host's own (`Addr.isLoopback`). Zones (`fe80::1%eth0`)
are refused.

`print` writes RFC 5952: lowercase, no leading zeros (`Digits.head_toChars`), `::` for the
leftmost longest run of two or more zero groups (`longestZeroRun_some`, `longestZeroRun_none`),
and an IPv4-mapped address as `::ffff:a.b.c.d` (§5). `parse (print a) = some a`.
-/

@[expose] public section

namespace Lanes.Ip

open Digits

inductive Addr where
  | v4 (n : Fin (2 ^ 32))
  | v6 (n : Fin (2 ^ 128))
  deriving DecidableEq, Repr

def octet? (cs : List Char) : Option Nat :=
  if cs = [] ∨ 3 < cs.length ∨ (cs.head? = some '0' ∧ 1 < cs.length) then none
  else (ofChars? 10 cs).filter (· < 256)

def parse4 (cs : List Char) : Option (Fin (2 ^ 32)) := do
  let fields := cs.splitOn '.'
  if fields.length ≠ 4 then none
  let n := join 256 (← fields.mapM octet?)
  if h : n < 2 ^ 32 then some ⟨n, h⟩ else none

def print4 (n : Nat) : List Char := ['.'].intercalate ((split 256 4 n).map (toChars 10))

def hexGroup? (cs : List Char) : Option Nat :=
  if cs = [] ∨ 4 < cs.length then none else ofChars? 16 cs

/-- Hex groups, the last of which may be an IPv4 address standing for two. -/
def groups? : List (List Char) → Option (List Nat)
  | [] => some []
  | [f] =>
    if '.' ∈ f then (parse4 f).map fun x => [x.val / 65536, x.val % 65536]
    else (hexGroup? f).map ([·])
  | f :: g :: rest => do return (← hexGroup? f) :: (← groups? (g :: rest))

/-- The groups around a `::`, which stands for at least one zero group. -/
def expand (l r : List Nat) : Option (List Nat) :=
  if l.length + r.length ≤ 7 then some (l ++ List.replicate (8 - l.length - r.length) 0 ++ r)
  else none

/-- The fields between colons: an empty one is where `::` was, two of them at either end. -/
def fields? (fs : List (List Char)) : Option (List Nat) :=
  match fs.splitOn [] with
  | [all] => do
    let g ← groups? all
    if g.length = 8 then some g else none
  | [l, r] => if l ≠ [] ∧ r ≠ [] then do expand (← l.mapM hexGroup?) (← groups? r) else none
  | [[], [], r] => if r ≠ [] then do expand [] (← groups? r) else none
  | [l, [], []] => if l ≠ [] then do expand (← l.mapM hexGroup?) [] else none
  | [[], [], [], []] => expand [] []
  | _ => none

def parse6 (cs : List Char) : Option (Fin (2 ^ 128)) := do
  let n := join 65536 (← fields? (cs.splitOn ':'))
  if h : n < 2 ^ 128 then some ⟨n, h⟩ else none

def parse (s : String) : Option Addr :=
  if ':' ∈ s.toList then (parse6 s.toList).map .v6 else (parse4 s.toList).map .v4

/-- The number of zero groups from the start of `g`. -/
def zeroRun : List Nat → Nat
  | 0 :: rest => zeroRun rest + 1
  | _ => 0

def runAt (g : List Nat) (i : Nat) : Nat := zeroRun (g.drop i)

/-- Where the longest run of two or more zero groups starts and how long it is; the leftmost
of the longest (RFC 5952 §4.2). -/
def longestZeroRun (g : List Nat) : Option (Nat × Nat) :=
  (List.range g.length).foldl (init := none) fun best i =>
    if 2 ≤ runAt g i ∧ best.all (·.2 < runAt g i) then some (i, runAt g i) else best

def withEllipsis : List (List Char) → List (List Char) → List (List Char)
  | [], [] => [[], [], []]
  | [], r => [] :: [] :: r
  | l, [] => l ++ [[], []]
  | l, r => l ++ [] :: r

def hexFields (g : List Nat) : List (List Char) := g.map (toChars 16)

def fields (g : List Nat) : List (List Char) :=
  match longestZeroRun g with
  | none => hexFields g
  | some (i, n) => withEllipsis (hexFields (g.take i)) (hexFields (g.drop (i + n)))

def mappedPrefix : List Nat := [0, 0, 0, 0, 0, 0xffff]

def print6 (n : Nat) : List Char :=
  if (split 65536 8 n).take 6 = mappedPrefix then
    [':', ':', 'f', 'f', 'f', 'f', ':'] ++ print4 (n % 2 ^ 32)
  else [':'].intercalate (fields (split 65536 8 n))

def print : Addr → String
  | .v4 n => String.ofList (print4 n.val)
  | .v6 n => String.ofList (print6 n.val)

/-! ### The run `::` stands for -/

theorem zeroRun_spec (l : List Nat) :
    l = List.replicate (zeroRun l) 0 ++ l.drop (zeroRun l) := by
  match l with
  | [] => rfl
  | 0 :: rest =>
    simp only [zeroRun, List.replicate_succ, List.cons_append, List.drop_succ_cons]
    exact congrArg _ (zeroRun_spec rest)
  | (_ + 1) :: _ => rfl

theorem zeroRun_le (l : List Nat) : zeroRun l ≤ l.length := by
  match l with
  | [] => exact Nat.le_refl _
  | 0 :: rest => simpa [zeroRun] using zeroRun_le rest
  | (_ + 1) :: _ => exact Nat.zero_le _

theorem runAt_spec (g : List Nat) (i : Nat) :
    g = g.take i ++ List.replicate (runAt g i) 0 ++ g.drop (i + runAt g i) := by
  conv => lhs; rw [← List.take_append_drop i g, zeroRun_spec (g.drop i)]
  simp [runAt, List.drop_drop, List.append_assoc]

theorem runAt_le (g : List Nat) (i : Nat) : i + runAt g i ≤ g.length ∨ runAt g i = 0 := by
  have := zeroRun_le (g.drop i)
  simp only [List.length_drop] at this
  unfold runAt; omega

/-- What `longestZeroRun` has found after looking at the first `k` positions. -/
def Found (g : List Nat) (k : Nat) : Option (Nat × Nat) → Prop
  | none => ∀ j < k, runAt g j < 2
  | some (i, n) => i < k ∧ runAt g i = n ∧ 2 ≤ n ∧ (∀ j < k, runAt g j ≤ n) ∧ ∀ j < i, runAt g j < n

theorem found_step {g : List Nat} {k : Nat} {best : Option (Nat × Nat)} (ih : Found g k best) :
    Found g (k + 1)
      (if 2 ≤ runAt g k ∧ best.all (·.2 < runAt g k) then some (k, runAt g k) else best) := by
  have last : ∀ j, j < k + 1 → j < k ∨ j = k := fun j hj => by omega
  cases best with
  | none =>
    simp only [Option.all_none, and_true]
    split
    · rename_i h
      refine ⟨by omega, rfl, h, fun j hj => ?_, fun j hj => ?_⟩
      · rcases last j hj with hj | rfl
        · have := ih j hj; omega
        · exact Nat.le_refl _
      · have := ih j hj; omega
    · rename_i h
      intro j hj
      rcases last j hj with hj | rfl
      · exact ih j hj
      · omega
  | some p =>
    obtain ⟨i, n⟩ := p
    obtain ⟨hik, hi, hn, hmax, hleft⟩ := ih
    simp only [Option.all_some, decide_eq_true_eq]
    split
    · rename_i h
      refine ⟨by omega, rfl, h.1, fun j hj => ?_, fun j hj => ?_⟩
      · rcases last j hj with hj | rfl
        · have := hmax j hj; omega
        · exact Nat.le_refl _
      · have := hmax j hj; omega
    · rename_i h
      refine ⟨by omega, hi, hn, fun j hj => ?_, hleft⟩
      rcases last j hj with hj | rfl
      · exact hmax j hj
      · by_cases h2 : 2 ≤ runAt g j
        · have : ¬ n < runAt g j := fun hlt => h ⟨h2, hlt⟩
          omega
        · omega

theorem found_range (g : List Nat) (k : Nat) :
    Found g k ((List.range k).foldl (init := none) fun best i =>
      if 2 ≤ runAt g i ∧ best.all (·.2 < runAt g i) then some (i, runAt g i) else best) := by
  induction k with
  | zero => intro j hj; omega
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact found_step ih

theorem runAt_of_length_le {g : List Nat} {j : Nat} (h : g.length ≤ j) : runAt g j = 0 := by
  simp [runAt, List.drop_eq_nil_of_le h, zeroRun]

/-- RFC 5952 §4.2.2 and §4.2.3: the run chosen is a longest one, of two groups at least, and no
run as long starts before it. -/
theorem longestZeroRun_some {g : List Nat} {i n : Nat} (h : longestZeroRun g = some (i, n)) :
    runAt g i = n ∧ 2 ≤ n ∧ (∀ j, runAt g j ≤ n) ∧ ∀ j < i, runAt g j < n := by
  have := found_range g g.length
  rw [← longestZeroRun, h] at this
  obtain ⟨_, hi, hn, hmax, hleft⟩ := this
  refine ⟨hi, hn, fun j => ?_, hleft⟩
  by_cases hj : j < g.length
  · exact hmax j hj
  · rw [runAt_of_length_le (by omega)]; omega

/-- RFC 5952 §4.2.2: a single zero group is not shortened to `::`. -/
theorem longestZeroRun_none {g : List Nat} (h : longestZeroRun g = none) : ∀ j, runAt g j < 2 := by
  have := found_range g g.length
  rw [← longestZeroRun, h] at this
  intro j
  by_cases hj : j < g.length
  · exact this j hj
  · rw [runAt_of_length_le (by omega)]; omega

/-! ### Reading back what `print` writes -/

theorem mem_lower_ne {c : Char} (h : c ∈ lower) : c ≠ ':' ∧ c ≠ '.' ∧ c ≠ '/' := by
  revert c h; decide

theorem octet?_toChars {d : Nat} (hd : d < 256) : octet? (toChars 10 d) = some d := by
  have hne := toChars_ne_nil 10 d
  have hlen := length_toChars_le (b := 10) (k := 3) (by omega) (by omega)
    (show d < 10 ^ 3 by omega)
  unfold octet?
  rw [ite_eq_right]
  · simp [ofChars?_toChars (b := 10) (by omega) (by omega), hd]
  · rintro (h | h | ⟨h0, h1⟩)
    · exact hne h
    · omega
    · have := head_toChars (b := 10) (by omega) (by omega) h0
      subst this
      simp [toChars, digits] at h1

theorem parse4_print4 (x : Fin (2 ^ 32)) : parse4 (print4 x.val) = some x := by
  have hfields : (print4 x.val).splitOn '.' = (split 256 4 x.val).map (toChars 10) := by
    apply List.splitOn_intercalate
    · intro l hl hdot
      simp only [List.mem_map] at hl
      obtain ⟨d, _, rfl⟩ := hl
      exact (mem_lower_ne (mem_toChars (by omega) (by omega) hdot)).2.1 rfl
    · simp [length_split, ← List.length_eq_zero_iff]
  have hoct : ((split 256 4 x.val).map (toChars 10)).mapM octet? = some (split 256 4 x.val) := by
    rw [List.mapM_map]
    have := mapM_some (l := split 256 4 x.val) (f := octet? ∘ toChars 10) (g := id)
      fun d hd => octet?_toChars (lt_of_mem_split (by omega) hd)
    simpa using this
  have hj : join 256 (split 256 4 x.val) = x.val := by
    rw [join_split]; exact Nat.mod_eq_of_lt (by have := x.isLt; omega)
  simp only [parse4, hfields, List.length_map, length_split, hoct]
  simp only [ne_eq, not_true_eq_false, ite_false, Option.bind_eq_bind, Option.bind_some]
  rw [dite_eq_left (by rw [hj]; exact x.isLt)]
  exact congrArg some (Fin.ext hj)

theorem not_colon_print4 (n : Nat) : ':' ∉ print4 n := by
  intro h
  rcases mem_intercalate h with h | ⟨l, hl, hc⟩
  · simp at h
  · simp only [List.mem_map] at hl
    obtain ⟨d, _, rfl⟩ := hl
    exact (mem_lower_ne (mem_toChars (by omega) (by omega) hc)).1 rfl

theorem dot_print4 (n : Nat) : '.' ∈ print4 n :=
  mem_intercalate_of_two_le (by simp) (by simp [length_split])

theorem hexGroup?_toChars {d : Nat} (hd : d < 65536) : hexGroup? (toChars 16 d) = some d := by
  have hlen := length_toChars_le (b := 16) (k := 4) (by omega) (by omega) (show d < 16 ^ 4 by omega)
  unfold hexGroup?
  rw [ite_eq_right fun h => h.elim (toChars_ne_nil 16 d) (by omega)]
  exact ofChars?_toChars (by omega) (by omega) d

theorem not_dot_toChars (d : Nat) : '.' ∉ toChars 16 d :=
  fun h => (mem_lower_ne (mem_toChars (by omega) (by omega) h)).2.1 rfl

theorem groups?_hexFields {g : List Nat} (h : ∀ d ∈ g, d < 65536) : groups? (hexFields g) = some g := by
  match g with
  | [] => rfl
  | [d] => simp [hexFields, groups?, not_dot_toChars, hexGroup?_toChars (h d (by simp))]
  | d :: e :: rest =>
    have ih := groups?_hexFields (g := e :: rest) fun x hx => h x (by simp [hx])
    simp only [hexFields, List.map_cons] at ih ⊢
    simp [groups?, ih, hexGroup?_toChars (h d (by simp))]

theorem mapM_hexFields {g : List Nat} (h : ∀ d ∈ g, d < 65536) :
    (hexFields g).mapM hexGroup? = some g := by
  rw [hexFields, List.mapM_map]
  simpa using mapM_some (l := g) (f := hexGroup? ∘ toChars 16) (g := id)
    fun d hd => hexGroup?_toChars (h d hd)

theorem hexFields_ne_nil (g : List Nat) : ∀ f ∈ hexFields g, f ≠ [] := by
  intro f hf
  simp only [hexFields, List.mem_map] at hf
  obtain ⟨d, _, rfl⟩ := hf
  exact toChars_ne_nil 16 d

theorem nil_not_mem_hexFields (g : List Nat) : [] ∉ hexFields g :=
  fun h => hexFields_ne_nil g [] h rfl

theorem splitOn_colon {fs : List (List Char)} (h : ∀ f ∈ fs, ':' ∉ f) (hne : fs ≠ []) :
    ([':'].intercalate fs).splitOn ':' = fs :=
  List.splitOn_intercalate ':' h hne

theorem mem_withEllipsis {l r : List (List Char)} {f : List Char} (h : f ∈ withEllipsis l r) :
    f = [] ∨ f ∈ l ∨ f ∈ r := by
  have sub : withEllipsis l r ⊆ [] :: (l ++ r) := by
    intro x hx
    rcases l with _ | ⟨a, l⟩ <;> rcases r with _ | ⟨b, r⟩ <;>
      simp only [withEllipsis, List.mem_cons, List.mem_append, List.not_mem_nil, List.nil_append,
        List.append_nil, List.cons_append, or_false] at hx ⊢ <;>
      (try (rcases hx with hx | hx | hx | hx <;> simp [hx])) <;>
      (try (rcases hx with hx | hx | hx <;> exact hx))
  simpa using sub h

theorem withEllipsis_ne_nil (l r : List (List Char)) : withEllipsis l r ≠ [] := by
  unfold withEllipsis; split <;> simp

theorem two_le_length_withEllipsis (l r : List (List Char)) : 2 ≤ (withEllipsis l r).length := by
  rcases l with _ | ⟨a, l⟩ <;> rcases r with _ | ⟨b, r⟩ <;> simp [withEllipsis] <;> omega

theorem fields?_withEllipsis {l r : List (List Char)} (hl : [] ∉ l) (hr : [] ∉ r) :
    fields? (withEllipsis l r) =
      (l.mapM hexGroup?).bind fun gl => (groups? r).bind fun gr => expand gl gr := by
  have split : ∀ segs : List (List (List Char)), (∀ s ∈ segs, [] ∉ s) → segs ≠ [] →
      ([[]].intercalate segs).splitOn [] = segs :=
    fun segs h hne => List.splitOn_intercalate [] h hne
  have nonEmpty : ∀ {f : List Char} {l : List (List Char)}, [] ∉ f :: l → ¬ f = [] ∧ [] ∉ l :=
    fun h => ⟨fun hf => h (hf ▸ List.mem_cons_self), fun hl => h (List.mem_cons_of_mem _ hl)⟩
  match l, r with
  | [], [] =>
    have := split [[], [], [], []] (by simp) (by simp)
    rw [show withEllipsis [] [] = [[]].intercalate [[], [], [], []] by
      simp [withEllipsis, List.intercalate_cons_cons], fields?, this]
    rfl
  | [], f :: r =>
    have := split [[], [], f :: r] (by simpa using nonEmpty hr) (by simp)
    rw [show withEllipsis [] (f :: r) = [[]].intercalate [[], [], f :: r] by
      simp [withEllipsis, List.intercalate_cons_cons], fields?, this]
    simp
  | f :: l, [] =>
    have := split [f :: l, [], []] (by simpa using nonEmpty hl) (by simp)
    rw [show withEllipsis (f :: l) [] = [[]].intercalate [f :: l, [], []] by
      simp [withEllipsis, List.intercalate_cons_cons], fields?, this]
    simp [groups?]
  | f :: l, g :: r =>
    have := split [f :: l, g :: r] (by simpa using ⟨nonEmpty hl, nonEmpty hr⟩) (by simp)
    rw [show withEllipsis (f :: l) (g :: r) = [[]].intercalate [f :: l, g :: r] by
      simp [withEllipsis, List.intercalate_cons_cons], fields?, this]
    simp

theorem expand_run {g : List Nat} {i n : Nat} (hg : g.length = 8) (hn : 1 ≤ n) (hi : i + n ≤ 8)
    (hrun : g = g.take i ++ List.replicate n 0 ++ g.drop (i + n)) :
    expand (g.take i) (g.drop (i + n)) = some g := by
  unfold expand
  rw [ite_eq_left (by simp [hg]; omega)]
  have : 8 - (g.take i).length - (g.drop (i + n)).length = n := by simp [hg]; omega
  rw [this, ← hrun]

theorem split_lt (n : Nat) : ∀ d ∈ split 65536 8 n, d < 65536 :=
  fun _ hd => lt_of_mem_split (by omega) hd

theorem fields?_fields (n : Nat) :
    fields? (([':'].intercalate (fields (split 65536 8 n))).splitOn ':') = some (split 65536 8 n) := by
  have hg := length_split 65536 8 n
  have hlt := split_lt n
  have noColon : ∀ g, ∀ f ∈ hexFields g, ':' ∉ f := fun g f hf hc => by
    simp only [hexFields, List.mem_map] at hf
    obtain ⟨d, _, rfl⟩ := hf
    exact (mem_lower_ne (mem_toChars (by omega) (by omega) hc)).1 rfl
  unfold fields
  split
  · rename_i hnone
    rw [splitOn_colon (noColon _) (by simp [hexFields, ← List.length_eq_zero_iff, hg])]
    have hseg : (hexFields (split 65536 8 n)).splitOn [] = [hexFields (split 65536 8 n)] :=
      List.splitOn_intercalate (ls := [hexFields (split 65536 8 n)]) []
        (by simpa using nil_not_mem_hexFields _) (by simp)
    simp [fields?, hseg, groups?_hexFields hlt, hg]
  · rename_i i k hsome
    obtain ⟨hrun, hk, _, _⟩ := longestZeroRun_some hsome
    have hle : i + k ≤ 8 := by have := runAt_le (split 65536 8 n) i; omega
    have hfs : ∀ f ∈ withEllipsis (hexFields ((split 65536 8 n).take i))
        (hexFields ((split 65536 8 n).drop (i + k))), ':' ∉ f := fun f hf => by
      rcases mem_withEllipsis hf with rfl | hf | hf
      · exact List.not_mem_nil
      · exact noColon _ f hf
      · exact noColon _ f hf
    rw [splitOn_colon hfs (withEllipsis_ne_nil _ _),
      fields?_withEllipsis (nil_not_mem_hexFields _) (nil_not_mem_hexFields _),
      mapM_hexFields fun d hd => hlt d (List.mem_of_mem_take hd),
      groups?_hexFields fun d hd => hlt d (List.mem_of_mem_drop hd)]
    exact expand_run hg (by omega) hle (hrun ▸ runAt_spec _ i)

theorem split_mapped {x : Nat} (h : (split 65536 8 x).take 6 = mappedPrefix) :
    split 65536 8 x = mappedPrefix ++ [x / 65536 % 65536, x % 65536] := by
  have hs := split_add 65536 6 2 x
  simp only [Nat.reduceAdd] at hs
  rw [hs, List.take_left' (length_split _ _ _)] at h
  rw [hs, h]
  simp [split]

theorem parse6_print6 (x : Fin (2 ^ 128)) : parse6 (print6 x.val) = some x := by
  have hj : join 65536 (split 65536 8 x.val) = x.val := by
    rw [join_split]; exact Nat.mod_eq_of_lt (by have := x.isLt; omega)
  have finish : ∀ g, fields? ((print6 x.val).splitOn ':') = some g → g = split 65536 8 x.val →
      parse6 (print6 x.val) = some x := by
    rintro g hg rfl
    simp only [parse6, hg, Option.bind_eq_bind, Option.bind_some]
    rw [dite_eq_left (by rw [hj]; exact x.isLt)]
    exact congrArg some (Fin.ext hj)
  by_cases hm : (split 65536 8 x.val).take 6 = mappedPrefix
  · let low : Fin (2 ^ 32) := ⟨x.val % 2 ^ 32, Nat.mod_lt _ (by decide)⟩
    have htext : [':', ':', 'f', 'f', 'f', 'f', ':'] ++ print4 (x.val % 2 ^ 32)
        = [':'].intercalate (withEllipsis [] [['f', 'f', 'f', 'f'], print4 low.val]) := by
      simp [withEllipsis, List.intercalate_cons_cons, low]
    have hcolon : ∀ f ∈ withEllipsis [] [['f', 'f', 'f', 'f'], print4 low.val], ':' ∉ f := by
      intro f hf
      simp only [withEllipsis, List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl
      · exact List.not_mem_nil
      · exact List.not_mem_nil
      · decide
      · exact not_colon_print4 _
    have hnil : [] ∉ [['f', 'f', 'f', 'f'], print4 low.val] := by
      have : print4 low.val ≠ [] := fun h => by have := dot_print4 low.val; simp [h] at this
      simp [this]
    refine finish _ ?_ (split_mapped hm).symm
    rw [print6, ite_eq_left hm, htext, splitOn_colon hcolon (withEllipsis_ne_nil _ _), fields?_withEllipsis (by simp) hnil]
    simp only [List.mapM_nil, groups?, dot_print4, ite_true, parse4_print4,
      show hexGroup? ['f', 'f', 'f', 'f'] = some 65535 by decide]
    simp only [pure, Option.bind_eq_bind, Option.bind_some, Option.map_some, expand, mappedPrefix,
      low, List.length_nil, List.length_cons]
    rw [ite_eq_left (by decide)]
    simp only [Option.some.injEq, Nat.reduceSub, Nat.reducePow, List.replicate, List.nil_append,
      List.cons_append, List.cons.injEq, true_and, and_true]
    constructor <;> omega
  · exact finish _ (by rw [print6, ite_eq_right hm]; exact fields?_fields x.val) rfl

theorem colon_print6 (n : Nat) : ':' ∈ print6 n := by
  unfold print6
  split
  · simp
  · apply mem_intercalate_of_two_le (by simp)
    unfold fields
    split
    · simp [hexFields, length_split]
    · exact two_le_length_withEllipsis _ _

theorem parse_print (a : Addr) : parse (print a) = some a := by
  cases a with
  | v4 n => simp [parse, print, not_colon_print4, parse4_print4]
  | v6 n => simp [parse, print, colon_print6, parse6_print6]

/-! ### Prefixes (RFC 4632) -/

def Addr.width : Addr → Nat
  | .v4 _ => 32
  | .v6 _ => 128

def Addr.toNat : Addr → Nat
  | .v4 n => n.val
  | .v6 n => n.val

/-- The first `bits` bits of `n`, out of `w`, and zeros after them. -/
def mask (w bits n : Nat) : Nat := n / 2 ^ (w - bits) * 2 ^ (w - bits)

theorem mask_le (w bits n : Nat) : mask w bits n ≤ n := Nat.div_mul_le_self n _

theorem mask_mask (w bits n : Nat) : mask w bits (mask w bits n) = mask w bits n := by
  simp [mask, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

def Addr.masked (a : Addr) (bits : Nat) : Addr :=
  match a with
  | .v4 n => .v4 ⟨mask 32 bits n, Nat.lt_of_le_of_lt (mask_le ..) n.isLt⟩
  | .v6 n => .v6 ⟨mask 128 bits n, Nat.lt_of_le_of_lt (mask_le ..) n.isLt⟩

theorem width_masked (a : Addr) (bits : Nat) : (a.masked bits).width = a.width := by
  cases a <;> rfl

theorem masked_masked (a : Addr) (bits : Nat) : (a.masked bits).masked bits = a.masked bits := by
  cases a <;> simp [Addr.masked, mask_mask]

structure Prefix where
  addr : Addr
  bits : Nat
  le : bits ≤ addr.width
  deriving DecidableEq

def Prefix.masked (p : Prefix) : Prefix := ⟨p.addr.masked p.bits, p.bits, by
  rw [width_masked]; exact p.le⟩

def Prefix.contains (p : Prefix) (a : Addr) : Bool :=
  a.width == p.addr.width && a.masked p.bits == p.addr.masked p.bits

theorem Prefix.masked_masked (p : Prefix) : p.masked.masked = p.masked := by
  simp [Prefix.masked, Ip.masked_masked]

theorem Prefix.contains_masked (p : Prefix) (a : Addr) : p.masked.contains a = p.contains a := by
  simp [Prefix.contains, Prefix.masked, width_masked, Ip.masked_masked]

theorem Prefix.contains_addr (p : Prefix) : p.contains p.addr := by
  simp [Prefix.contains]

private theorem mask_eq_iff {w bits m n : Nat} : mask w bits m = mask w bits n ↔
    m / 2 ^ (w - bits) = n / 2 ^ (w - bits) :=
  ⟨fun h => Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos _) h, fun h => by simp [mask, h]⟩

/-- An address is in a prefix when it is of the same family and its first `bits` bits are the
prefix's. -/
theorem Prefix.contains_iff (p : Prefix) (a : Addr) : p.contains a ↔
    a.width = p.addr.width ∧ a.toNat / 2 ^ (a.width - p.bits) = p.addr.toNat / 2 ^ (a.width - p.bits) := by
  obtain ⟨b, bits, le⟩ := p
  cases a <;> cases b <;> simp [Prefix.contains, Addr.width, Addr.masked, Addr.toNat, Fin.ext_iff,
    mask_eq_iff]

def Prefix.print (p : Prefix) : String :=
  Ip.print p.addr ++ "/" ++ String.ofList (toChars 10 p.bits)

def decimal? (cs : List Char) : Option Nat :=
  if cs = [] ∨ (cs.head? = some '0' ∧ 1 < cs.length) then none else ofChars? 10 cs

def Prefix.parse (s : String) : Option Prefix :=
  match s.toList.splitOn '/' with
  | [a, b] => do
    let addr ← Ip.parse (String.ofList a)
    let bits ← decimal? b
    if h : bits ≤ addr.width then some ⟨addr, bits, h⟩ else none
  | _ => none

theorem mem_print4 {n : Nat} {c : Char} (h : c ∈ print4 n) : c ∈ lower ∨ c = '.' := by
  rcases mem_intercalate h with h | ⟨l, hl, hc⟩
  · exact .inr (by simpa using h)
  · simp only [List.mem_map] at hl
    obtain ⟨d, _, rfl⟩ := hl
    exact .inl (mem_toChars (by omega) (by omega) hc)

theorem mem_print {a : Addr} {c : Char} (h : c ∈ (print a).toList) :
    c ∈ lower ∨ c = '.' ∨ c = ':' := by
  have hex : ∀ {g f}, f ∈ hexFields g → c ∈ f → c ∈ lower := fun hf hc => by
    simp only [hexFields, List.mem_map] at hf
    obtain ⟨d, _, rfl⟩ := hf
    exact mem_toChars (by omega) (by omega) hc
  cases a with
  | v4 n =>
    simp only [print, String.toList_ofList] at h
    exact (mem_print4 h).elim .inl (.inr ∘ .inl)
  | v6 n =>
    simp only [print, String.toList_ofList, print6] at h
    split at h
    · simp only [List.cons_append, List.mem_cons, List.nil_append] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | h
      all_goals first | exact (mem_print4 h).elim .inl (.inr ∘ .inl) | simp [lower]
    · rcases mem_intercalate h with h | ⟨f, hf, hc⟩
      · exact .inr (.inr (by simpa using h))
      · unfold fields at hf
        split at hf
        · exact .inl (hex hf hc)
        · rcases mem_withEllipsis hf with rfl | hf | hf
          · cases hc
          · exact .inl (hex hf hc)
          · exact .inl (hex hf hc)

theorem decimal?_toChars (n : Nat) : decimal? (toChars 10 n) = some n := by
  unfold decimal?
  rw [ite_eq_right]
  · exact ofChars?_toChars (by omega) (by omega) n
  · rintro (h | ⟨h0, h1⟩)
    · exact toChars_ne_nil 10 n h
    · have := head_toChars (b := 10) (by omega) (by omega) h0
      subst this
      simp [toChars, digits] at h1

theorem Prefix.parse_print (p : Prefix) : Prefix.parse p.print = some p := by
  obtain ⟨a, bits, le⟩ := p
  have hsplit : (Prefix.print ⟨a, bits, le⟩).toList.splitOn '/' = [(Ip.print a).toList, toChars 10 bits] := by
    rw [show (Prefix.print ⟨a, bits, le⟩).toList = ['/'].intercalate [(Ip.print a).toList, toChars 10 bits]
      by simp [Prefix.print, List.intercalate_cons_cons]]
    apply List.splitOn_intercalate
    · intro l hl hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · rcases mem_print hc with h | h | h
        · exact (mem_lower_ne h).2.2 rfl
        · cases h
        · cases h
      · exact (mem_lower_ne (mem_toChars (by omega) (by omega) hc)).2.2 rfl
    · simp
  simp only [Prefix.parse, hsplit, String.ofList_toList, Ip.parse_print, decimal?_toChars,
    Option.bind_eq_bind, Option.bind_some]
  rw [dite_eq_left le]

/-! ### Loopback -/

/-- Whether the address is the host's own: in `127.0.0.0/8`, `::1`, or in `127.0.0.0/8` mapped
into IPv6 (`::ffff:127.0.0.1`), as Go's `netip.Addr.IsLoopback` reads it. -/
def Addr.isLoopback : Addr → Bool
  | .v4 n => n.val / 2 ^ 24 == 127
  | .v6 n => n.val == 1 || n.val / 2 ^ 24 == 0xffff7f

theorem isLoopback_v4 (n : Fin (2 ^ 32)) :
    (Addr.v4 n).isLoopback ↔ 127 * 2 ^ 24 ≤ n.val ∧ n.val < 128 * 2 ^ 24 := by
  simp only [Addr.isLoopback, beq_iff_eq]
  omega

theorem isLoopback_v6 (n : Fin (2 ^ 128)) :
    (Addr.v6 n).isLoopback ↔
      n.val = 1 ∨ 0xffff7f * 2 ^ 24 ≤ n.val ∧ n.val < 0xffff80 * 2 ^ 24 := by
  simp only [Addr.isLoopback, Bool.or_eq_true, beq_iff_eq]
  omega

end Lanes.Ip
