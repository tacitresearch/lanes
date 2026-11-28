/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Data.Match
public import Lanes.Data.BodySound
public import Lanes.Proof.List.Basic

/-!
Matching by name reads old data as the data-format decision's rules say. The same schema needs
no plan, so a value reads as itself (`Body.decodeWith_encode_self`). A field added with a
default, anywhere, takes it, and every old field keeps its value (`Schema.Plan.of_insertIdx`). A
renamed constructor reads through its former name, and every value keeps its constructor and its
fields (`Schema.Plan.of_rename`). A type with a declared migration reads through it
(`Body.decodeWith_migrate`). The two named-type theorems hold of a record or a sum at the root
whose fields' types are one type in both schemas (`Schema.Plan.Alike`): those need no plan, and
matching does not look into them again.
-/

@[expose] public section

namespace Lanes

namespace Schema.Plan

open Codec (Error Limits)

variable {ms : List Migration}

/-! The same schema. -/

theorem of_self (s : Schema) : of ms s s = .ok .same := by
  unfold of; simp

theorem apply_same (v : Value) : Plan.same.apply v = .ok v := by
  simp [apply, same, applyTy]

/-! Which of the writer's names a reader's name takes. -/

theorem claim_getElem {names : List String} (hn : names.Nodup) {j : Nat}
    (hj : j < names.length) (aliases : List String) : claim names names[j] aliases = some j := by
  simp [claim, idxOf?_getElem hn hj]

theorem claim_new {names : List String} {name : String} {aliases : List String}
    (hname : name ∉ names) (ha : ∀ x ∈ aliases, x ∉ names) : claim names name aliases = none := by
  simp only [claim, List.idxOf?_eq_none_iff.mpr hname, List.findSome?_eq_none_iff]
  exact fun x hx => List.idxOf?_eq_none_iff.mpr (ha x hx)

theorem claim_alias {names : List String} (hn : names.Nodup) {name : String}
    {aliases : List String} {k : Nat} (hk : k < names.length) (hname : name ∉ names)
    (hwas : names[k] ∈ aliases) (ha : ∀ x ∈ aliases, x ∈ names → x = names[k]) :
    claim names name aliases = some k := by
  simp only [claim, List.idxOf?_eq_none_iff.mpr hname]
  induction aliases with
  | nil => simp at hwas
  | cons x xs ih =>
    rw [List.findSome?_cons]
    by_cases hx : x ∈ names
    · rw [ha x List.mem_cons_self hx, idxOf?_getElem hn hk]
    · rw [List.idxOf?_eq_none_iff.mpr hx]
      apply ih
      · rcases List.mem_cons.mp hwas with h | h
        · exact absurd (h ▸ List.getElem_mem hk) hx
        · exact h
      · exact fun y hy => ha y (List.mem_cons_of_mem _ hy)

theorem clash_eq_none : ∀ (cs : List (String × Option Nat)) (seen : List Nat),
    (cs.filterMap (·.2) ++ seen).Nodup → clash cs seen = none
  | [], _, _ => rfl
  | (_, none) :: cs, seen, h => by
    rw [clash]
    exact clash_eq_none cs seen (by simpa using h)
  | (_, some k) :: cs, seen, h => by
    simp only [List.filterMap_cons, List.cons_append, List.nodup_cons, List.mem_append,
      not_or] at h
    simp only [clash, h.1.2, ↓reduceIte]
    exact clash_eq_none cs (k :: seen)
      (List.perm_middle.nodup_iff.mpr (List.nodup_cons.mpr ⟨by simp [h.1.1, h.1.2], h.2⟩))

theorem unambiguous_eq {step : String → Error.Step} {names : List String}
    {claims : List (String × Option Nat)} (h : (claims.filterMap (·.2)).Nodup) :
    unambiguous step names claims = .ok () := by
  rw [unambiguous, clash_eq_none claims [] (by simpa using h)]

theorem filterMap_claims {β : Type} {name : β → String} {aliases : β → List String}
    {ws : List β} (hn : (ws.map name).Nodup) :
    ws.filterMap (fun g => claim (ws.map name) (name g) (aliases g)) = List.range ws.length :=
  filterMap_eq_range fun j hj => by
    have := claim_getElem hn (by simpa using hj) (aliases ws[j])
    rwa [List.getElem_map] at this

/-! Named types that are one type in two tables. -/

/-- `names` are one type in the tables `w` and `r`: each declared in both, the same, using only
names among them. -/
def Alike (w r : List (String × Schema.Decl)) (names : List String) : Prop :=
  ∀ x ∈ names, ∃ d, w.lookup x = some d ∧ r.lookup x = some d ∧ ∀ y ∈ d.refs, y ∈ names

theorem mem_of_lookup {w : List (String × Schema.Decl)} {x : String} {d : Schema.Decl}
    (h : w.lookup x = some d) : ∃ d', (x, d') ∈ w := by
  induction w with
  | nil => simp at h
  | cons e w ih =>
    obtain ⟨n, d'⟩ := e
    rw [List.lookup_cons] at h
    by_cases hx : x = n
    · subst hx; exact ⟨d', List.mem_cons_self⟩
    · simp only [beq_eq_false_iff_ne.mpr hx] at h
      obtain ⟨d'', hm⟩ := ih h
      exact ⟨d'', List.mem_cons_of_mem _ hm⟩

theorem subset_keep {w : List (String × Schema.Decl)} {P names : List String} (hP : ∀ x ∈ P, x ∈ names)
    (hw : ∀ x ∈ P, ∃ d, w.lookup x = some d ∧ ∀ y ∈ d.refs, y ∈ P) :
    ∀ x ∈ P, x ∈ keep w names := by
  intro x hx
  obtain ⟨d, hd, hrefs⟩ := hw x hx
  simp only [keep, List.mem_filter, hd, List.all_eq_true, List.contains_iff_mem]
  exact ⟨hP x hx, fun y hy => hP y (hrefs y hy)⟩

theorem subset_prune {w : List (String × Schema.Decl)} {P : List String}
    (hw : ∀ x ∈ P, ∃ d, w.lookup x = some d ∧ ∀ y ∈ d.refs, y ∈ P) :
    ∀ (k : Nat) (names : List String), (∀ x ∈ P, x ∈ names) → ∀ x ∈ P, x ∈ prune w k names
  | 0, _, hP => hP
  | k + 1, names, hP => by
    rw [prune]
    split
    · exact hP
    · exact subset_prune hw k _ (subset_keep hP hw)

theorem prune_subset {w : List (String × Schema.Decl)} :
    ∀ (k : Nat) (names : List String), ∀ x ∈ prune w k names, x ∈ names
  | 0, _, _, hx => hx
  | k + 1, names, x, hx => by
    rw [prune] at hx
    split at hx
    · exact hx
    · exact (List.mem_filter.mp (prune_subset k _ x hx)).1

theorem mem_alike {w r : List (String × Schema.Decl)} {names : List String} (h : Alike w r names) :
    ∀ x ∈ names, x ∈ alike w r := by
  refine subset_prune (fun x hx => ?_) _ _ (fun x hx => ?_)
  · obtain ⟨d, hw, -, hrefs⟩ := h x hx
    exact ⟨d, hw, hrefs⟩
  · obtain ⟨d, hw, hr, -⟩ := h x hx
    obtain ⟨d', hm⟩ := mem_of_lookup hw
    exact List.mem_filterMap.mpr ⟨(x, d'), hm, by simp [hw, hr]⟩

theorem lookup_of_mem_alike {w r : List (String × Schema.Decl)} {x : String} (h : x ∈ alike w r) :
    ∃ d, w.lookup x = some d ∧ r.lookup x = some d := by
  obtain ⟨⟨n, d⟩, -, he⟩ := List.mem_filterMap.mp (prune_subset _ _ x h)
  simp only at he
  split at he
  · rename_i d' hd'
    split at he
    · cases he
      rename_i hr
      exact ⟨d', hd', beq_iff_eq.mp hr⟩
    · cases he
  · cases he

theorem sameTy_of_alike {w r : List (String × Schema.Decl)} {names : List String} (h : Alike w r names)
    {t : Schema.Ty} (ht : ∀ x ∈ t.refs, x ∈ names) : sameTy (alike w r) t t = true := by
  simp only [sameTy, beq_self_eq_true, Bool.true_and, List.all_eq_true, List.contains_iff_mem]
  exact fun x hx => mem_alike h x (ht x hx)

theorem ofTy_same {w r : Schema} {names : List String} {fuel : Nat} {wt rt : Schema.Ty} {memo : Memo}
    (h : sameTy names wt rt = true) : ofTy ms w r names fuel wt rt memo = .ok (.same, memo) := by
  rw [ofTy.eq_def]; simp [h]

/-! Fields. -/

/-- A reader's field that is one of the writer's, of one type in both, or that is new and has a
default. -/
def Known (names : List String) (ws : List (Schema.Field Schema.Ty)) (g : Schema.Field Schema.Ty) : Prop :=
  (g ∈ ws ∧ sameTy names g.schema g.schema = true)
    ∨ (g.name ∉ ws.map (·.name) ∧ (∀ x ∈ g.aliases, x ∉ ws.map (·.name)) ∧ g.default.isSome)

/-- The plan of a known field. -/
def knownPlan (ws : List (Schema.Field Schema.Ty)) (g : Schema.Field Schema.Ty) : Plan.Field Plan.Ty :=
  match (ws.map (·.name)).idxOf? g.name with
  | some k => .take g.name k .same
  | none => .fill (g.default.getD (.nat 0))

/-- The value of a known field, read from the writer's `vs`. -/
def knownValue (ws : List (Schema.Field Schema.Ty)) (vs : List Value) (g : Schema.Field Schema.Ty) : Value :=
  match (ws.map (·.name)).idxOf? g.name with
  | some k => vs.getD k (.nat 0)
  | none => g.default.getD (.nat 0)

theorem ofFields_known {w r : Schema} {names : List String} {fuel : Nat} {memo : Memo}
    {ws : List (Schema.Field Schema.Ty)} (hn : (ws.map (·.name)).Nodup) :
    ∀ (R : List (Schema.Field Schema.Ty)), (∀ g ∈ R, Known names ws g) →
      ofFields ms w r names fuel ws R memo = .ok (R.map (knownPlan ws), memo)
  | [], _ => by rw [ofFields]; rfl
  | ⟨name, aliases, s, default⟩ :: R, hR => by
    have ih := ofFields_known (w := w) (r := r) (fuel := fuel) (memo := memo) hn R
      fun g hg => hR g (List.mem_cons_of_mem _ hg)
    rw [ofFields.eq_def]; simp only
    rcases hR _ List.mem_cons_self with ⟨hmem, hsame⟩ | ⟨hname, halias, hdef⟩
    · obtain ⟨k, hk, hg⟩ := List.getElem_of_mem hmem
      have hk' : k < (ws.map (·.name)).length := by simpa using hk
      have hname : (ws.map (·.name))[k] = name := by simp [hg]
      have hc := claim_getElem hn hk' aliases
      have hi := idxOf?_getElem hn hk'
      rw [hname] at hc hi
      have hget : ws[k]? = some ⟨name, aliases, s, default⟩ := by
        rw [List.getElem?_eq_getElem hk, hg]
      simp only at hsame
      simp [hc, hi, hget, knownPlan, ofTy_same hsame, ih]
    · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hdef
      have hi := List.idxOf?_eq_none_iff.mpr hname
      simp only at hv
      simp [claim_new hname halias, hi, hv, knownPlan, ih]

theorem applyFields_known {pairs : List ((String × String) × Plan.Decl)} {ws : List (Schema.Field Schema.Ty)}
    {vs : List Value} (hl : vs.length = ws.length) : ∀ (R : List (Schema.Field Schema.Ty)),
      applyFields pairs (R.map (knownPlan ws)) vs = .ok (R.map (knownValue ws vs))
  | [] => by rw [List.map_nil, applyFields]; rfl
  | g :: R => by
    have ih := applyFields_known (pairs := pairs) hl R
    cases h : (ws.map (·.name)).idxOf? g.name with
    | none =>
      simp only [List.map_cons, knownPlan, knownValue, h]
      rw [applyFields, ih]
    | some k =>
      have hk : k < vs.length := by
        have := (List.idxOf?_eq_some_iff.mp h).1
        simp only [List.length_map] at this
        omega
      simp only [List.map_cons, knownPlan, knownValue, h]
      rw [applyFields]
      split
      · simp_all
      · rename_i v hv
        simp only [List.getElem?_eq_getElem hk, Option.some.injEq] at hv
        subst hv
        simp [applyTy, ih, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]

theorem map_knownValue {ws : List (Schema.Field Schema.Ty)} {vs : List Value}
    (hn : (ws.map (·.name)).Nodup) (hl : vs.length = ws.length) :
    ws.map (knownValue ws vs) = vs := by
  apply List.ext_getElem (by simp [hl])
  intro j h1 h2
  have hj : j < (ws.map (·.name)).length := by simpa using h1
  have hi := idxOf?_getElem hn hj
  simp only [List.getElem_map] at hi
  simp [knownValue, hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

/-! The root: a named type of each schema, matched as a pair. -/

theorem migrationFor_none {w r : Schema} {n n' : String}
    (hm : ∀ m ∈ ms, m.old.root ≠ .ref n ∨ m.new.root ≠ .ref n') :
    migrationFor ms w r (.ref n) (.ref n') = none := by
  rw [migrationFor, List.find?_eq_none]
  intro m hm'
  rcases hm m hm' with h | h <;> simp [h]

/-- Matching two schemas whose roots are named types: the pair's plan, made once. -/
theorem of_ref {w r : Schema} {n n' : String} (hw : w.root = .ref n) (hr : r.root = .ref n')
    (hne : w ≠ r) (hm : ∀ m ∈ ms, m.old.root ≠ .ref n ∨ m.new.root ≠ .ref n')
    (hsame : sameTy (alike w.types r.types) (.ref n) (.ref n') = false) :
    of ms w r = (match ofPair ms w r (alike w.types r.types) (w.types.length * r.types.length + 1)
      n n' [] with
      | .ok (p, memo) => .ok ⟨made memo, p⟩
      | .error e => .error e) := by
  unfold of
  rw [hw, hr] at *
  simp only [beq_eq_false_iff_ne.mpr hne, Bool.false_eq_true, ↓reduceIte, migrationFor_none hm]
  rw [ofTy.eq_def]
  simp only [hsame, Bool.false_eq_true, ↓reduceIte, migrationFor_none hm]
  rfl

/-- Two records, the roots, matched field by field. -/
theorem of_record {w r : Schema} {n n' t t' : String} {wfs rfs : List (Schema.Field Schema.Ty)}
    (hw : w.root = .ref n) (hr : r.root = .ref n')
    (hwl : w.types.lookup n = some (.record t wfs)) (hrl : r.types.lookup n' = some (.record t' rfs))
    (hne : w ≠ r) (hm : ∀ m ∈ ms, m.old.root ≠ .ref n ∨ m.new.root ≠ .ref n')
    (hsame : sameTy (alike w.types r.types) (.ref n) (.ref n') = false)
    (hc : (rfs.filterMap fun f => claim (wfs.map (·.name)) f.name f.aliases).Nodup)
    {ps : List (Plan.Field Plan.Ty)} {memo : Memo}
    (hf : ofFields ms w r (alike w.types r.types) (w.types.length * r.types.length) wfs rfs
      [((n, n'), none)] = .ok (ps, memo)) :
    of ms w r = .ok ⟨made (((n, n'), some (.record t' ps)) :: memo), .ref n n'⟩ := by
  rw [of_ref hw hr hne hm hsame, ofPair]
  simp only [List.lookup, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hwl, hrl]
  rw [unambiguous_eq (by simpa [List.filterMap_map, Function.comp_def] using hc)]
  simp [hf]

/-- Two sums, the roots, matched constructor by constructor. -/
theorem of_sum {w r : Schema} {n n' t t' : String} {wcs rcs : List (Schema.Ctor Schema.Ty)}
    (hw : w.root = .ref n) (hr : r.root = .ref n')
    (hwl : w.types.lookup n = some (.sum t wcs)) (hrl : r.types.lookup n' = some (.sum t' rcs))
    (hne : w ≠ r) (hm : ∀ m ∈ ms, m.old.root ≠ .ref n ∨ m.new.root ≠ .ref n')
    (hsame : sameTy (alike w.types r.types) (.ref n) (.ref n') = false)
    (hc : (rcs.filterMap fun c => claim (wcs.map (·.name)) c.name c.aliases).Nodup)
    {found : List (Option (Nat × Ctor Plan.Ty))} {memo : Memo}
    (hf : ofCtors ms w r (alike w.types r.types) (w.types.length * r.types.length) wcs rcs 0
      [((n, n'), none)] = .ok (found, memo)) :
    of ms w r = .ok ⟨made (((n, n'), some (.sum t' (wcs.mapIdx fun k c => pick found k c.name)))
      :: memo), .ref n n'⟩ := by
  rw [of_ref hw hr hne hm hsame, ofPair]
  simp only [List.lookup, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hwl, hrl]
  rw [unambiguous_eq (by simpa [List.filterMap_map, Function.comp_def] using hc)]
  simp [hf]

/-- The root of two different named types, or of one declared differently, is no one type. -/
theorem sameTy_ref {w r : List (String × Schema.Decl)} {n n' : String}
    (h : n = n' → w.lookup n ≠ r.lookup n) : sameTy (alike w r) (.ref n) (.ref n') = false := by
  rw [Bool.eq_false_iff]
  intro hs
  simp only [sameTy, Schema.Ty.ref.injEq, Bool.and_eq_true, beq_iff_eq, Schema.Ty.refs, List.all_cons,
    List.all_nil, Bool.and_true, List.contains_iff_mem] at hs
  obtain ⟨rfl, hmem⟩ := hs
  obtain ⟨d, hw, hr⟩ := lookup_of_mem_alike hmem
  exact h rfl (hw.trans hr.symm)

theorem apply_ref {n n' : String} {d : Plan.Decl} {memo : Memo} (v : Value) :
    (⟨made (((n, n'), some d) :: memo), .ref n n'⟩ : Plan).apply v = applyDecl
      (made (((n, n'), some d) :: memo)) d v := by
  simp [apply, applyTy, made]

/-- A field added with a default, anywhere: every old field keeps its value, and the new one
takes its default. The record is the root, `n` in the writer's table and `n'` in the reader's,
whose other named types are `types` in both, and each field's type is one type in both. -/
theorem of_insertIdx {n n' t t' : String} {types : List (String × Schema.Decl)}
    {ws : List (Schema.Field Schema.Ty)} {f : Schema.Field Schema.Ty} {i : Nat} {d : Value} (hi : i ≤ ws.length)
    (hn : (ws.map (·.name)).Nodup) (hname : f.name ∉ ws.map (·.name))
    (halias : ∀ x ∈ f.aliases, x ∉ ws.map (·.name)) (hd : f.default = some d)
    {names : List String}
    (halike : Alike ((n, .record t ws) :: types) ((n', .record t' (ws.insertIdx i f)) :: types)
      names)
    (hfields : ∀ g ∈ ws, ∀ x ∈ g.schema.refs, x ∈ names)
    (hm : ∀ m ∈ ms, m.old.root ≠ .ref n ∨ m.new.root ≠ .ref n') :
    ∃ p, of ms ⟨(n, .record t ws) :: types, .ref n⟩
        ⟨(n', .record t' (ws.insertIdx i f)) :: types, .ref n'⟩ = .ok p ∧
      ∀ vs : List Value, vs.length = ws.length →
        p.apply (.ctor 0 vs) = .ok (.ctor 0 (vs.insertIdx i d)) := by
  have hR : ∀ g ∈ ws.insertIdx i f, Known (alike ((n, .record t ws) :: types)
      ((n', .record t' (ws.insertIdx i f)) :: types)) ws g := by
    intro g hg
    rcases (List.mem_insertIdx hi).mp hg with rfl | h
    · exact .inr ⟨hname, halias, by simp [hd]⟩
    · exact .inl ⟨h, sameTy_of_alike halike (hfields g h)⟩
  have hlen : ws ≠ ws.insertIdx i f := by
    intro h
    have := congrArg List.length h
    rw [List.length_insertIdx_of_le_length hi] at this
    omega
  have hne : (⟨(n, .record t ws) :: types, .ref n⟩ : Schema)
      ≠ ⟨(n', .record t' (ws.insertIdx i f)) :: types, .ref n'⟩ := by
    intro h
    simp only [Schema.mk.injEq, List.cons.injEq, Prod.mk.injEq, Schema.Decl.record.injEq] at h
    exact hlen h.1.1.2.2
  have hsame := sameTy_ref (w := (n, .record t ws) :: types)
    (r := (n', .record t' (ws.insertIdx i f)) :: types) (n := n) (n' := n') fun h => by
      subst h
      simp only [List.lookup_cons, beq_self_eq_true, ne_eq, Option.some.injEq, Schema.Decl.record.injEq,
        not_and]
      exact fun _ => hlen
  have hc : ((ws.insertIdx i f).filterMap fun g =>
      claim (ws.map (·.name)) g.name g.aliases).Nodup := by
    rw [filterMap_insertIdx (f := fun (g : Schema.Field Schema.Ty) => claim (ws.map (·.name)) g.name g.aliases)
      (claim_new hname halias), filterMap_claims hn]
    exact List.nodup_range
  refine ⟨_, of_record (t := t) (t' := t') (wfs := ws) (rfs := ws.insertIdx i f) rfl rfl
    (by simp) (by simp) hne hm
    hsame hc (ofFields_known hn _ hR), fun vs hl => ?_⟩
  rw [apply_ref, applyDecl]
  rw [applyFields_known hl, Body.within_ok]
  simp only [map_insertIdx, map_knownValue hn hl]
  simp [knownValue, List.idxOf?_eq_none_iff.mpr hname, hd]

/-! Constructors. -/

/-- Each reader's constructor that takes one of the writer's with the same fields, of one type in
both, keeps them. -/
theorem ofCtors_same {w r : Schema} {names : List String} {fuel : Nat} {memo : Memo}
    {cs : List (Schema.Ctor Schema.Ty)} :
    ∀ (R : List (Schema.Ctor Schema.Ty)) (index : Nat),
      (∀ r ∈ R, ∃ k c, claim (cs.map (·.name)) r.name r.aliases = some k ∧ cs[k]? = some c ∧
        c.fields = r.fields ∧ ∀ g ∈ r.fields, sameTy names g.schema g.schema = true) →
      ofCtors ms w r names fuel cs R index memo = .ok (R.mapIdx fun j r =>
        (claim (cs.map (·.name)) r.name r.aliases).map fun k => (k, .to r.name (index + j) none),
        memo)
  | [], _, _ => by rw [ofCtors]; rfl
  | ⟨name, aliases, fields⟩ :: R, index, hR => by
    have ih := ofCtors_same (w := w) (r := r) (fuel := fuel) (memo := memo) R (index + 1)
      fun r hr => hR r (List.mem_cons_of_mem _ hr)
    obtain ⟨k, c, hc, hk, hf, hs⟩ := hR _ List.mem_cons_self
    simp only at hc hf hs
    have hall : (fields.all fun f => sameTy names f.schema f.schema) = true :=
      List.all_eq_true.mpr hs
    rw [ofCtors.eq_def]
    simp only [hc, hk, hf, beq_self_eq_true, hall, Bool.and_self, ↓reduceIte, ih,
      List.mapIdx_cons, Nat.add_zero, Option.map_some]
    congr 4
    funext j r
    rw [show index + 1 + j = index + (j + 1) by omega]

theorem pick_eq : ∀ (found : List (Option (Nat × Ctor Plan.Ty))) (off k : Nat) (c : Ctor Plan.Ty)
    (name : String), (∀ j (hj : j < found.length), ∃ c, found[j] = some (off + j, c)) →
    found[k]? = some (some (off + k, c)) → pick found (off + k) name = c
  | [], _, _, _, _, _, h => by simp at h
  | x :: found, off, k, c, name, H, h => by
    obtain ⟨c0, h0⟩ := H 0 (by simp)
    simp only [List.getElem_cons_zero, Nat.add_zero] at h0
    subst h0
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq, Nat.add_zero] at h
      simp [pick, h.2]
    | succ k =>
      simp only [pick, show ¬off = off + (k + 1) by omega, ↓reduceIte]
      rw [show off + (k + 1) = off + 1 + k by omega]
      refine pick_eq found (off + 1) k c name (fun j hj => ?_) ?_
      · obtain ⟨c', h'⟩ := H (j + 1) (by simp; omega)
        exact ⟨c', by rw [show off + 1 + j = off + (j + 1) by omega]; simpa using h'⟩
      · rw [show off + 1 + k = off + (k + 1) by omega]; simpa using h

theorem applyCtor_to {pairs : List ((String × String) × Plan.Decl)} :
    ∀ (ctors : List (Ctor Plan.Ty)) (k : Nat) (vs : List Value) {name : String}
    {j : Nat}, ctors[k]? = some (.to name j none) → applyCtor pairs ctors k vs = .ok (.ctor j vs)
  | [], _, _, _, _, h => by simp at h
  | _ :: _, 0, _, _, _, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    rw [applyCtor]
  | _ :: ctors, k + 1, vs, _, _, h => by
    rw [applyCtor]
    exact applyCtor_to ctors k vs (by simpa using h)

/-- A renamed constructor reads through its former name: the data's `k`th constructor is the
reader's, under its new name, and every value keeps its constructor and its fields. The sum is
the root, `n` in the writer's table and `n'` in the reader's, whose other named types are `types`
in both, and each field's type is one type in both. -/
theorem of_rename {n n' t t' : String} {types : List (String × Schema.Decl)} {cs : List (Schema.Ctor Schema.Ty)}
    {k : Nat} (hk : k < cs.length) {c : Schema.Ctor Schema.Ty}
    (hn : (cs.map (·.name)).Nodup) (hname : c.name ∉ cs.map (·.name))
    (hwas : cs[k].name ∈ c.aliases)
    (halias : ∀ x ∈ c.aliases, x ∈ cs.map (·.name) → x = cs[k].name)
    (hfields : c.fields = cs[k].fields) {names : List String}
    (halike : Alike ((n, .sum t cs) :: types) ((n', .sum t' (cs.set k c)) :: types) names)
    (hctors : ∀ c ∈ cs, ∀ g ∈ c.fields, ∀ x ∈ g.schema.refs, x ∈ names)
    (hm : ∀ m ∈ ms, m.old.root ≠ .ref n ∨ m.new.root ≠ .ref n') :
    ∃ p, of ms ⟨(n, .sum t cs) :: types, .ref n⟩ ⟨(n', .sum t' (cs.set k c)) :: types, .ref n'⟩
        = .ok p ∧
      ∀ j vs, j < cs.length → p.apply (.ctor j vs) = .ok (.ctor j vs) := by
  have hk' : k < (cs.map (·.name)).length := by simpa using hk
  have hclaim : ∀ j (hj : j < (cs.set k c).length),
      claim (cs.map (·.name)) (cs.set k c)[j].name (cs.set k c)[j].aliases = some j := by
    intro j hj
    have hj' : j < (cs.map (·.name)).length := by simpa using hj
    have hj'' : j < cs.length := by simpa using hj
    rw [List.getElem_set]
    split
    · subst k
      exact claim_alias hn hk' hname (by simpa using hwas) (by simpa using halias)
    · simpa using claim_getElem hn hj' cs[j].aliases
  have hR : ∀ r ∈ cs.set k c, ∃ k' c', claim (cs.map (·.name)) r.name r.aliases = some k' ∧
      cs[k']? = some c' ∧ c'.fields = r.fields ∧ ∀ g ∈ r.fields,
        sameTy (alike ((n, .sum t cs) :: types) ((n', .sum t' (cs.set k c)) :: types))
          g.schema g.schema = true := by
    intro r hr
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hr
    have hj'' : j < cs.length := by simpa using hj
    have hfj : cs[j].fields = (cs.set k c)[j].fields := by
      rw [List.getElem_set]
      split
      · subst k; exact hfields.symm
      · rfl
    refine ⟨j, cs[j], hclaim j hj, List.getElem?_eq_getElem hj'', hfj, fun g hg => ?_⟩
    rw [← hfj] at hg
    exact sameTy_of_alike halike (hctors _ (List.getElem_mem hj'') g hg)
  have hne' : cs ≠ cs.set k c := by
    intro h
    have := congrArg (·[k]?) h
    simp only [List.getElem?_set_self hk, List.getElem?_eq_getElem hk, Option.some.injEq] at this
    exact hname (this ▸ List.mem_map_of_mem (f := (·.name)) (List.getElem_mem hk))
  have hne : (⟨(n, .sum t cs) :: types, .ref n⟩ : Schema)
      ≠ ⟨(n', .sum t' (cs.set k c)) :: types, .ref n'⟩ := by
    intro h
    simp only [Schema.mk.injEq, List.cons.injEq, Prod.mk.injEq, Schema.Decl.sum.injEq] at h
    exact hne' h.1.1.2.2
  have hsame := sameTy_ref (w := (n, .sum t cs) :: types)
    (r := (n', .sum t' (cs.set k c)) :: types) (n := n) (n' := n') fun h => by
      subst h
      simp only [List.lookup_cons, beq_self_eq_true, ne_eq, Option.some.injEq, Schema.Decl.sum.injEq,
        not_and]
      exact fun _ => hne'
  have hc : ((cs.set k c).filterMap fun r =>
      claim (cs.map (·.name)) r.name r.aliases).Nodup := by
    rw [filterMap_eq_range hclaim]
    exact List.nodup_range
  refine ⟨_, of_sum (t := t) (t' := t') (wcs := cs) (rcs := cs.set k c) rfl rfl
    (by simp) (by simp) hne hm
    hsame hc (ofCtors_same _ 0 hR), fun j vs hj => ?_⟩
  have hj2 : j < (cs.set k c).length := by simpa using hj
  have hpick := pick_eq (List.mapIdx (fun j r => (claim (cs.map (·.name)) r.name r.aliases).map
      fun k => (k, Ctor.to r.name (0 + j) none)) (cs.set k c)) 0 j
    (.to (cs.set k c)[j].name (0 + j) none) cs[j].name
    (fun j' hj' => by
      have hj'' : j' < (cs.set k c).length := by simpa using hj'
      exact ⟨.to (cs.set k c)[j'].name (0 + j') none, by
        rw [List.getElem_mapIdx, hclaim j' hj'']; simp⟩)
    (by rw [List.getElem?_mapIdx, List.getElem?_eq_getElem hj2, Option.map_some, hclaim j hj2]; simp)
  simp only [Nat.zero_add] at hpick
  rw [apply_ref, applyDecl]
  rw [applyCtor_to _ j vs (name := (cs.set k c)[j].name) (j := j)]
  · rfl
  · rw [List.getElem?_mapIdx, List.getElem?_eq_getElem hj, Option.map_some]
    simp only [Nat.zero_add] at hpick ⊢
    rw [hpick]

end Schema.Plan

namespace Body

open Codec (Limits)

variable {α : Type} {limits : Limits}

theorem readWith_same (s : Schema) (bytes : ByteArray) :
    readWith limits s .same bytes = read limits s bytes := by
  unfold readWith; split <;> simp_all [Schema.Plan.apply_same]

theorem decodeWith_same (s : Schema.Of α) (bytes : ByteArray) :
    decodeWith limits s.schema .same s bytes = decode limits s bytes := by
  simp only [decodeWith, readWith_same, decode]; rfl

/-- With the same schema, a type's value reads back as itself. -/
theorem decodeWith_encode_self {ms : List Schema.Migration} {s : Schema.Of α} {a : α}
    {bytes : ByteArray} {plan : Schema.Plan} (hp : Schema.Plan.of ms s.schema s.schema = .ok plan)
    (h : encode limits s a = .ok bytes) : decodeWith limits s.schema plan s bytes = .ok a := by
  rw [Schema.Plan.of_self] at hp
  cases hp
  rw [decodeWith_same, decode_encode h]

/-- A type changed with a declared migration: its old value reads as the migrated one. -/
theorem decodeWith_migrate {β : Type} {old : Schema.Of α} {new : Schema.Of β} {f : α → β}
    (hne : old.schema ≠ new.schema) {a : α} {bytes : ByteArray}
    (h : encode limits old a = .ok bytes) :
    ∃ plan, Schema.Plan.of [.of old new f] old.schema new.schema = .ok plan ∧
      decodeWith limits old.schema plan new bytes = .ok (f a) := by
  refine ⟨⟨[], .convert new.schema.name (Schema.Migration.of old new f).run⟩, ?_, ?_⟩
  · unfold Schema.Plan.of
    simp [beq_eq_false_iff_ne.mpr hne, Schema.Plan.migrationFor, Schema.Migration.of,
      List.all_eq_true]
  · simp only [decodeWith, readWith, read_write h, Schema.Plan.apply, Schema.Plan.applyTy,
      Schema.Migration.of, old.ofValue_toValue, Option.map_some, new.ofValue_toValue]

end Body

end Lanes
