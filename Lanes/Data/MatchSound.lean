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
(`Body.decodeWith_migrate`). The equality of values and of schemas is lawful
(`Value.instLawfulBEq`, `Schema.instLawfulBEq`).
-/

@[expose] public section

namespace Lanes

/-! Equality of values and of schemas. -/

mutual

theorem Value.beq_refl : (v : Value) → Value.beq v v = true
  | .nat _ | .int _ | .string _ | .bytes _ => by simp [Value.beq]
  | .list vs => by simp only [Value.beq]; exact Value.beqAll_refl vs
  | .ctor _ vs => by simp only [Value.beq, beq_self_eq_true, Bool.true_and]; exact Value.beqAll_refl vs

theorem Value.beqAll_refl : (vs : List Value) → Value.beqAll vs vs = true
  | [] => rfl
  | v :: vs => by simp only [Value.beqAll, Value.beq_refl v, Value.beqAll_refl vs, Bool.and_self]

end

mutual

theorem Value.eq_of_beq : (a b : Value) → Value.beq a b = true → a = b
  | .nat _, b, h | .int _, b, h | .string _, b, h | .bytes _, b, h => by
    cases b <;> simp_all [Value.beq]
  | .list as, b, h => by
    cases b <;> simp [Value.beq] at h
    rw [Value.eq_of_beqAll as _ h]
  | .ctor _ as, b, h => by
    cases b <;> simp [Value.beq] at h
    rw [h.1, Value.eq_of_beqAll as _ h.2]

theorem Value.eq_of_beqAll : (as bs : List Value) → Value.beqAll as bs = true → as = bs
  | [], [], _ => rfl
  | [], _ :: _, h | _ :: _, [], h => by simp [Value.beqAll] at h
  | a :: as, b :: bs, h => by
    simp only [Value.beqAll, Bool.and_eq_true] at h
    rw [Value.eq_of_beq a b h.1, Value.eq_of_beqAll as bs h.2]

end

instance Value.instLawfulBEq : LawfulBEq Value where
  rfl := Value.beq_refl _
  eq_of_beq := Value.eq_of_beq _ _

mutual

theorem Schema.beq_refl : (s : Schema) → Schema.beq s s = true
  | .nat | .int | .string | .bytes | .unit => by simp [Schema.beq]
  | .list s | .dependent s => by simp only [Schema.beq]; exact Schema.beq_refl s
  | .map k v => by simp only [Schema.beq, Schema.beq_refl k, Schema.beq_refl v, Bool.and_self]
  | .record _ as fs => by
    simp only [Schema.beq, beq_self_eq_true, Schema.beqAll_refl as, Schema.beqFields_refl fs,
      Bool.and_self]
  | .sum _ as cs => by
    simp only [Schema.beq, beq_self_eq_true, Schema.beqAll_refl as, Schema.beqCtors_refl cs,
      Bool.and_self]

theorem Schema.beqAll_refl : (ss : List Schema) → Schema.beqAll ss ss = true
  | [] => by simp [Schema.beqAll]
  | s :: ss => by simp only [Schema.beqAll, Schema.beq_refl s, Schema.beqAll_refl ss, Bool.and_self]

theorem Schema.beqFields_refl : (fs : List (Schema.Field Schema)) → Schema.beqFields fs fs = true
  | [] => by simp [Schema.beqFields]
  | ⟨_, _, s, _⟩ :: fs => by
    simp only [Schema.beqFields, beq_self_eq_true, Schema.beq_refl s, Schema.beqFields_refl fs,
      Bool.and_self]

theorem Schema.beqCtors_refl : (cs : List (Schema.Ctor Schema)) → Schema.beqCtors cs cs = true
  | [] => by simp [Schema.beqCtors]
  | ⟨_, _, fs⟩ :: cs => by
    simp only [Schema.beqCtors, beq_self_eq_true, Schema.beqFields_refl fs,
      Schema.beqCtors_refl cs, Bool.and_self]

end

mutual

theorem Schema.eq_of_beq : (a b : Schema) → Schema.beq a b = true → a = b
  | .nat, b, h | .int, b, h | .string, b, h | .bytes, b, h | .unit, b, h => by
    cases b <;> simp_all [Schema.beq]
  | .list a, b, h => by
    cases b <;> simp [Schema.beq] at h
    rw [Schema.eq_of_beq a _ h]
  | .dependent a, b, h => by
    cases b <;> simp [Schema.beq] at h
    rw [Schema.eq_of_beq a _ h]
  | .map k v, b, h => by
    cases b <;> simp [Schema.beq] at h
    rw [Schema.eq_of_beq k _ h.1, Schema.eq_of_beq v _ h.2]
  | .record _ as fs, b, h => by
    cases b <;> simp [Schema.beq] at h
    obtain ⟨⟨ht, ha⟩, hf⟩ := h
    rw [ht, Schema.eq_of_beqAll as _ ha, Schema.eq_of_beqFields fs _ hf]
  | .sum _ as cs, b, h => by
    cases b <;> simp [Schema.beq] at h
    obtain ⟨⟨ht, ha⟩, hc⟩ := h
    rw [ht, Schema.eq_of_beqAll as _ ha, Schema.eq_of_beqCtors cs _ hc]

theorem Schema.eq_of_beqAll : (as bs : List Schema) → Schema.beqAll as bs = true → as = bs
  | [], [], _ => rfl
  | [], _ :: _, h | _ :: _, [], h => by simp [Schema.beqAll] at h
  | a :: as, b :: bs, h => by
    simp only [Schema.beqAll, Bool.and_eq_true] at h
    rw [Schema.eq_of_beq a b h.1, Schema.eq_of_beqAll as bs h.2]

theorem Schema.eq_of_beqFields :
    (as bs : List (Schema.Field Schema)) → Schema.beqFields as bs = true → as = bs
  | [], [], _ => rfl
  | [], _ :: _, h | _ :: _, [], h => by simp [Schema.beqFields] at h
  | ⟨_, _, s, _⟩ :: as, ⟨_, _, s', _⟩ :: bs, h => by
    simp only [Schema.beqFields, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨hn, ha⟩, hs⟩, hd⟩, hr⟩ := h
    rw [hn, ha, Schema.eq_of_beq s s' hs, hd, Schema.eq_of_beqFields as bs hr]

theorem Schema.eq_of_beqCtors :
    (as bs : List (Schema.Ctor Schema)) → Schema.beqCtors as bs = true → as = bs
  | [], [], _ => rfl
  | [], _ :: _, h | _ :: _, [], h => by simp [Schema.beqCtors] at h
  | ⟨_, _, fs⟩ :: as, ⟨_, _, fs'⟩ :: bs, h => by
    simp only [Schema.beqCtors, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨hn, ha⟩, hf⟩, hr⟩ := h
    rw [hn, ha, Schema.eq_of_beqFields fs fs' hf, Schema.eq_of_beqCtors as bs hr]

end

instance Schema.instLawfulBEq : LawfulBEq Schema where
  rfl := Schema.beq_refl _
  eq_of_beq := Schema.eq_of_beq _ _

theorem Schema.beqFields_iff {as bs : List (Schema.Field Schema)} :
    Schema.beqFields as bs = true ↔ as = bs :=
  ⟨Schema.eq_of_beqFields as bs, fun h => h ▸ Schema.beqFields_refl as⟩

namespace Schema.Plan

open Codec (Error Limits)

variable {ms : List Migration}

/-! The same schema. -/

theorem of_self (s : Schema) : of ms s s = .ok .same := by
  unfold of; simp

theorem apply_same (v : Value) : Plan.same.apply v = .ok v := by
  rw [apply]

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

/-! Fields. -/

/-- A reader's field that is one of the writer's, or that is new and has a default. -/
def Known (ws : List (Schema.Field Schema)) (g : Schema.Field Schema) : Prop :=
  g ∈ ws ∨ (g.name ∉ ws.map (·.name) ∧ (∀ x ∈ g.aliases, x ∉ ws.map (·.name)) ∧ g.default.isSome)

/-- The plan of a known field. -/
def knownPlan (ws : List (Schema.Field Schema)) (g : Schema.Field Schema) : Plan.Field Plan :=
  match (ws.map (·.name)).idxOf? g.name with
  | some k => .take g.name k .same
  | none => .fill (g.default.getD (.nat 0))

/-- The value of a known field, read from the writer's `vs`. -/
def knownValue (ws : List (Schema.Field Schema)) (vs : List Value) (g : Schema.Field Schema) :
    Value :=
  match (ws.map (·.name)).idxOf? g.name with
  | some k => vs.getD k (.nat 0)
  | none => g.default.getD (.nat 0)

theorem ofFields_known {ws : List (Schema.Field Schema)} (hn : (ws.map (·.name)).Nodup) :
    ∀ (R : List (Schema.Field Schema)), (∀ g ∈ R, Known ws g) →
      ofFields ms ws R = .ok (R.map (knownPlan ws))
  | [], _ => by rw [ofFields]; rfl
  | ⟨name, aliases, s, default⟩ :: R, hR => by
    have ih := ofFields_known hn R fun g hg => hR g (List.mem_cons_of_mem _ hg)
    rw [ofFields.eq_def]; simp only
    rcases hR _ List.mem_cons_self with hmem | ⟨hname, halias, hdef⟩
    · obtain ⟨k, hk, hg⟩ := List.getElem_of_mem hmem
      have hk' : k < (ws.map (·.name)).length := by simpa using hk
      have hname : (ws.map (·.name))[k] = name := by simp [hg]
      have hc := claim_getElem hn hk' aliases
      have hi := idxOf?_getElem hn hk'
      rw [hname] at hc hi
      have hget : ws[k]? = some ⟨name, aliases, s, default⟩ := by
        rw [List.getElem?_eq_getElem hk, hg]
      simp [hc, hi, hget, knownPlan, of_self, ih]
    · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hdef
      have hi := List.idxOf?_eq_none_iff.mpr hname
      simp only at hv
      simp [claim_new hname halias, hi, hv, knownPlan, ih]

theorem applyFields_known {ws : List (Schema.Field Schema)} {vs : List Value}
    (hl : vs.length = ws.length) : ∀ (R : List (Schema.Field Schema)),
      applyFields (R.map (knownPlan ws)) vs = .ok (R.map (knownValue ws vs))
  | [] => by rw [List.map_nil, applyFields]; rfl
  | g :: R => by
    have ih := applyFields_known hl R
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
      rw [applyFields, List.getElem?_eq_getElem hk]
      simp [apply_same, ih, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]

theorem map_knownValue {ws : List (Schema.Field Schema)} {vs : List Value}
    (hn : (ws.map (·.name)).Nodup) (hl : vs.length = ws.length) :
    ws.map (knownValue ws vs) = vs := by
  apply List.ext_getElem (by simp [hl])
  intro j h1 h2
  have hj : j < (ws.map (·.name)).length := by simpa using h1
  have hi := idxOf?_getElem hn hj
  simp only [List.getElem_map] at hi
  simp [knownValue, hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

/-- Two records, matched field by field. -/
theorem of_record {t t' : String} {a a' : List Schema} {wfs rfs : List (Schema.Field Schema)}
    (hne : Schema.record t a wfs ≠ .record t' a' rfs)
    (hm : ∀ m ∈ ms, m.old ≠ .record t a wfs ∨ m.new ≠ .record t' a' rfs)
    (hc : (rfs.filterMap fun f => claim (wfs.map (·.name)) f.name f.aliases).Nodup)
    {ps : List (Plan.Field Plan)} (hf : ofFields ms wfs rfs = .ok ps) :
    of ms (.record t a wfs) (.record t' a' rfs) = .ok (.record t' ps) := by
  have hfind : ms.find? (fun m => m.old == .record t a wfs && m.new == .record t' a' rfs)
      = none := by
    simp only [List.find?_eq_none, Bool.and_eq_true, beq_iff_eq, not_and]
    intro m hm' ho
    exact (hm m hm').resolve_left (fun h => h ho)
  unfold of
  simp only [beq_eq_false_iff_ne.mpr hne, hfind, Bool.false_eq_true, ↓reduceIte]
  rw [unambiguous_eq (by simpa [List.filterMap_map, Function.comp_def] using hc)]
  simp [hf]

/-- A field added with a default, anywhere: every old field keeps its value, and the new one
takes its default. -/
theorem of_insertIdx {t t' : String} {a a' : List Schema} {ws : List (Schema.Field Schema)}
    {f : Schema.Field Schema} {i : Nat} {d : Value} (hi : i ≤ ws.length)
    (hn : (ws.map (·.name)).Nodup) (hname : f.name ∉ ws.map (·.name))
    (halias : ∀ x ∈ f.aliases, x ∉ ws.map (·.name)) (hd : f.default = some d)
    (hm : ∀ m ∈ ms, m.old ≠ .record t a ws ∨ m.new ≠ .record t' a' (ws.insertIdx i f)) :
    ∃ p, of ms (.record t a ws) (.record t' a' (ws.insertIdx i f)) = .ok p ∧
      ∀ vs : List Value, vs.length = ws.length →
        p.apply (.ctor 0 vs) = .ok (.ctor 0 (vs.insertIdx i d)) := by
  have hR : ∀ g ∈ ws.insertIdx i f, Known ws g := by
    intro g hg
    rcases (List.mem_insertIdx hi).mp hg with rfl | h
    · exact .inr ⟨hname, halias, by simp [hd]⟩
    · exact .inl h
  have hne : Schema.record t a ws ≠ .record t' a' (ws.insertIdx i f) := by
    intro h
    injection h with _ _ h
    have := congrArg List.length h
    rw [List.length_insertIdx_of_le_length hi] at this
    omega
  have hc : ((ws.insertIdx i f).filterMap fun g =>
      claim (ws.map (·.name)) g.name g.aliases).Nodup := by
    rw [filterMap_insertIdx (f := fun (g : Schema.Field Schema) => claim (ws.map (·.name)) g.name g.aliases)
      (claim_new hname halias), filterMap_claims hn]
    exact List.nodup_range
  refine ⟨_, of_record hne hm hc (ofFields_known hn _ hR), fun vs hl => ?_⟩
  rw [apply]
  rw [applyFields_known hl, Body.within_ok]
  simp only [map_insertIdx, map_knownValue hn hl]
  simp [knownValue, List.idxOf?_eq_none_iff.mpr hname, hd]

/-! Constructors. -/

/-- Each reader's constructor that takes one of the writer's with the same fields keeps them. -/
theorem ofCtors_same {cs : List (Schema.Ctor Schema)} :
    ∀ (R : List (Schema.Ctor Schema)) (index : Nat),
      (∀ r ∈ R, ∃ k c, claim (cs.map (·.name)) r.name r.aliases = some k ∧ cs[k]? = some c ∧
        c.fields = r.fields) →
      ofCtors ms cs R index = .ok (R.mapIdx fun j r =>
        (claim (cs.map (·.name)) r.name r.aliases).map fun k => (k, .to r.name (index + j) none))
  | [], _, _ => by rw [ofCtors]; rfl
  | ⟨name, aliases, fields⟩ :: R, index, hR => by
    have ih := ofCtors_same R (index + 1) fun r hr => hR r (List.mem_cons_of_mem _ hr)
    obtain ⟨k, c, hc, hk, hf⟩ := hR _ List.mem_cons_self
    simp only at hc hf
    rw [ofCtors.eq_def]
    simp only [hc, hk, hf, Schema.beqFields_refl, ↓reduceIte, ih, List.mapIdx_cons,
      Nat.add_zero, Option.map_some]
    congr 3
    funext j r
    rw [show index + 1 + j = index + (j + 1) by omega]

theorem pick_eq : ∀ (found : List (Option (Nat × Ctor Plan))) (off k : Nat) (c : Ctor Plan)
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

theorem applyCtor_to : ∀ (ctors : List (Ctor Plan)) (k : Nat) (vs : List Value) {name : String}
    {j : Nat}, ctors[k]? = some (.to name j none) → applyCtor ctors k vs = .ok (.ctor j vs)
  | [], _, _, _, _, h => by simp at h
  | _ :: _, 0, _, _, _, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    rw [applyCtor]
  | _ :: ctors, k + 1, vs, _, _, h => by
    rw [applyCtor]
    exact applyCtor_to ctors k vs (by simpa using h)

/-- Two sums, matched constructor by constructor. -/
theorem of_sum {t t' : String} {a a' : List Schema} {wcs rcs : List (Schema.Ctor Schema)}
    (hne : Schema.sum t a wcs ≠ .sum t' a' rcs)
    (hm : ∀ m ∈ ms, m.old ≠ .sum t a wcs ∨ m.new ≠ .sum t' a' rcs)
    (hc : (rcs.filterMap fun c => claim (wcs.map (·.name)) c.name c.aliases).Nodup)
    {found : List (Option (Nat × Ctor Plan))} (hf : ofCtors ms wcs rcs 0 = .ok found) :
    of ms (.sum t a wcs) (.sum t' a' rcs)
      = .ok (.sum t' (wcs.mapIdx fun k c => pick found k c.name)) := by
  have hfind : ms.find? (fun m => m.old == .sum t a wcs && m.new == .sum t' a' rcs)
      = none := by
    simp only [List.find?_eq_none, Bool.and_eq_true, beq_iff_eq, not_and]
    intro m hm' ho
    exact (hm m hm').resolve_left (fun h => h ho)
  unfold of
  simp only [beq_eq_false_iff_ne.mpr hne, hfind, Bool.false_eq_true, ↓reduceIte]
  rw [unambiguous_eq (by simpa [List.filterMap_map, Function.comp_def] using hc)]
  simp [hf]

/-- A renamed constructor reads through its former name: the data's `k`th constructor is the
reader's, under its new name, and every value keeps its constructor and its fields. -/
theorem of_rename {t t' : String} {a a' : List Schema} {cs : List (Schema.Ctor Schema)}
    {k : Nat} (hk : k < cs.length) {c : Schema.Ctor Schema}
    (hn : (cs.map (·.name)).Nodup) (hname : c.name ∉ cs.map (·.name))
    (hwas : cs[k].name ∈ c.aliases)
    (halias : ∀ x ∈ c.aliases, x ∈ cs.map (·.name) → x = cs[k].name)
    (hfields : c.fields = cs[k].fields)
    (hm : ∀ m ∈ ms, m.old ≠ .sum t a cs ∨ m.new ≠ .sum t' a' (cs.set k c)) :
    ∃ p, of ms (.sum t a cs) (.sum t' a' (cs.set k c)) = .ok p ∧
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
      cs[k']? = some c' ∧ c'.fields = r.fields := by
    intro r hr
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hr
    have hj'' : j < cs.length := by simpa using hj
    refine ⟨j, cs[j], hclaim j hj, List.getElem?_eq_getElem hj'', ?_⟩
    rw [List.getElem_set]
    split
    · subst k; exact hfields.symm
    · rfl
  have hne : Schema.sum t a cs ≠ .sum t' a' (cs.set k c) := by
    intro h
    injection h with _ _ h
    have := congrArg (·[k]?) h
    simp only [List.getElem?_set_self hk, List.getElem?_eq_getElem hk, Option.some.injEq] at this
    exact hname (this ▸ List.mem_map_of_mem (f := (·.name)) (List.getElem_mem hk))
  have hc : ((cs.set k c).filterMap fun r =>
      claim (cs.map (·.name)) r.name r.aliases).Nodup := by
    rw [filterMap_eq_range hclaim]
    exact List.nodup_range
  refine ⟨_, of_sum hne hm hc (ofCtors_same _ 0 hR), fun j vs hj => ?_⟩
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
  rw [apply, applyCtor_to _ j vs (name := (cs.set k c)[j].name) (j := j)]
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
  refine ⟨.convert new.schema.name (Schema.Migration.of old new f).run, ?_, ?_⟩
  · unfold Schema.Plan.of
    simp [beq_eq_false_iff_ne.mpr hne, Schema.Migration.of]
  · simp only [decodeWith, readWith, read_write h, Schema.Plan.apply, Schema.Migration.of,
      old.ofValue_toValue, Option.map_some, new.ofValue_toValue]

end Body

end Lanes
