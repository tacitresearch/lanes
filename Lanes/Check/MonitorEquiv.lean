/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Check.Monitor
public import Lanes.Check.WorldEquiv

/-!
# Monitors compare as sets

`==` on monitors is equal length and inclusion one way, up to `Service.State.equiv`. Because a
monitor holds no state twice (`Monitor.distinct`), that is equality of the candidates as sets
(`Monitor.beq_iff`), so it is an equivalence, and the hash, a sum over the candidates, agrees
with it. These are the instances the search needs of the state of a monitored driver
(`Check.search_sound`), together with the same for pairs.
-/

@[expose] public section

namespace Lanes

theorem prod_beq_iff {α β : Type} [BEq α] [BEq β] {a b : α × β} :
    (a == b) = true ↔ (a.1 == b.1) = true ∧ (a.2 == b.2) = true :=
  Bool.and_eq_true_iff

instance {α β : Type} [BEq α] [BEq β] [EquivBEq α] [EquivBEq β] : EquivBEq (α × β) where
  symm h := prod_beq_iff.mpr ⟨BEq.symm (prod_beq_iff.mp h).1, BEq.symm (prod_beq_iff.mp h).2⟩
  trans h₁ h₂ := prod_beq_iff.mpr ⟨BEq.trans (prod_beq_iff.mp h₁).1 (prod_beq_iff.mp h₂).1,
    BEq.trans (prod_beq_iff.mp h₁).2 (prod_beq_iff.mp h₂).2⟩

instance {α β : Type} [BEq α] [BEq β] [Hashable α] [Hashable β] [LawfulHashable α]
    [LawfulHashable β] : LawfulHashable (α × β) where
  hash_eq a b h := by
    simp only [hash, hash_eq (prod_beq_iff.mp h).1, hash_eq (prod_beq_iff.mp h).2]

/--
Pigeonhole, up to an equivalence `r`: if no two members of `a` are equivalent and `g` sends each
to an equivalent member of `b`, then `b` is those images and a remainder.
-/
theorem exists_perm_map_append {α : Type} {r : α → α → Bool}
    (symm : ∀ {x y}, r x y = true → r y x = true)
    (trans : ∀ {x y z}, r x y = true → r y z = true → r x z = true) {g : α → α} :
    ∀ {a b : List α}, a.Pairwise (fun x y => r y x = false) →
      (∀ x ∈ a, g x ∈ b ∧ r x (g x) = true) → ∃ rest, b.Perm (a.map g ++ rest)
  | [], b, _, _ => ⟨b, .refl _⟩
  | x :: a, b, ha, hg => by
    obtain ⟨s, t, rfl⟩ := List.append_of_mem (hg x (.head _)).1
    obtain ⟨hxa, ha⟩ := List.pairwise_cons.mp ha
    have hrest : ∀ z ∈ a, g z ∈ s ++ t ∧ r z (g z) = true := fun z hz => by
      obtain ⟨hmem, hzg⟩ := hg z (List.mem_cons_of_mem _ hz)
      refine ⟨?_, hzg⟩
      rcases List.mem_append.mp hmem with h | h
      · exact List.mem_append_left _ h
      · rcases List.mem_cons.mp h with h | h
        · have hzx := trans (h ▸ hzg) (symm (hg x (.head _)).2)
          simp [hxa z hz] at hzx
        · exact List.mem_append_right _ h
    obtain ⟨rest, hperm⟩ := exists_perm_map_append (r := r) symm trans ha hrest
    exact ⟨rest, List.perm_middle.trans (hperm.cons _)⟩

theorem foldl_add_eq_of_perm {α : Type} {l₁ l₂ : List α} (h : l₁.Perm l₂) (f : α → UInt64) :
    l₁.foldl (fun acc x => acc + f x) 0 = l₂.foldl (fun acc x => acc + f x) 0 :=
  h.foldl_eq'
    (fun _ _ _ _ z => by rw [UInt64.add_assoc, UInt64.add_comm (f _), UInt64.add_assoc]) 0

variable {σ : Signature} {S : Type} [BEq S]

namespace Service.State

theorem equiv_refl [ReflBEq S] (a : State σ S) : a.equiv a = true := by
  simp [equiv, List.isPerm_iff]

theorem equiv_symm [PartialEquivBEq S] {a b : State σ S} (h : a.equiv b = true) :
    b.equiv a = true := by
  simp only [equiv, Bool.and_eq_true, List.isPerm_iff] at h ⊢
  exact ⟨⟨BEq.symm h.1.1, h.1.2.symm⟩, h.2.symm⟩

theorem equiv_trans [PartialEquivBEq S] {a b c : State σ S} (h₁ : a.equiv b = true)
    (h₂ : b.equiv c = true) : a.equiv c = true := by
  simp only [equiv, Bool.and_eq_true, List.isPerm_iff] at h₁ h₂ ⊢
  exact ⟨⟨BEq.trans h₁.1.1 h₂.1.1, h₁.1.2.trans h₂.1.2⟩, h₁.2.trans h₂.2⟩

theorem hash_eq_of_equiv [Hashable S] [LawfulHashable S] [Hashable σ.In] [Hashable σ.Out]
    {a b : State σ S} (h : a.equiv b = true) : a.hash = b.hash := by
  simp only [equiv, Bool.and_eq_true, List.isPerm_iff] at h
  simp only [hash, hash_eq h.1.1, foldl_add_eq_of_perm h.1.2, foldl_add_eq_of_perm h.2]

end Service.State

namespace Check.Monitor

open Service (State)

/-- `a` is included in `b`, up to `State.equiv`. -/
def Within (a b : List (State σ S)) : Prop :=
  ∀ s ∈ a, ∃ t ∈ b, s.equiv t = true

theorem beq_iff_length_within {a b : Monitor σ S} : (a == b) = true ↔
    a.candidates.length = b.candidates.length ∧ Within a.candidates b.candidates := by
  simp [BEq.beq, Within]

/-- A set of pairwise different states included in `b` is matched one to one into `b`. -/
theorem exists_perm_of_within [PartialEquivBEq S] {a b : List (State σ S)}
    (ha : State.Distinct a) (h : Within a b) : ∃ (g : State σ S → State σ S) (rest : _),
      (∀ s ∈ a, s.equiv (g s) = true) ∧ b.Perm (a.map g ++ rest) := by
  have hg : ∀ s ∈ a, (b.find? (s.equiv ·)).getD s ∈ b ∧
      s.equiv ((b.find? (s.equiv ·)).getD s) = true := by
    intro s hs
    obtain ⟨t, ht, hst⟩ := h s hs
    cases hfind : b.find? (s.equiv ·) with
    | none => simp [List.find?_eq_none.mp hfind t ht] at hst
    | some u => exact ⟨List.mem_of_find?_eq_some hfind, List.find?_some hfind⟩
  obtain ⟨rest, hrest⟩ :=
    exists_perm_map_append (r := State.equiv) State.equiv_symm State.equiv_trans ha hg
  exact ⟨_, rest, fun s hs => (hg s hs).2, hrest⟩

/-- `==` monitors hold the same candidates in some order, up to `State.equiv`. -/
theorem exists_perm_of_beq [PartialEquivBEq S] {a b : Monitor σ S} (h : (a == b) = true) :
    ∃ g : State σ S → State σ S,
      (∀ s ∈ a.candidates, s.equiv (g s) = true) ∧ b.candidates.Perm (a.candidates.map g) := by
  obtain ⟨hlength, hab⟩ := beq_iff_length_within.mp h
  obtain ⟨g, rest, hg, hperm⟩ := exists_perm_of_within a.distinct hab
  have hrest : rest = [] := List.eq_nil_of_length_eq_zero (by
    have := hperm.length_eq
    simp only [List.length_append, List.length_map] at this
    omega)
  exact ⟨g, hg, by simpa [hrest] using hperm⟩

/-- Inclusion both ways is what `==` computes from the lengths and inclusion one way. -/
theorem beq_iff [PartialEquivBEq S] {a b : Monitor σ S} : (a == b) = true ↔
    Within a.candidates b.candidates ∧ Within b.candidates a.candidates := by
  constructor
  · intro h
    obtain ⟨g, hg, hperm⟩ := exists_perm_of_beq h
    refine ⟨(beq_iff_length_within.mp h).2, fun t ht => ?_⟩
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp (hperm.mem_iff.mp ht)
    exact ⟨s, hs, State.equiv_symm (hg s hs)⟩
  · rintro ⟨hab, hba⟩
    obtain ⟨_, _, _, hb⟩ := exists_perm_of_within a.distinct hab
    obtain ⟨_, _, _, ha⟩ := exists_perm_of_within b.distinct hba
    have := hb.length_eq
    have := ha.length_eq
    simp only [List.length_append, List.length_map] at *
    exact beq_iff_length_within.mpr ⟨by omega, hab⟩

theorem Within.trans [PartialEquivBEq S] {a b c : List (State σ S)} (hab : Within a b)
    (hbc : Within b c) : Within a c := fun s hs =>
  have ⟨t, ht, hst⟩ := hab s hs
  have ⟨u, hu, htu⟩ := hbc t ht
  ⟨u, hu, State.equiv_trans hst htu⟩

instance [EquivBEq S] : EquivBEq (Monitor σ S) where
  rfl := beq_iff_length_within.mpr ⟨rfl, fun s hs => ⟨s, hs, s.equiv_refl⟩⟩
  symm h := beq_iff.mpr (beq_iff.mp h).symm
  trans h₁ h₂ := beq_iff.mpr ⟨(beq_iff.mp h₁).1.trans (beq_iff.mp h₂).1,
    (beq_iff.mp h₂).2.trans (beq_iff.mp h₁).2⟩

instance [EquivBEq S] [Hashable S] [LawfulHashable S] [Hashable σ.In] [Hashable σ.Out] :
    LawfulHashable (Monitor σ S) where
  hash_eq a b h := by
    obtain ⟨g, hg, hperm⟩ := exists_perm_of_beq h
    have hmap : (a.candidates.map g).map State.hash = a.candidates.map State.hash := by
      rw [List.map_map]
      exact List.map_congr_left fun s hs => (State.hash_eq_of_equiv (hg s hs)).symm
    simp only [hash]
    rw [foldl_add_eq_of_perm hperm, ← List.foldl_map (f := State.hash)
      (g := fun h x => h + mixHash 7 x), ← List.foldl_map (f := State.hash)
      (g := fun h x => h + mixHash 7 x), hmap]

theorem ok_congr {a b : Monitor σ S} (h : (a == b) = true) : a.ok = b.ok := by
  have hlength := (beq_iff_length_within.mp h).1
  rw [ok, ok, Bool.eq_iff_iff, Bool.not_eq_true', Bool.not_eq_true', ← Bool.not_eq_true,
    ← Bool.not_eq_true, List.isEmpty_iff_length_eq_zero, List.isEmpty_iff_length_eq_zero, hlength]

end Check.Monitor

/-- The refinement property cannot tell merged worlds apart. -/
theorem World.Equiv.holds_refines {sys : System σ} {D : Type} [BEq D] {env : EnvModel σ}
    {a b : World sys (D × Check.Monitor σ S)} (h : World.Equiv env a b) (name : String) :
    (Check.refines name).holds a = (Check.refines name).holds b :=
  Check.Monitor.ok_congr (prod_beq_iff.mp h.driver).2

end Lanes
