/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Semantics.Seq

/-!
# Labelled transition systems

The transition systems that every spec, model and system semantics of Lanes is: a labelled
transition relation, its runs, internal steps (`τ`) and the saturated steps that skip them, and
infinite runs.

The definitions and the names follow CSLib's (`leanprover/cslib`, Apache-2.0, by Fabrizio
Montesi and Ching-Tsun Chou), which Lanes used before it had its own, so a proof written against
CSLib reads the same here. Only what Lanes uses is written again. The reflexive transitive
closure follows the one of the Lean community's mathematics library (`Relation.ReflTransGen`).

## Main definitions

- `ReflTransGen r`: zero or more steps of `r`.
- `LTS State Label`: a labelled transition relation.
- `LTS.MTr`: a run along a list of labels.
- `HasTau`: a type of labels with an internal label `τ`.
- `LTS.τSTr`, `LTS.STr`, `LTS.SMTr`: internal steps, a saturated step, a saturated run.
- `LTS.OmegaExecution`: an infinite run.

## Main statements

- `LTS.sTr_τSTr_iff`: a saturated `τ` step is a run of internal steps.
- `LTS.STr.comp`, `LTS.SMTr.comp`: saturated steps and runs compose.
-/

@[expose] public section

namespace Lanes

universe u v

/-! ### Zero or more steps of a relation -/

/-- Zero or more steps of `r` from `a`. -/
inductive ReflTransGen {α : Sort u} (r : α → α → Prop) (a : α) : α → Prop where
  /-- No step. -/
  | refl : ReflTransGen r a a
  /-- Some steps, then one more. -/
  | tail {b c : α} : ReflTransGen r a b → r b c → ReflTransGen r a c

namespace ReflTransGen

variable {α : Sort u} {r : α → α → Prop} {a b c : α}

/-- One step is a run. -/
theorem single (hab : r a b) : ReflTransGen r a b :=
  tail refl hab

/-- Runs compose. -/
theorem trans (hab : ReflTransGen r a b) (hbc : ReflTransGen r b c) : ReflTransGen r a c := by
  induction hbc with
  | refl => exact hab
  | tail _ hcd ih => exact tail ih hcd

/-- A step, then a run, is a run. -/
theorem head (hab : r a b) (hbc : ReflTransGen r b c) : ReflTransGen r a c :=
  trans (single hab) hbc

/-- Induction on a run from its first step. -/
@[elab_as_elim]
theorem head_induction_on {motive : ∀ a : α, ReflTransGen r a b → Prop} {a : α}
    (h : ReflTransGen r a b) (refl : motive b refl)
    (head : ∀ {a c} (h' : r a c) (h : ReflTransGen r c b), motive c h → motive a (h.head h')) :
    motive a h := by
  induction h with
  | refl => exact refl
  | @tail b' c' hab' hbc ih =>
    apply ih (motive := fun a hab => motive a (hab.tail hbc))
    · exact head hbc _ refl
    · exact fun h₁ h₂ => head h₁ _

end ReflTransGen

/-! ### Transition systems and their runs -/

/-- A labelled transition system: a transition relation between states, labelled. -/
structure LTS (State : Type u) (Label : Type v) where
  /-- The transition relation. -/
  Tr : State → Label → State → Prop

namespace LTS

variable {State : Type u} {Label : Type v} {lts : LTS State Label}

/-- A run of `lts` along a list of labels. -/
inductive MTr (lts : LTS State Label) : State → List Label → State → Prop where
  /-- The empty run. -/
  | refl {s : State} : lts.MTr s [] s
  /-- A step, then a run. -/
  | stepL {s1 : State} {μ : Label} {s2 : State} {μs : List Label} {s3 : State} :
    lts.Tr s1 μ s2 → lts.MTr s2 μs s3 → lts.MTr s1 (μ :: μs) s3

/-- One step is a run. -/
theorem MTr.single (lts : LTS State Label) {s1 s2 : State} {μ : Label} (h : lts.Tr s1 μ s2) :
    lts.MTr s1 [μ] s2 :=
  .stepL h .refl

/-- A run, then a step, is a run. -/
theorem MTr.stepR (lts : LTS State Label) {s1 s2 s3 : State} {μs : List Label} {μ : Label}
    (h1 : lts.MTr s1 μs s2)
    (h2 : lts.Tr s2 μ s3) : lts.MTr s1 (μs ++ [μ]) s3 := by
  induction h1 with
  | refl => exact .single lts h2
  | stepL h _ ih => exact .stepL h (ih h2)

/-- Runs compose. -/
theorem MTr.comp (lts : LTS State Label) {s1 s2 s3 : State} {μs1 μs2 : List Label}
    (h1 : lts.MTr s1 μs1 s2)
    (h2 : lts.MTr s2 μs2 s3) : lts.MTr s1 (μs1 ++ μs2) s3 := by
  induction h1 with
  | refl => exact h2
  | stepL h _ ih => exact .stepL h (ih h2)

/-- `s2` can be reached from `s1` by some run. -/
def CanReach (lts : LTS State Label) (s1 s2 : State) : Prop :=
  ∃ μs, lts.MTr s1 μs s2

/-- Every state can reach itself. -/
theorem CanReach.refl (lts : LTS State Label) (s : State) : lts.CanReach s s :=
  ⟨[], .refl⟩

end LTS

/-! ### Internal steps -/

/-- A type of labels with an internal label, `τ`. -/
class HasTau (Label : Type v) where
  /-- The internal label. -/
  τ : Label

/-- Whether a label is `τ` can be decided. -/
abbrev DecidableEqTau (α : Type v) [HasTau α] := ∀ a : α, Decidable (a = HasTau.τ)

/-- `none` is the internal label of `Option`. -/
instance instHasTauOption {α : Type v} : HasTau (Option α) := ⟨.none⟩

/-- Whether an option is `none` can be decided. -/
instance instDecidableEqTauOption {α : Type v} : DecidableEqTau (Option α) :=
  fun a => Option.decidableEqNone a

namespace LTS

variable {State : Type u} {Label : Type v} [HasTau Label] {lts : LTS State Label}
  {s s' s1 s2 s3 s4 : State} {μ : Label}

/-- Zero or more internal steps. -/
def τSTr (lts : LTS State Label) : State → State → Prop :=
  ReflTransGen fun s s' => lts.Tr s HasTau.τ s'

/-- No internal step. -/
theorem τSTr.refl : lts.τSTr s s :=
  ReflTransGen.refl

/-- A saturated step: internal steps, the step, internal steps; or no step at all for `τ`. -/
inductive STr (lts : LTS State Label) : State → Label → State → Prop where
  /-- No step, read as `τ`. -/
  | refl {s : State} : lts.STr s HasTau.τ s
  /-- Internal steps, a step labelled `μ`, internal steps. -/
  | tr {s1 s2 s3 s4 : State} {μ : Label} :
    lts.τSTr s1 s2 → lts.Tr s2 μ s3 → lts.τSTr s3 s4 → lts.STr s1 μ s4

/-- A step is a saturated step. -/
theorem STr.single (h : lts.Tr s μ s') : lts.STr s μ s' :=
  .tr .refl h .refl

/-- A saturated `τ` step is a run of internal steps. -/
theorem sTr_τSTr_iff (lts : LTS State Label) : lts.STr s HasTau.τ s' ↔ lts.τSTr s s' := by
  constructor
  · intro h
    cases h with
    | refl => exact .refl
    | tr h1 h2 h3 => exact ReflTransGen.trans h1 (ReflTransGen.head h2 h3)
  · intro h
    cases h with
    | refl => exact .refl
    | tail h1 h2 => exact .tr h1 h2 .refl

/-- Saturated `τ` steps compose. -/
theorem STr.trans_τ (h1 : lts.STr s1 HasTau.τ s2) (h2 : lts.STr s2 HasTau.τ s3) :
    lts.STr s1 HasTau.τ s3 := by
  rw [sTr_τSTr_iff] at h1 h2 ⊢
  exact ReflTransGen.trans h1 h2

/-- Saturated steps compose with saturated `τ` steps on both sides. -/
theorem STr.comp (h1 : lts.STr s1 HasTau.τ s2) (h2 : lts.STr s2 μ s3)
    (h3 : lts.STr s3 HasTau.τ s4) : lts.STr s1 μ s4 := by
  rw [sTr_τSTr_iff] at h1 h3
  cases h2 with
  | refl => exact (sTr_τSTr_iff lts).mpr (ReflTransGen.trans h1 h3)
  | tr hτ1 htr hτ2 => exact .tr (ReflTransGen.trans h1 hτ1) htr (ReflTransGen.trans hτ2 h3)

/-- A saturated run: saturated steps along the visible labels. -/
inductive SMTr (lts : LTS State Label) : State → List Label → State → Prop where
  /-- Internal steps only. -/
  | τ {s s' : State} : lts.STr s HasTau.τ s' → lts.SMTr s [] s'
  /-- A saturated step, then a saturated run. -/
  | stepL {s1 s2 s3 : State} {μ : Label} {μs : List Label} :
    lts.STr s1 μ s2 → lts.SMTr s2 μs s3 → lts.SMTr s1 (μ :: μs) s3

/-- The empty saturated run. -/
theorem SMTr.refl (lts : LTS State Label) (s : State) : lts.SMTr s [] s :=
  .τ .refl

/-- Saturated runs compose. -/
theorem SMTr.comp {μs₁ μs₂ : List Label} (h₁ : lts.SMTr s1 μs₁ s2) (h₂ : lts.SMTr s2 μs₂ s3) :
    lts.SMTr s1 (μs₁ ++ μs₂) s3 := by
  induction h₁ with
  | τ htr =>
    cases h₂ with
    | τ htr' => exact .τ (htr.trans_τ htr')
    | stepL hstr hmstr => exact .stepL (htr.comp hstr .refl) hmstr
  | stepL hstr _ ih => exact .stepL hstr (ih h₂)

/-- A run is a saturated run. -/
theorem SMTr.fromMTr {μs : List Label} (h : lts.MTr s μs s') : lts.SMTr s μs s' := by
  induction h with
  | refl => exact .refl lts _
  | stepL htr _ ih => exact .stepL (.single htr) ih

/-- Internal steps are a saturated run along no label. -/
theorem sMTr_τSTr_iff : lts.τSTr s s' ↔ lts.SMTr s [] s' := by
  constructor
  · intro h
    exact .τ ((sTr_τSTr_iff lts).mpr h)
  · intro h
    cases h with
    | τ h => exact (sTr_τSTr_iff lts).mp h

end LTS

/-! ### Infinite runs -/

/-- An infinite run: the `i`th step goes from state `ss i`, labelled `μs i`, to `ss (i + 1)`. -/
def LTS.OmegaExecution {State : Type u} {Label : Type v} (lts : LTS State Label)
    (ss : ωSequence State) (μs : ωSequence Label) : Prop :=
  ∀ i, lts.Tr (ss i) (μs i) (ss (i + 1))

end Lanes
