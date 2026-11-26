/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Actors.Monotone

/-!
# What a step does, counted

`Below` is enough for an invariant: it says no message is in flight that was not before. A
refinement has to count. A request in flight is one the spec is still waiting to serve, and an
output waiting is one the spec owes, so one too many or one too few is a different behaviour.

`Loses` is `Below` with the counting kept: the outputs waiting are the same list, and the
messages in flight are a sublist, so a message is there no more often than before. Every step
of the semantics is an input, an output handed over, or an actor moving (`grow`), followed by
losing messages and timers. `Lanes.Semantics.Steps` turns that into a proof rule for refinement.
-/

@[expose] public section

namespace Lanes

variable {σ : Signature} {sys : System σ}

namespace Effect

variable {i : σ.Id}

theorem emits_nil : emits ([] : List (Effect σ i)) = [] := rfl

theorem emits_append (a b : List (Effect σ i)) : emits (a ++ b) = emits a ++ emits b :=
  List.filterMap_append

theorem emits_cons (eff : Effect σ i) (effs : List (Effect σ i)) :
    emits (eff :: effs) = (match eff with | .emit out => [out] | _ => []) ++ emits effs := by
  cases eff <;> rfl

theorem emits_map {α : Type} (f : α → Effect σ i) (l : List α) :
    emits (l.map f) = l.filterMap fun a => match f a with | .emit out => some out | _ => none := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, emits_cons, ih, List.filterMap_cons]
    cases f a <;> rfl

theorem sends_append (a b : List (Effect σ i)) : sends i (a ++ b) = sends i a ++ sends i b :=
  List.filterMap_append

end Effect

namespace SysState

/-- `c'` is `c` with some messages and timers gone. Which actors are up is not compared. -/
structure Loses (c' c : SysState sys) : Prop where
  state : c'.state = c.state
  net : c'.net.Sublist c.net
  timers : ∀ i msg, msg ∈ c'.timers i → msg ∈ c.timers i
  outbox : c'.outbox = c.outbox

theorem Loses.refl (c : SysState sys) : c.Loses c :=
  ⟨rfl, List.Sublist.refl _, fun _ _ h => h, rfl⟩

theorem Loses.trans {c₁ c₂ c₃ : SysState sys} (h₁ : c₁.Loses c₂) (h₂ : c₂.Loses c₃) :
    c₁.Loses c₃ :=
  ⟨h₁.state.trans h₂.state, h₁.net.trans h₂.net,
    fun i msg h => h₂.timers i msg (h₁.timers i msg h), h₁.outbox.trans h₂.outbox⟩

theorem Loses.below {c' c : SysState sys} (h : c'.Loses c) : c'.Below c :=
  ⟨h.state, fun _ he => h.net.subset he, h.timers, fun _ ho => h.outbox ▸ ho⟩

theorem performAll_net (c : SysState sys) (i : σ.Id) (effs : List (Effect σ i)) :
    (c.performAll i effs).net = c.net ++ Effect.sends i effs := by
  induction effs generalizing c with
  | nil => simp [Effect.sends]
  | cons eff effs ih =>
    rw [performAll_cons, ih]
    cases eff <;> simp [perform, Effect.sends]

theorem performAll_outbox (c : SysState sys) (i : σ.Id) (effs : List (Effect σ i)) :
    (c.performAll i effs).outbox = c.outbox ++ Effect.emits effs := by
  induction effs generalizing c with
  | nil => simp [Effect.emits]
  | cons eff effs ih =>
    rw [performAll_cons, ih]
    cases eff <;> simp [perform, Effect.emits]

theorem settle_outbox (env : EnvModel σ) (c : SysState sys) (i : σ.Id)
    (r : sys.State i × List (Effect σ i)) :
    (c.settle env i r).outbox = c.outbox ++ Effect.emits r.2 := by
  unfold settle
  split <;> simp [down, performAll_outbox]

theorem settle_net_sublist (env : EnvModel σ) (c : SysState sys) (i : σ.Id)
    (r : sys.State i × List (Effect σ i)) :
    (c.settle env i r).net.Sublist (c.net ++ Effect.sends i r.2) := by
  have hnet := performAll_net ({ c with state := update c.state i r.1 }) i r.2
  unfold settle
  split
  · exact hnet ▸ List.filter_sublist
  · exact hnet ▸ List.Sublist.refl _

/-- Whatever was lost before an actor moved, and whether or not it stopped, the result is
`grow` with messages and timers lost. -/
theorem Loses.settle {c₀ c : SysState sys} (h : c₀.Loses c) (env : EnvModel σ) (i : σ.Id)
    (r : sys.State i × List (Effect σ i)) : (c₀.settle env i r).Loses (c.grow i r) where
  state := (Below.settle h.below env i r).state
  net := (settle_net_sublist env c₀ i r).trans
    (List.Sublist.append h.net (List.Sublist.refl _))
  timers := (Below.settle h.below env i r).timers
  outbox := by rw [settle_outbox, h.outbox]; rfl

theorem Loses.handle {c₀ c : SysState sys} (h : c₀.Loses c) (env : EnvModel σ) (i : σ.Id)
    (msg : σ.Msg i) :
    (c₀.handle env i msg).Loses (c.grow i ((sys.actor i).step (c.state i) msg)) := by
  rw [← congrFun h.state i]
  exact Loses.settle h env i _

theorem Loses.startActor (c : SysState sys) (env : EnvModel σ) (i : σ.Id) :
    (c.startActor env i).Loses (c.grow i ((sys.actor i).recover (c.state i))) :=
  Loses.settle (c₀ := { c with up := update c.up i true }) (c := c)
    ⟨rfl, List.Sublist.refl _, fun _ _ h => h, rfl⟩ env i _

theorem Loses.down (env : EnvModel σ) (c : SysState sys) (i : σ.Id) : (c.down env i).Loses c := by
  refine ⟨rfl, List.filter_sublist, fun j m hm => ?_, rfl⟩
  by_cases hj : j = i
  · subst hj; simp [SysState.down] at hm
  · simpa [SysState.down, hj] using hm

end SysState

end Lanes
