/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Actors.Step
public import Lanes.Data.List

/-!
# Steps and runs in closed form

`SysState.settle` performs a step's effects one at a time. `SysState.settle_eq` says what that
leaves: the messages the effects send (`Effect.sends`), the timers after them (`Effect.retime`)
and the outputs they emit (`Effect.emits`), each added at once. A proof that follows a state
through a step rewrites with it and then reasons about lists.

The rest is runs whose result is known: inputs put in, outputs handed over.
-/

@[expose] public section

namespace Lanes

variable {σ : Signature} {sys : System σ}

namespace Effect

variable {i : σ.Id}

def sends (i : σ.Id) (effs : List (Effect σ i)) : List (Envelope σ) :=
  effs.filterMap fun
    | .send to msg => some ⟨some i, to, msg⟩
    | _ => none

def armed (effs : List (Effect σ i)) : List (σ.Msg i) :=
  effs.filterMap fun
    | .after _ msg => some msg
    | _ => none

def emits (effs : List (Effect σ i)) : List σ.Out :=
  effs.filterMap fun
    | .emit out => some out
    | _ => none

/-- An actor's timers after its effects. -/
def retime (effs : List (Effect σ i)) (timers : List (σ.Msg i)) : List (σ.Msg i) :=
  effs.foldl (fun timers eff =>
    match eff with
    | .after _ msg => if msg ∈ timers then timers else timers ++ [msg]
    | .cancel msg => timers.erase msg
    | _ => timers) timers

theorem mem_sends {effs : List (Effect σ i)} {e : Envelope σ} :
    e ∈ sends i effs ↔ e.src = some i ∧ .send e.dst e.msg ∈ effs := by
  obtain ⟨src, dst, msg⟩ := e
  induction effs with
  | nil => simp [sends]
  | cons eff effs ih =>
    simp only [sends, List.filterMap_cons, List.mem_cons] at ih ⊢
    cases eff <;> simp only [List.mem_cons, ih, reduceCtorEq, false_or]
    simp only [Envelope.mk.injEq, send.injEq]
    exact ⟨fun h => h.elim (fun h => ⟨h.1, .inl h.2⟩) fun h => ⟨h.1, .inr h.2⟩,
      fun h => h.2.elim (fun h' => .inl ⟨h.1, h'⟩) fun h' => .inr ⟨h.1, h'⟩⟩

theorem mem_armed {effs : List (Effect σ i)} {msg : σ.Msg i} :
    msg ∈ armed effs ↔ ∃ delay, .after delay msg ∈ effs := by
  induction effs with
  | nil => simp [armed]
  | cons eff effs ih =>
    simp only [armed, List.filterMap_cons, List.mem_cons] at ih ⊢
    cases eff <;> simp only [List.mem_cons, ih, reduceCtorEq, false_or]
    simp only [after.injEq, exists_or, exists_eq_left]

theorem emits_map_emit (outs : List σ.Out) : emits (outs.map (emit (self := i))) = outs := by
  induction outs with
  | nil => rfl
  | cons out outs ih => simpa [emits] using ih

theorem sends_map_emit (outs : List σ.Out) : sends i (outs.map emit) = [] := by
  induction outs with
  | nil => rfl
  | cons out outs ih => simp [sends]

theorem armed_map_emit (outs : List σ.Out) : armed (outs.map (emit (self := i))) = [] := by
  induction outs with
  | nil => rfl
  | cons out outs ih => simp [armed]

/-- Effects rewritten one by one stop the actor exactly when the originals do. -/
theorem any_isStop_flatMap {τ : Signature} {j : τ.Id} {f : Effect σ i → List (Effect τ j)}
    (h : ∀ eff, (f eff).any isStop = eff.isStop) (effs : List (Effect σ i)) :
    (effs.flatMap f).any isStop = effs.any isStop := by
  rw [List.any_flatMap]
  exact congrArg effs.any (funext h)

theorem any_isStop_map {τ : Signature} {j : τ.Id} {f : Effect σ i → Effect τ j}
    (h : ∀ eff, (f eff).isStop = eff.isStop) (effs : List (Effect σ i)) :
    (effs.map f).any isStop = effs.any isStop := by
  rw [List.any_map]
  exact congrArg effs.any (funext h)

end Effect

namespace SysState

variable {env : EnvModel σ}

theorem performAll_eq (c : SysState sys) (i : σ.Id) (effs : List (Effect σ i)) :
    c.performAll i effs = { c with
      net := c.net ++ Effect.sends i effs
      timers := update c.timers i (Effect.retime effs (c.timers i))
      outbox := c.outbox ++ Effect.emits effs } := by
  induction effs generalizing c with
  | nil => simp [Effect.sends, Effect.emits, Effect.retime]
  | cons eff effs ih =>
    rw [performAll_cons, ih]
    cases eff <;>
      simp [perform, Effect.sends, Effect.emits, Effect.retime, List.append_assoc, update_update]

/-- A step in full: the new state and what the effects add, then the actor taken down if one
of them is `stop`. -/
theorem settle_eq (env : EnvModel σ) (c : SysState sys) (i : σ.Id)
    (r : sys.State i × List (Effect σ i)) :
    c.settle env i r =
      if r.2.any Effect.isStop then
        ({ c with
          state := update c.state i r.1
          net := c.net ++ Effect.sends i r.2
          timers := update c.timers i (Effect.retime r.2 (c.timers i))
          outbox := c.outbox ++ Effect.emits r.2 } : SysState sys).down env i
      else
        { c with
          state := update c.state i r.1
          net := c.net ++ Effect.sends i r.2
          timers := update c.timers i (Effect.retime r.2 (c.timers i))
          outbox := c.outbox ++ Effect.emits r.2 } := by
  simp only [settle, performAll_eq]

/-- An actor's step does not look at the messages in flight: one that stays in flight could as
well be lost after the step as before it. -/
theorem settle_erase (c : SysState sys) (i : σ.Id) (r : sys.State i × List (Effect σ i))
    {e : Envelope σ} (hmem : e ∈ c.net) (hlossy : (env.link e.src e.dst).lossy = true) :
    e ∈ (c.settle env i r).net ∧
      ({ c with net := c.net.erase e } : SysState sys).settle env i r =
        { c.settle env i r with net := (c.settle env i r).net.erase e } := by
  simp only [settle_eq]
  split
  · simp only [down]
    refine ⟨by simp [hmem, hlossy], ?_⟩
    rw [List.erase_filter, List.erase_append_left _ hmem]
  · exact ⟨by simp [hmem], by rw [List.erase_append_left _ hmem]⟩

theorem run_inputs (env : EnvModel σ) (c : SysState sys) (xs : List σ.In) :
    c.run env (xs.map .input) = some { c with
      net := c.net ++ xs.map fun x => ⟨none, (sys.accept x).1, (sys.accept x).2⟩ } := by
  induction xs generalizing c with
  | nil => simp [run]
  | cons x xs ih => simp [run, step, ih, List.append_assoc]

/-- Handing over the outputs that are not `kept`, when none of them waits behind an equal one
that is kept. -/
theorem run_outputs_filter (env : EnvModel σ) (c : SysState sys) (kept : σ.Out → Bool)
    (pre outs : List σ.Out) (hpre : ∀ out ∈ pre, kept out = true) :
    ({ c with outbox := pre ++ outs } : SysState sys).run env
        ((outs.filter (!kept ·)).map .output)
      = some { c with outbox := pre ++ outs.filter kept } := by
  induction outs generalizing pre with
  | nil => simp [run]
  | cons out outs ih =>
    cases hout : kept out with
    | true =>
      have h := ih (pre ++ [out]) (by
        intro o ho
        rcases List.mem_append.mp ho with ho | ho
        · exact hpre o ho
        · simp only [List.mem_singleton] at ho
          exact ho ▸ hout)
      simpa [hout, List.append_assoc] using h
    | false =>
      have hnot : out ∉ pre := fun h => by simp [hpre out h] at hout
      simp only [List.filter_cons, hout, Bool.not_false, ↓reduceIte, List.map_cons, run]
      rw [step_output.mpr ⟨by simp, rfl⟩]
      simp only [Option.bind_some, List.erase_append_right _ hnot, List.erase_cons_head]
      simpa [hout] using ih pre hpre

end SysState

end Lanes
