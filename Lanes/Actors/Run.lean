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
through a step rewrites with it and then reasons about lists. `SysState.started` is a start in
that form, without the case on whether the actor stops, for when stopping loses no message
(`startActor_eq_started`).

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

theorem mem_emits {effs : List (Effect σ i)} {out : σ.Out} : out ∈ emits effs ↔ .emit out ∈ effs := by
  induction effs with
  | nil => simp [emits]
  | cons eff effs ih =>
    simp only [emits, List.filterMap_cons, List.mem_cons] at ih ⊢
    cases eff <;> simp [ih, eq_comm]

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

theorem emits_nil : emits ([] : List (Effect σ i)) = [] := rfl

theorem emits_append (a b : List (Effect σ i)) : emits (a ++ b) = emits a ++ emits b :=
  List.filterMap_append

theorem emits_cons (eff : Effect σ i) (effs : List (Effect σ i)) :
    emits (eff :: effs) = (match eff with | .emit out => [out] | _ => []) ++ emits effs := by
  cases eff <;> rfl

/-- Unlike `emits_map_emit` this has no type that depends on the signature among its arguments,
so `simp` finds it for the effects of a concrete system. -/
theorem emits_map {α : Type} (f : α → Effect σ i) (l : List α) :
    emits (l.map f) = l.filterMap fun a => match f a with | .emit out => some out | _ => none := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, emits_cons, ih, List.filterMap_cons]
    cases f a <;> rfl

theorem sends_append (a b : List (Effect σ i)) : sends i (a ++ b) = sends i a ++ sends i b :=
  List.filterMap_append

/-! What a step sends, arms and emits, computed by `simp` for a concrete system. A lemma whose
left side has a type such as `σ.Out` or `σ.Msg i` as an implicit argument (`emits_map_emit`:
`List.map` at `σ.Out`) is keyed by the discrimination tree on `Signature.Out _`, which a
concrete signature, reduced to its fields, never matches; these have none. -/

attribute [simp] emits_nil emits_append sends_append

@[simp] theorem sends_nil : sends i ([] : List (Effect σ i)) = [] := rfl

@[simp] theorem sends_cons_send (to : σ.Id) (msg : σ.Msg to) (effs : List (Effect σ i)) :
    sends i (.send to msg :: effs) = ⟨some i, to, msg⟩ :: sends i effs := rfl

@[simp] theorem sends_cons_emit (out : σ.Out) (effs : List (Effect σ i)) :
    sends i (.emit out :: effs) = sends i effs := rfl

@[simp] theorem sends_cons_after (delay_ms : Nat) (msg : σ.Msg i) (effs : List (Effect σ i)) :
    sends i (.after delay_ms msg :: effs) = sends i effs := rfl

@[simp] theorem sends_cons_cancel (msg : σ.Msg i) (effs : List (Effect σ i)) :
    sends i (.cancel msg :: effs) = sends i effs := rfl

@[simp] theorem sends_cons_stop (effs : List (Effect σ i)) :
    sends i (.stop :: effs) = sends i effs := rfl

@[simp] theorem emits_cons_send (to : σ.Id) (msg : σ.Msg to) (effs : List (Effect σ i)) :
    emits (.send to msg :: effs) = emits effs := rfl

@[simp] theorem emits_cons_emit (out : σ.Out) (effs : List (Effect σ i)) :
    emits (.emit out :: effs) = out :: emits effs := rfl

@[simp] theorem emits_cons_after (delay_ms : Nat) (msg : σ.Msg i) (effs : List (Effect σ i)) :
    emits (.after delay_ms msg :: effs) = emits effs := rfl

@[simp] theorem emits_cons_cancel (msg : σ.Msg i) (effs : List (Effect σ i)) :
    emits (.cancel msg :: effs) = emits effs := rfl

@[simp] theorem emits_cons_stop (effs : List (Effect σ i)) :
    emits (.stop :: effs) = emits effs := rfl

@[simp] theorem armed_nil : armed ([] : List (Effect σ i)) = [] := rfl

@[simp] theorem armed_append (a b : List (Effect σ i)) : armed (a ++ b) = armed a ++ armed b :=
  List.filterMap_append

@[simp] theorem armed_cons_send (to : σ.Id) (msg : σ.Msg to) (effs : List (Effect σ i)) :
    armed (.send to msg :: effs) = armed effs := rfl

@[simp] theorem armed_cons_emit (out : σ.Out) (effs : List (Effect σ i)) :
    armed (.emit out :: effs) = armed effs := rfl

@[simp] theorem armed_cons_after (delay_ms : Nat) (msg : σ.Msg i) (effs : List (Effect σ i)) :
    armed (.after delay_ms msg :: effs) = msg :: armed effs := rfl

@[simp] theorem armed_cons_cancel (msg : σ.Msg i) (effs : List (Effect σ i)) :
    armed (.cancel msg :: effs) = armed effs := rfl

@[simp] theorem armed_cons_stop (effs : List (Effect σ i)) :
    armed (.stop :: effs) = armed effs := rfl

/-- `emits_map` for what a step sends. -/
@[simp] theorem sends_map {α : Type} (f : α → Effect σ i) (l : List α) :
    sends i (l.map f) =
      l.filterMap fun a => match f a with | .send to msg => some ⟨some i, to, msg⟩ | _ => none := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.filterMap_cons, ← ih]
    cases f a <;> rfl

/-- `emits_map` for the timers a step arms. -/
@[simp] theorem armed_map {α : Type} (f : α → Effect σ i) (l : List α) :
    armed (l.map f) = l.filterMap fun a => match f a with | .after _ msg => some msg | _ => none := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.filterMap_cons, ← ih]
    cases f a <;> rfl

attribute [simp] emits_map

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

theorem retime_cons (eff : Effect σ i) (effs : List (Effect σ i)) (timers : List (σ.Msg i)) :
    retime (eff :: effs) timers = retime effs (retime [eff] timers) :=
  rfl

/-- A timer stays armed through effects that do not cancel it. -/
theorem mem_retime_of_mem {effs : List (Effect σ i)} {timers : List (σ.Msg i)} {msg : σ.Msg i}
    (h : msg ∈ timers) (hkeep : .cancel msg ∉ effs) : msg ∈ retime effs timers := by
  induction effs generalizing timers with
  | nil => exact h
  | cons eff effs ih =>
    simp only [List.mem_cons, not_or] at hkeep
    rw [retime_cons]
    refine ih ?_ hkeep.2
    cases eff with
    | after _ m => simp only [retime, List.foldl_cons, List.foldl_nil]; split <;> simp [h]
    | cancel m =>
      have hne : msg ≠ m := fun he => hkeep.1 (he ▸ rfl)
      exact (List.mem_erase_of_ne hne).mpr h
    | send _ _ | emit _ | stop => exact h

/-- Effects that arm a timer and do not cancel it leave it armed. -/
theorem mem_retime_of_after {effs : List (Effect σ i)} {timers : List (σ.Msg i)} {msg : σ.Msg i}
    {delay_ms : Nat} (h : .after delay_ms msg ∈ effs) (hkeep : .cancel msg ∉ effs) :
    msg ∈ retime effs timers := by
  induction effs generalizing timers with
  | nil => simp at h
  | cons eff effs ih =>
    simp only [List.mem_cons, not_or] at hkeep h
    rw [retime_cons]
    rcases h with rfl | h
    · refine mem_retime_of_mem ?_ hkeep.2
      simp only [retime, List.foldl_cons, List.foldl_nil]
      split <;> simp [*]
    · exact ih h hkeep.2

end Effect

/-- An input, a loss or a hand-over: an event that changes no actor's state, starts or stops no
actor and arms no timer. -/
def Event.quiet : Event σ → Bool
  | .input _ | .drop _ | .output _ => true
  | _ => false

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

/-- Stopping loses no output. -/
theorem settle_outbox_eq (env : EnvModel σ) (c : SysState sys) (i : σ.Id)
    (r : sys.State i × List (Effect σ i)) :
    (c.settle env i r).outbox = c.outbox ++ Effect.emits r.2 := by
  rw [settle_eq]
  split <;> rfl

theorem settle_net_sublist (env : EnvModel σ) (c : SysState sys) (i : σ.Id)
    (r : sys.State i × List (Effect σ i)) :
    (c.settle env i r).net.Sublist (c.net ++ Effect.sends i r.2) := by
  rw [settle_eq]
  split
  · exact List.filter_sublist
  · exact List.Sublist.refl _

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

/-- `c` after actor `i` moves to `r.1` with effects `r.2` as it starts, when stopping loses no
message. -/
def startedWith (c : SysState sys) (i : σ.Id) (r : sys.State i × List (Effect σ i)) :
    SysState sys where
  state := update c.state i r.1
  up := update c.up i !(r.2.any Effect.isStop)
  net := c.net ++ Effect.sends i r.2
  timers := update c.timers i
    (if r.2.any Effect.isStop then [] else Effect.retime r.2 (c.timers i))
  outbox := c.outbox ++ Effect.emits r.2

def started (c : SysState sys) (i : σ.Id) : SysState sys :=
  c.startedWith i ((sys.actor i).recover (c.state i))

theorem startActor_eq_started (c : SysState sys) (i : σ.Id)
    (h : ((sys.actor i).recover (c.state i)).2.any Effect.isStop = true →
      ∀ src, (env.link src i).lossy = true) : c.startActor env i = c.started i := by
  simp only [startActor, settle_eq, started, startedWith]
  split
  · next hstop =>
    have hkept : ∀ l : List (Envelope σ),
        l.filter (fun e => decide (e.dst ≠ i) || (env.link e.src e.dst).lossy) = l := fun l =>
      List.filter_eq_self.mpr fun e _ => by
        by_cases he : e.dst = i
        · simp [he, h hstop e.src]
        · simp [he]
    simp only [down, hkept, update_update, hstop, Bool.not_true]
  · next hstop =>
    simp only [Bool.not_eq_true] at hstop
    simp only [hstop, Bool.not_false]

/-- Arming timers keeps those armed and arms each. -/
theorem mem_timers_performAll_after {α : Type} (c : SysState sys) (i : σ.Id) (delay_ms : Nat)
    (f : α → σ.Msg i) (xs : List α) {msg : σ.Msg i}
    (h : msg ∈ c.timers i ∨ ∃ x ∈ xs, msg = f x) :
    msg ∈ (c.performAll i (xs.map fun x => .after delay_ms (f x))).timers i := by
  induction xs generalizing c with
  | nil => simpa using h
  | cons x xs ih =>
    apply ih
    simp only [perform, update_self]
    rcases h with h | ⟨x', hx', rfl⟩
    · exact .inl (by split <;> simp [h])
    · rcases List.mem_cons.mp hx' with rfl | hx'
      · exact .inl (by split <;> simp [*])
      · exact .inr ⟨x', hx', rfl⟩

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

theorem run_quiet {evs : List (Event σ)} (hquiet : ∀ ev ∈ evs, ev.quiet = true)
    {c c' : SysState sys} (hrun : c.run env evs = some c') :
    c'.state = c.state ∧ c'.up = c.up ∧ c'.timers = c.timers := by
  induction evs generalizing c with
  | nil =>
    simp only [run, Option.some.injEq] at hrun
    exact hrun ▸ ⟨rfl, rfl, rfl⟩
  | cons ev evs ih =>
    simp only [run] at hrun
    cases hstep : c.step env ev with
    | none => simp [hstep] at hrun
    | some c₁ =>
      obtain ⟨h₁, h₂, h₃⟩ := ih (fun ev' h => hquiet ev' (List.mem_cons_of_mem _ h))
        (by simpa [hstep] using hrun)
      have hq := hquiet ev List.mem_cons_self
      have : c₁.state = c.state ∧ c₁.up = c.up ∧ c₁.timers = c.timers := by
        cases ev with
        | input x => obtain rfl := step_input.mp hstep; exact ⟨rfl, rfl, rfl⟩
        | drop e => obtain ⟨_, _, rfl⟩ := step_drop.mp hstep; exact ⟨rfl, rfl, rfl⟩
        | output out => obtain ⟨_, rfl⟩ := step_output.mp hstep; exact ⟨rfl, rfl, rfl⟩
        | _ => cases hq
      exact ⟨h₁.trans this.1, h₂.trans this.2.1, h₃.trans this.2.2⟩

theorem run_take {c c' : SysState sys} {evs : List (Event σ)} (hrun : c.run env evs = some c')
    (j : Nat) : ∃ d, c.run env (evs.take j) = some d ∧ d.run env (evs.drop j) = some c' := by
  rw [← List.take_append_drop j evs, run_append] at hrun
  cases h : c.run env (evs.take j) with
  | none => simp [h] at hrun
  | some d => exact ⟨d, rfl, by simpa [h] using hrun⟩

theorem mem_settle_net {c : SysState sys} {i : σ.Id} {r : sys.State i × List (Effect σ i)}
    {e : Envelope σ} (he : e ∈ (c.settle env i r).net) : e ∈ c.net ∨ e.src = some i := by
  rcases List.mem_append.mp ((settle_net_sublist env c i r).subset he) with h | h
  · exact .inl h
  · exact .inr (Effect.mem_sends.mp h).1

end SysState

/-- A message from outside in flight is an input the system accepted. -/
theorem System.Reachable.accepted {env : EnvModel σ} {c : SysState sys} (h : sys.Reachable env c)
    {e : Envelope σ} (he : e ∈ c.net) (hsrc : e.src = none) :
    ∃ x, (⟨none, (sys.accept x).1, (sys.accept x).2⟩ : Envelope σ) = e := by
  let P (c : SysState sys) : Prop := ∀ e ∈ c.net, e.src = none →
    ∃ x, (⟨none, (sys.accept x).1, (sys.accept x).2⟩ : Envelope σ) = e
  have hsettle (c : SysState sys) (i : σ.Id) (r : sys.State i × List (Effect σ i)) (hc : P c) :
      P (c.settle env i r) := fun e he hsrc =>
    (SysState.mem_settle_net he).elim (fun h => hc e h hsrc) fun h => by simp [h] at hsrc
  suffices hall : P c from hall e he hsrc
  clear he hsrc
  induction h with
  | init =>
    exact SysState.init_induction (P := P) (by simp [P, SysState.blank])
      fun c i hc => hsettle { c with up := update c.up i true } i _ hc
  | @step c c' ev _ hstep ih =>
    cases ev with
    | input x =>
      obtain rfl := SysState.step_input.mp hstep
      intro e he hsrc
      rcases List.mem_append.mp he with he | he
      · exact ih e he hsrc
      · exact ⟨x, (List.mem_singleton.mp he).symm⟩
    | deliver e' =>
      obtain ⟨_, _, rfl⟩ := SysState.step_deliver.mp hstep
      exact hsettle _ _ _ fun e he => ih e (List.mem_of_mem_erase he)
    | duplicate e' =>
      obtain ⟨_, _, _, rfl⟩ := SysState.step_duplicate.mp hstep
      exact hsettle _ _ _ ih
    | drop e' =>
      obtain ⟨_, _, rfl⟩ := SysState.step_drop.mp hstep
      exact fun e he => ih e (List.mem_of_mem_erase he)
    | timeout i msg =>
      obtain ⟨_, _, rfl⟩ := SysState.step_timeout.mp hstep
      exact hsettle _ _ _ ih
    | output out =>
      obtain ⟨_, rfl⟩ := SysState.step_output.mp hstep
      exact ih
    | crash i =>
      obtain ⟨_, _, rfl⟩ := SysState.step_crash.mp hstep
      exact fun e he => ih e (List.mem_filter.mp he).1
    | start i =>
      obtain ⟨_, _, rfl⟩ := SysState.step_start.mp hstep
      exact hsettle _ _ _ ih

end Lanes
