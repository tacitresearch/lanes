/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Proof.Monotone
public import Lanes.Outside.Basic

/-!
# What a system hands to the outside

An output handed to the outside world is one an actor emitted. So what holds of every output
each step and each start may emit holds of every output in every run, under every environment
model. A model of something outside (`Outside`) that is shown to behave whenever the outputs it
sees are of some form is then shown to behave beside the system (`Outside.after_invariant`).
What holds of the system and of the outside together, each input as the outside allows it, is
proved by the rule of `Inductive.of_monotone` with the outside's memory beside the state
(`Outside.Beside`).
-/

@[expose] public section

namespace Lanes.System

variable {σ : Signature} {sys : System σ}

/-- Every output an actor's step or start emits is one `good` admits, whatever it is told. -/
def Emits (sys : System σ) (good : σ.Out → Prop) : Prop :=
  (∀ i ctx s msg out, Effect.emit out ∈ ((sys.actor i).stepAt ctx s msg).2 → good out) ∧
    ∀ i t s out, Effect.emit out ∈ ((sys.actor i).recoverAt t s).2 → good out

theorem Emits.outbox {good : σ.Out → Prop} (h : sys.Emits good) :
    sys.Monotone fun c => ∀ out ∈ c.outbox, good out where
  blank := by simp [SysState.blank]
  below _ _ hc hbelow out hout := hc out (hbelow.outbox out hout)
  input c _ hc := hc
  step c i msg hc _ ctx out hout := by
    simp only [SysState.grow, List.mem_append] at hout
    exact hout.elim (hc out) fun hout => h.1 i ctx _ msg out (Effect.mem_emits.mp hout)
  recover c i hc t out hout := by
    simp only [SysState.grow, List.mem_append] at hout
    exact hout.elim (hc out) fun hout => h.2 i t _ out (Effect.mem_emits.mp hout)

/-- Every output of a run is one `good` admits, if every output an actor emits is. -/
theorem Emits.outputs {good : σ.Out → Prop} (h : sys.Emits good) {env : EnvModel σ}
    {events : List (Event σ)} {c : SysState sys}
    (hrun : (SysState.init sys env).run env events = some c) :
    ∀ out, Event.output out ∈ events → good out := by
  have hinv := (h.outbox.invariant env)
  refine Reachable.run_induction (P := fun events _ => ∀ out, Event.output out ∈ events → good out)
    .init hrun (by simp) ?_
  intro evs c₁ ev c₂ hc₁ hP hstep out hout
  rcases List.mem_append.mp hout with hout | hout
  · exact hP out hout
  · simp only [List.mem_singleton] at hout
    subst hout
    exact hinv c₁ hc₁ out (SysState.step_output.mp hstep).1

end Lanes.System

namespace Lanes

variable {σ : Signature} {sys : System σ}

/-- The proof rule of `Inductive.of_monotone` for a property of the system's state and the
memory of an outside beside it: it holds of the blank state and the outside's start, removing
messages, timers and outputs cannot break it, and it is kept by each input the outside allows,
by each output it sees, by any actor handling a message in flight to it or armed as its timer
in a reachable state, by any actor recovering, and by a restart, which puts the system back at
its start while the outside remembers what it saw. It then holds after every run the outside
allows (`Outside.Beside.holds`). -/
structure Outside.Beside {D : Type} (outside : Outside σ D) (sys : System σ) (env : EnvModel σ)
    (P : SysState sys → D → Prop) : Prop where
  blank : P (SysState.blank sys) outside.init
  below : ∀ c c' d, P c d → c'.Below c → P c' d
  input : ∀ c d x d', P c d → outside.allow d x = some d' →
    P { c with net := c.net ++ [⟨none, (sys.accept x).1, (sys.accept x).2⟩] } d'
  output : ∀ c d out, P c d → out ∈ c.outbox →
    P { c with outbox := c.outbox.erase out } (outside.observe d out)
  step : ∀ c d i msg, sys.Reachable env c → P c d →
    ((∃ src, ⟨src, i, msg⟩ ∈ c.net) ∨ msg ∈ c.timers i) →
      ∀ ctx, P (c.grow i ((sys.actor i).stepAt ctx (c.state i) msg)) d
  recover : ∀ c d i, P c d → ∀ t, P (c.grow i ((sys.actor i).recoverAt t (c.state i))) d
  restart : env.mayRestart = true → ∀ c d, sys.Reachable env c → P c d →
    P (SysState.init sys env) d

namespace Outside.Beside

open SysState

variable {D : Type} {outside : Outside σ D} {env : EnvModel σ} {P : SysState sys → D → Prop}

theorem init (h : outside.Beside sys env P) : P (SysState.init sys env) outside.init :=
  init_induction h.blank fun c i hc =>
    h.below _ _ _ (h.recover c _ i hc _) (Below.startActor c env i)

/-- Each event that the system and the outside both allow keeps the property. -/
theorem keeps (h : outside.Beside sys env P) {c c' : SysState sys} {d d' : D} {ev : Event σ}
    (hc : sys.Reachable env c) (hP : P c d) (hstep : c.step env ev = some c')
    (hsee : outside.see d ev = some d') : P c' d' := by
  cases ev with
  | input x =>
    obtain rfl := step_input.mp hstep
    exact h.input c d x d' hP hsee
  | deliver e =>
    obtain ⟨_, hdeliverable, rfl⟩ := step_deliver.mp hstep
    obtain rfl := Option.some.inj hsee
    have hbelow : SysState.Below { c with net := c.net.erase e } c :=
      ⟨rfl, fun _ h => List.mem_of_mem_erase h, fun _ _ h => h, fun _ h => h⟩
    exact h.below _ _ _
      (h.step c d e.dst e.msg hc hP (.inl ⟨e.src, mem_of_deliverable hdeliverable⟩) _)
      (Below.handle hbelow ..)
  | duplicate e =>
    obtain ⟨_, _, hdeliverable, rfl⟩ := step_duplicate.mp hstep
    obtain rfl := Option.some.inj hsee
    exact h.below _ _ _
      (h.step c d e.dst e.msg hc hP (.inl ⟨e.src, mem_of_deliverable hdeliverable⟩) _)
      (Below.handle (Below.refl c) ..)
  | drop e =>
    obtain ⟨_, _, rfl⟩ := step_drop.mp hstep
    obtain rfl := Option.some.inj hsee
    exact h.below _ _ _ hP ⟨rfl, fun _ h => List.mem_of_mem_erase h, fun _ _ h => h, fun _ h => h⟩
  | timeout i msg =>
    obtain ⟨_, hmem, rfl⟩ := step_timeout.mp hstep
    obtain rfl := Option.some.inj hsee
    have hbelow : SysState.Below
        { c with timers := update c.timers i ((c.timers i).erase msg) } c := by
      refine ⟨rfl, fun _ h => h, ?_, fun _ h => h⟩
      intro j m hm
      by_cases hj : j = i
      · subst hj
        simp only [update_self] at hm
        exact List.mem_of_mem_erase hm
      · simpa [hj] using hm
    exact h.below _ _ _ (h.step c d i msg hc hP (.inr hmem) _) (Below.handle hbelow ..)
  | output out =>
    obtain ⟨hmem, rfl⟩ := step_output.mp hstep
    obtain rfl := Option.some.inj hsee
    exact h.output c d out hP hmem
  | crash i =>
    obtain ⟨_, _, rfl⟩ := step_crash.mp hstep
    obtain rfl := Option.some.inj hsee
    refine h.below _ _ _ hP ⟨rfl, fun _ h => (List.mem_filter.mp h).1, ?_, fun _ h => h⟩
    intro j m hm
    by_cases hj : j = i
    · subst hj; simp [down] at hm
    · simpa [down, hj] using hm
  | start i =>
    obtain ⟨_, _, rfl⟩ := step_start.mp hstep
    obtain rfl := Option.some.inj hsee
    exact h.below _ _ _ (h.recover c d i hP _) (Below.startActor c env i)
  | restart =>
    obtain ⟨hmay, rfl⟩ := step_restart.mp hstep
    obtain rfl := Option.some.inj hsee
    exact h.restart hmay c d hc hP
  | tick m =>
    obtain rfl := step_tick.mp hstep
    obtain rfl := Option.some.inj hsee
    exact h.below _ _ _ hP ⟨rfl, fun _ h => h, fun _ _ h => h, fun _ h => h⟩

/-- The property holds after every run that the outside allows. -/
theorem holds (h : outside.Beside sys env P) {events : List (Event σ)} {c : SysState sys} {d : D}
    (hrun : (SysState.init sys env).run env events = some c)
    (hd : outside.after events = some d) : P c d :=
  outside.run_induction (P := fun _ c d => P c d) h.init
    (fun _ _ _ _ _ _ hc hP hstep hsee => h.keeps hc hP hstep hsee) hrun hd

end Outside.Beside

end Lanes
