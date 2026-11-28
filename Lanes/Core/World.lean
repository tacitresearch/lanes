/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Core.System

/-!
# What a system means: one pure step function

This file defines the meaning of a Lanes system once, as a pure function
`SysState.step : EnvModel σ → SysState sys → Event σ → Option (SysState sys)`.

Everything else is built on that one function. The deterministic scheduler picks events with a
seeded generator and applies it. The model checker applies it to every enabled event. Trace
checking replays a runtime trace through it. `Lanes.Semantics` wraps it as a CSLib `LTS` for
proofs. There is no second model to keep in sync.

Concurrency is absent here by construction: an `Event` handles one message for one actor
(rule 3.6). All nondeterminism, such as which message is next, whether a link loses it, and when
a node crashes, is the choice of the event.
-/

@[expose] public section

namespace Lanes

def update {ι : Type} [DecidableEq ι] {β : ι → Type} (f : (i : ι) → β i) (i : ι) (v : β i) :
    (j : ι) → β j :=
  fun j => if h : j = i then h ▸ v else f j

@[simp] theorem update_self {ι : Type} [DecidableEq ι] {β : ι → Type} (f : (i : ι) → β i) (i : ι)
    (v : β i) : update f i v i = v := by
  simp [update]

@[simp] theorem update_of_ne {ι : Type} [DecidableEq ι] {β : ι → Type} (f : (i : ι) → β i)
    {i j : ι} (v : β i) (h : j ≠ i) : update f i v j = f j := by
  simp [update, h]

@[simp] theorem update_eq_self {ι : Type} [DecidableEq ι] {β : ι → Type} (f : (i : ι) → β i)
    (i : ι) : update f i (f i) = f := by
  funext j
  by_cases h : j = i
  · subst h; simp
  · simp [h]

theorem update_update {ι : Type} [DecidableEq ι] {β : ι → Type} (f : (i : ι) → β i) (i : ι)
    (v v' : β i) : update (update f i v) i v' = update f i v' := by
  funext j
  by_cases h : j = i
  · subst h; simp
  · simp [h]

theorem update_comm {ι : Type} [DecidableEq ι] {β : ι → Type} (f : (i : ι) → β i) {i k : ι}
    (h : i ≠ k) (a : β i) (b : β k) : update (update f i a) k b = update (update f k b) i a := by
  funext j
  by_cases hi : j = i
  · subst hi
    simp [h]
  · by_cases hk : j = k
    · subst hk
      simp [hi]
    · simp [hi, hk]

theorem apply_update {ι : Type} [DecidableEq ι] {β γ : ι → Type} (f : (j : ι) → β j → γ j)
    (g : (j : ι) → β j) (i : ι) (v : β i) :
    (fun j => f j (update g i v j)) = update (fun j => f j (g j)) i (f i v) := by
  funext j
  by_cases h : j = i
  · subst h; simp
  · simp [h]

variable {σ : Signature}

/-- A whole system at one moment: each actor's state and whether it is up, the messages in
flight, each actor's pending timers, and the outputs not yet handed to the outside. The
semantics is `SysState.step`, one function on it. -/
structure SysState (sys : System σ) where
  state : (i : σ.Id) → sys.State i
  up : σ.Id → Bool
  /-- Messages in flight, oldest first. -/
  net : List (Envelope σ)
  timers : (i : σ.Id) → List (σ.Msg i)
  outbox : List σ.Out

theorem SysState.ext' {sys : System σ} {a b : SysState sys} (hstate : a.state = b.state)
    (hup : a.up = b.up) (hnet : a.net = b.net) (htimers : a.timers = b.timers)
    (houtbox : a.outbox = b.outbox) : a = b := by
  cases a; cases b; simp_all

/-- One thing that can happen to a system. Inputs come from outside; drops, duplicates,
crashes and restarts are what the environment model allows; the rest follow from what the
actors did.
`SysState.step` says when each is enabled. -/
inductive Event (σ : Signature) : Type where
  | input (x : σ.In)
  | deliver (e : Envelope σ)
  /-- The receiver handles a message in flight that stays in flight (a duplicating link). -/
  | duplicate (e : Envelope σ)
  | drop (e : Envelope σ)
  | timeout (i : σ.Id) (msg : σ.Msg i)
  /-- An emitted output is handed to the outside world. -/
  | output (out : σ.Out)
  | crash (i : σ.Id)
  | start (i : σ.Id)
  /-- The process restarts: every actor is back at its initial state, as at `SysState.init`,
  and messages in flight, timers and outputs not yet handed over are lost (D110). -/
  | restart

/-- What the outside world sees: inputs, outputs, and a spec's deadlines passing. -/
inductive Visible (In Out : Type) (T : Type := Empty) : Type where
  | input (x : In)
  | output (out : Out)
  | fire (t : T)

/-- Which messages an actor handles, by actor and message, are deadlines of a spec, and which:
as timers firing (`deadlines`), or as messages delivered (`delivered`). The others are
internal. -/
abbrev Deadlines (σ : Signature) (T : Type) : Type := (i : σ.Id) → σ.Msg i → Option T

/-- What the outside world sees of an event: inputs, outputs, the timers `deadlines` names and
the deliveries `delivered` names, each passing its deadline. A message handed over a second
time passes it again. -/
@[simp] def Event.timed {T : Type} (deadlines : Deadlines σ T)
    (delivered : Deadlines σ T := fun _ _ => none) : Event σ → Option (Visible σ.In σ.Out T)
  | .input x => some (.input x)
  | .output out => some (.output out)
  | .timeout i msg => (deadlines i msg).map .fire
  | .deliver e | .duplicate e => (delivered e.dst e.msg).map .fire
  | _ => none

def Event.visible : Event σ → Option (Visible σ.In σ.Out) :=
  Event.timed fun _ _ => none

namespace SysState

variable {sys : System σ}

def blank (sys : System σ) : SysState sys where
  state i := (sys.actor i).init
  up _ := false
  net := []
  timers _ := []
  outbox := []

def hasMail (c : SysState sys) (i : σ.Id) : Bool :=
  c.net.any fun e => decide (e.dst = i)

/-- `stop` is handled once the whole step is done, by `settle`. -/
def perform (c : SysState sys) (i : σ.Id) : Effect σ i → SysState sys
  | .send to msg => { c with net := c.net ++ [⟨some i, to, msg⟩] }
  | .emit out => { c with outbox := c.outbox ++ [out] }
  | .after _ msg =>
    { c with timers := update c.timers i (if msg ∈ c.timers i then c.timers i
        else c.timers i ++ [msg]) }
  | .cancel msg => { c with timers := update c.timers i ((c.timers i).erase msg) }
  | .stop => c

def performAll (c : SysState sys) (i : σ.Id) (effs : List (Effect σ i)) : SysState sys :=
  effs.foldl (fun c eff => c.perform i eff) c

/--
Take actor `i` down. Its timers are lost. So is its mailbox: messages already handed over on a
link that never loses messages are gone with the actor, while messages on a lossy link may still
arrive after a restart.
-/
def down (env : EnvModel σ) (c : SysState sys) (i : σ.Id) : SysState sys :=
  { c with
    up := update c.up i false
    timers := update c.timers i []
    net := c.net.filter fun e => decide (e.dst ≠ i) || (env.link e.src e.dst).lossy }

def settle (env : EnvModel σ) (c : SysState sys) (i : σ.Id)
    (r : sys.State i × List (Effect σ i)) : SysState sys :=
  let c := ({ c with state := update c.state i r.1 }).performAll i r.2
  if r.2.any Effect.isStop then c.down env i else c

def handle (env : EnvModel σ) (c : SysState sys) (i : σ.Id) (msg : σ.Msg i) : SysState sys :=
  c.settle env i ((sys.actor i).step (c.state i) msg)

def startActor (env : EnvModel σ) (c : SysState sys) (i : σ.Id) : SysState sys :=
  ({ c with up := update c.up i true }).settle env i ((sys.actor i).recover (c.state i))

/-- The state at the start: no actor up, then each actor of `sys.boot` started in order. -/
def init (sys : System σ) (env : EnvModel σ) : SysState sys :=
  sys.boot.foldl (fun c i => c.startActor env i) (blank sys)

/-- Whether `e` may be delivered now: it is in flight, and if its link is ordered it is the
oldest message on that link. -/
def deliverable (env : EnvModel σ) (c : SysState sys) (e : Envelope σ) : Bool :=
  if (env.link e.src e.dst).ordered then c.net.find? e.sameLink == some e else c.net.contains e

/-- `none` when the event is not enabled in this state under this environment model. -/
def step (env : EnvModel σ) (c : SysState sys) : Event σ → Option (SysState sys)
  | .input x =>
    let ⟨i, msg⟩ := sys.accept x
    some { c with net := c.net ++ [⟨none, i, msg⟩] }
  | .deliver e =>
    if c.up e.dst && c.deliverable env e then
      some (({ c with net := c.net.erase e }).handle env e.dst e.msg)
    else none
  | .duplicate e =>
    if c.up e.dst && (env.link e.src e.dst).duplicating && c.deliverable env e then
      some (c.handle env e.dst e.msg)
    else none
  | .drop e =>
    if (env.link e.src e.dst).lossy && c.net.contains e then
      some { c with net := c.net.erase e }
    else none
  | .timeout i msg =>
    if c.up i && (c.timers i).contains msg then
      some (({ c with timers := update c.timers i ((c.timers i).erase msg) }).handle env i msg)
    else none
  | .output out =>
    if c.outbox.contains out then some { c with outbox := c.outbox.erase out } else none
  | .crash i =>
    if c.up i && env.mayCrash i then some (c.down env i) else none
  | .start i =>
    if !c.up i && (c.hasMail i || env.restarts i) then some (c.startActor env i) else none
  | .restart => if env.mayRestart then some (init sys env) else none

/-- The state after the events, in order, or `none` if one of them is not enabled. A
counterexample of the checker, and a run of the scheduler, replay through it. -/
def run (env : EnvModel σ) (c : SysState sys) : List (Event σ) → Option (SysState sys)
  | [] => some c
  | ev :: evs => (c.step env ev).bind fun c' => c'.run env evs

theorem run_append (env : EnvModel σ) (c : SysState sys) (a b : List (Event σ)) :
    c.run env (a ++ b) = (c.run env a).bind (·.run env b) := by
  induction a generalizing c with
  | nil => rfl
  | cons ev a ih =>
    simp only [List.cons_append, run]
    cases c.step env ev with
    | none => rfl
    | some c' => simpa using ih c'

end SysState

namespace System

variable (sys : System σ)

/-- The states the semantics reaches from `SysState.init` by enabled events under `env`. -/
inductive Reachable (env : EnvModel σ) : SysState sys → Prop
  | init : Reachable env (SysState.init sys env)
  | step {c c' : SysState sys} (ev : Event σ) :
    Reachable env c → c.step env ev = some c' → Reachable env c'

/-- `P` holds in every state the system reaches under `env`. -/
def Invariant (env : EnvModel σ) (P : SysState sys → Prop) : Prop :=
  ∀ c, sys.Reachable env c → P c

/-- `P` holds at the start and every enabled event keeps it, which gives `Invariant`
(`System.Inductive.invariant`). -/
structure Inductive (env : EnvModel σ) (P : SysState sys → Prop) : Prop where
  init : P (SysState.init sys env)
  step : ∀ c ev c', P c → c.step env ev = some c' → P c'

variable {sys}

theorem Inductive.invariant {env : EnvModel σ} {P : SysState sys → Prop}
    (h : sys.Inductive env P) : sys.Invariant env P := by
  intro c hc
  induction hc with
  | init => exact h.init
  | step ev _ hstep ih => exact h.step _ ev _ ih hstep

theorem Reachable.run {env : EnvModel σ} {c c' : SysState sys} {evs : List (Event σ)}
    (h : sys.Reachable env c) (hrun : c.run env evs = some c') : sys.Reachable env c' := by
  induction evs generalizing c with
  | nil => simp only [SysState.run, Option.some.injEq] at hrun; exact hrun ▸ h
  | cons ev evs ih =>
    simp only [SysState.run] at hrun
    cases hstep : c.step env ev with
    | none => simp [hstep] at hrun
    | some c₁ => exact ih (h.step ev hstep) (by simpa [hstep] using hrun)

/-- Induction along a run, for properties that relate the events so far to the state reached. -/
theorem Reachable.run_induction {env : EnvModel σ} {P : List (Event σ) → SysState sys → Prop}
    {c c' : SysState sys} {events : List (Event σ)} (hc : sys.Reachable env c)
    (hrun : c.run env events = some c') (start : P [] c)
    (step : ∀ evs c₁ ev c₂, sys.Reachable env c₁ → P evs c₁ → c₁.step env ev = some c₂ →
      P (evs ++ [ev]) c₂) : P events c' := by
  suffices h : ∀ (rest evs : List (Event σ)) (c₁ : SysState sys), sys.Reachable env c₁ →
      P evs c₁ → c₁.run env rest = some c' → P (evs ++ rest) c' from h events [] c hc start hrun
  intro rest
  induction rest with
  | nil =>
    intro evs c₁ _ hP hrun
    simp only [SysState.run, Option.some.injEq] at hrun
    simpa [← hrun] using hP
  | cons ev rest ih =>
    intro evs c₁ hc₁ hP hrun
    simp only [SysState.run] at hrun
    cases hstep : c₁.step env ev with
    | none => simp [hstep] at hrun
    | some c₂ =>
      have h := ih (evs ++ [ev]) c₂ (hc₁.step ev hstep) (step evs c₁ ev c₂ hc₁ hP hstep)
        (by simpa [hstep] using hrun)
      simpa using h

end System

end Lanes
