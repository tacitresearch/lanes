/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Actors.System

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

## Main definitions

- `SysState sys`: actor states, which actors are up, messages in flight, pending timers and
  outputs not yet handed to the outside.
- `Event σ`: the steps a system can take, and `Event.visible`, the part of a step the outside
  world sees.
- `SysState.step`: apply one event, or `none` if it is not enabled.
- `SysState.init`: the state of a freshly booted system.
- `System.Reachable`: the states a system can reach under an environment model.
-/

@[expose] public section

namespace Lanes

/-- Replace the value of a dependent function at one point. -/
def update {ι : Type} [DecidableEq ι] {β : ι → Type} (f : (i : ι) → β i) (i : ι) (v : β i) :
    (j : ι) → β j :=
  fun j => if h : j = i then h ▸ v else f j

@[simp] theorem update_self {ι : Type} [DecidableEq ι] {β : ι → Type} (f : (i : ι) → β i) (i : ι)
    (v : β i) : update f i v i = v := by
  simp [update]

@[simp] theorem update_of_ne {ι : Type} [DecidableEq ι] {β : ι → Type} (f : (i : ι) → β i)
    {i j : ι} (v : β i) (h : j ≠ i) : update f i v j = f j := by
  simp [update, h]

variable {σ : Signature}

/-- The global state of a system. -/
structure SysState (sys : System σ) where
  /-- The private state of every actor. An actor that has never started is in its `init`. -/
  state : (i : σ.Id) → sys.State i
  /-- Which actors are running. -/
  up : σ.Id → Bool
  /-- Messages in flight, oldest first. -/
  net : List (Envelope σ)
  /-- The pending timers of every actor. -/
  timers : (i : σ.Id) → List (σ.Msg i)
  /-- Outputs emitted but not yet handed to the outside world. -/
  outbox : List σ.Out

/-- A step of a system. -/
inductive Event (σ : Signature) : Type where
  /-- An input arrives from outside and is queued for the actor that accepts it. -/
  | input (x : σ.In)
  /-- The receiver handles a message in flight; the message is consumed. -/
  | deliver (e : Envelope σ)
  /-- The receiver handles a message in flight that stays in flight (a duplicating link). -/
  | duplicate (e : Envelope σ)
  /-- A message in flight is lost (a lossy link). -/
  | drop (e : Envelope σ)
  /-- A pending timer of actor `i` fires and `i` handles its message. -/
  | timeout (i : σ.Id) (msg : σ.Msg i)
  /-- An emitted output is handed to the outside world. -/
  | output (out : σ.Out)
  /-- Actor `i` crashes. -/
  | crash (i : σ.Id)
  /-- Actor `i` starts, running its `recover`. -/
  | start (i : σ.Id)

/-- What the outside world can see of a system: the inputs it sends and the outputs it gets. -/
inductive Visible (σ : Signature) : Type where
  /-- An input arrived. -/
  | input (x : σ.In)
  /-- An output was handed over. -/
  | output (out : σ.Out)

/-- The visible part of an event. Everything but inputs and outputs is internal (`none`). -/
def Event.visible : Event σ → Option (Visible σ)
  | .input x => some (.input x)
  | .output out => some (.output out)
  | _ => none

namespace SysState

variable {sys : System σ}

/-- The state before anything has started: every actor at its `init` and down, nothing in
flight. -/
def blank (sys : System σ) : SysState sys where
  state i := (sys.actor i).init
  up _ := false
  net := []
  timers _ := []
  outbox := []

/-- Whether a message for `i` is in flight. -/
def hasMail (c : SysState sys) (i : σ.Id) : Bool :=
  c.net.any fun e => decide (e.dst = i)

/-- Perform one effect of actor `i`. `stop` is handled once the whole step is done, by `settle`. -/
def perform (c : SysState sys) (i : σ.Id) : Effect σ i → SysState sys
  | .send to msg => { c with net := c.net ++ [⟨some i, to, msg⟩] }
  | .emit out => { c with outbox := c.outbox ++ [out] }
  | .after _ msg =>
    { c with timers := update c.timers i (if msg ∈ c.timers i then c.timers i
        else c.timers i ++ [msg]) }
  | .cancel msg => { c with timers := update c.timers i ((c.timers i).erase msg) }
  | .stop => c

/-- Perform a list of effects of actor `i`, in order. -/
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

/-- Finish a step of actor `i`: store its new state, perform its effects, and stop it if it asked
to. -/
def settle (env : EnvModel σ) (c : SysState sys) (i : σ.Id)
    (r : sys.State i × List (Effect σ i)) : SysState sys :=
  let c := ({ c with state := update c.state i r.1 }).performAll i r.2
  if r.2.any Effect.isStop then c.down env i else c

/-- Actor `i` handles `msg`. -/
def handle (env : EnvModel σ) (c : SysState sys) (i : σ.Id) (msg : σ.Msg i) : SysState sys :=
  c.settle env i ((sys.actor i).step (c.state i) msg)

/-- Actor `i` starts: it comes up and runs `recover` on the state that survived. -/
def startActor (env : EnvModel σ) (c : SysState sys) (i : σ.Id) : SysState sys :=
  ({ c with up := update c.up i true }).settle env i ((sys.actor i).recover (c.state i))

/-- Whether `e` may be delivered now: it is in flight, and if its link is ordered it is the
oldest message on that link. -/
def deliverable (env : EnvModel σ) (c : SysState sys) (e : Envelope σ) : Bool :=
  if (env.link e.src e.dst).ordered then c.net.find? e.sameLink == some e else c.net.contains e

/--
Apply one event. The result is `none` when the event is not enabled in this state under this
environment model.
-/
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

/-- The state of a freshly booted system: the `boot` actors started in order. -/
def init (sys : System σ) (env : EnvModel σ) : SysState sys :=
  sys.boot.foldl (fun c i => c.startActor env i) (blank sys)

/-- Apply a list of events in order; `none` as soon as one is not enabled. -/
def run (env : EnvModel σ) (c : SysState sys) : List (Event σ) → Option (SysState sys)
  | [] => some c
  | ev :: evs => (c.step env ev).bind fun c' => c'.run env evs

end SysState

namespace System

variable (sys : System σ)

/-- The states a system can reach under an environment model. -/
inductive Reachable (env : EnvModel σ) : SysState sys → Prop
  | init : Reachable env (SysState.init sys env)
  | step {c c' : SysState sys} (ev : Event σ) :
    Reachable env c → c.step env ev = some c' → Reachable env c'

/-- `P` holds in every reachable state of the system. -/
def Invariant (env : EnvModel σ) (P : SysState sys → Prop) : Prop :=
  ∀ c, sys.Reachable env c → P c

/-- The proof obligation for a system invariant: it holds after boot and every enabled event
preserves it. -/
structure Inductive (env : EnvModel σ) (P : SysState sys → Prop) : Prop where
  /-- `P` holds in the freshly booted system. -/
  init : P (SysState.init sys env)
  /-- Every enabled event preserves `P`. -/
  step : ∀ c ev c', P c → c.step env ev = some c' → P c'

variable {sys}

/-- An inductive predicate is an invariant. -/
theorem Inductive.invariant {env : EnvModel σ} {P : SysState sys → Prop}
    (h : sys.Inductive env P) : sys.Invariant env P := by
  intro c hc
  induction hc with
  | init => exact h.init
  | step ev _ hstep ih => exact h.step _ ev _ ih hstep

end System

end Lanes
