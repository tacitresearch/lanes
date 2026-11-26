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

variable {σ : Signature}

structure SysState (sys : System σ) where
  state : (i : σ.Id) → sys.State i
  up : σ.Id → Bool
  /-- Messages in flight, oldest first. -/
  net : List (Envelope σ)
  timers : (i : σ.Id) → List (σ.Msg i)
  outbox : List σ.Out

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

inductive Visible (σ : Signature) : Type where
  | input (x : σ.In)
  | output (out : σ.Out)

def Event.visible : Event σ → Option (Visible σ)
  | .input x => some (.input x)
  | .output out => some (.output out)
  | _ => none

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

def init (sys : System σ) (env : EnvModel σ) : SysState sys :=
  sys.boot.foldl (fun c i => c.startActor env i) (blank sys)

def run (env : EnvModel σ) (c : SysState sys) : List (Event σ) → Option (SysState sys)
  | [] => some c
  | ev :: evs => (c.step env ev).bind fun c' => c'.run env evs

end SysState

namespace System

variable (sys : System σ)

inductive Reachable (env : EnvModel σ) : SysState sys → Prop
  | init : Reachable env (SysState.init sys env)
  | step {c c' : SysState sys} (ev : Event σ) :
    Reachable env c → c.step env ev = some c' → Reachable env c'

def Invariant (env : EnvModel σ) (P : SysState sys → Prop) : Prop :=
  ∀ c, sys.Reachable env c → P c

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

end System

end Lanes
