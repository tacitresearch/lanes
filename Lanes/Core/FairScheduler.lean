/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Core.Step

/-!
# A scheduler that keeps nothing waiting forever

A system owes the events it makes happen itself, while they are possible: delivering a
deliverable message to an actor that is up, firing an armed timer of an actor that is up,
starting a stopped actor that has mail, handing over an output. `FairScheduler` keeps the owed
events in a queue, the one owed longest first, and always takes the first. An event that stays
owed is therefore taken after at most as many steps as there were events ahead of it.

After a step the queue is brought up to date from what the step can have changed: the messages
in flight, the outbox, and the timers of the one actor that took the step. No list of all actors
is needed, so a signature may have infinitely many identities.

A timer that a step arms again is owed anew and goes to the back of the queue, as the runtime
gives it a new deadline. So a timer that its actor keeps arming again does not fire while the
steps that arm it keep coming, and one that is left alone fires in its turn.

`Lanes.Semantics.FairRuns` proves from this scheduler that every finite run extends to a fair
one.
-/

@[expose] public section

namespace Lanes

variable {σ : Signature}

deriving instance DecidableEq for Event

/-- The actor that takes the step, where the event is a step of one actor. No event changes
whether another actor is up, or another actor's timers. -/
def Event.actor? : Event σ → Option σ.Id
  | .deliver e | .duplicate e => some e.dst
  | .timeout i _ | .crash i | .start i => some i
  | .input _ | .drop _ | .output _ => none

/-- The timers that the effects of actor `i` arm, as the events that fire them. -/
def Effect.timeouts (i : σ.Id) (effs : List (Effect σ i)) : List (Event σ) :=
  effs.filterMap fun
    | .after _ msg => some (.timeout i msg)
    | _ => none

namespace SysState

variable {sys : System σ}

/-- The timers that taking `ev` from `c` arms, as the events that fire them. The runtime gives
a pending timer among them a new deadline, where the semantics leaves it as it is. -/
def arms (c : SysState sys) : Event σ → List (Event σ)
  | .deliver e | .duplicate e =>
    Effect.timeouts e.dst ((sys.actor e.dst).step (c.state e.dst) e.msg).2
  | .timeout i msg => Effect.timeouts i ((sys.actor i).step (c.state i) msg).2
  | .start i => Effect.timeouts i ((sys.actor i).recover (c.state i)).2
  | .input _ | .drop _ | .output _ | .crash _ => []

/-- The environment's events (inputs, duplicates, drops, crashes) are never owed, and neither is
starting an actor that has no mail. -/
def owed (env : EnvModel σ) (c : SysState sys) : Event σ → Bool
  | .deliver e => c.up e.dst && c.deliverable env e
  | .timeout i msg => c.up i && (c.timers i).contains msg
  | .start i => !c.up i && c.hasMail i
  | .output out => c.outbox.contains out
  | .input _ | .duplicate _ | .drop _ | .crash _ => false

/-- Contains every owed event except the timers of actors outside `actors`. -/
def maybeOwed (c : SysState sys) (actors : List σ.Id) : List (Event σ) :=
  c.net.map .deliver ++ c.net.map (fun e => .start e.dst) ++ c.outbox.map .output
    ++ actors.flatMap fun i => (c.timers i).map (.timeout i)

end SysState

structure FairScheduler (sys : System σ) where
  state : SysState sys
  /-- The events owed in `state`, the one owed longest first. -/
  queue : List (Event σ)

namespace FairScheduler

variable {sys : System σ}

/-- The queue after a step into `c` that changed the timers of no actor outside `actors`: what
is no longer owed leaves, what is newly owed joins at the back. -/
def requeue (env : EnvModel σ) (c : SysState sys) (actors : List σ.Id) (queue : List (Event σ)) :
    List (Event σ) :=
  let kept := queue.filter (c.owed env)
  kept ++ ((c.maybeOwed actors).filter fun ev => c.owed env ev && !kept.contains ev).eraseDups

def init (sys : System σ) (env : EnvModel σ) : FairScheduler sys :=
  let c := SysState.init sys env
  ⟨c, requeue env c sys.boot []⟩

/-- Take `ev`, which goes to the back of the queue, as do the timers it arms again. An event
that is not enabled changes nothing. -/
def take (env : EnvModel σ) (s : FairScheduler sys) (ev : Event σ) : FairScheduler sys :=
  match s.state.step env ev with
  | none => s
  | some c =>
    let waiting := (s.queue.erase ev).filter fun e => !(s.state.arms ev).contains e
    ⟨c, requeue env c ev.actor?.toList (waiting ++ [ev])⟩

def next (env : EnvModel σ) (s : FairScheduler sys) : Option (Event σ) :=
  s.queue.find? (s.state.owed env)

def advance (env : EnvModel σ) (s : FairScheduler sys) : FairScheduler sys :=
  match s.next env with
  | none => s
  | some ev => s.take env ev

end FairScheduler

end Lanes
