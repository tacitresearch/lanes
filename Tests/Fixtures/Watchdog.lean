/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
# Reference app: a watchdog

The system of `examples/watchdog/Watchdog.lean`, copied (`Tests/Copies.lean`).

A dog barks when it has heard nothing from its keeper for a while. Every `ping` arms its
`silence` timer again, which starts the delay again, so the dog stays quiet for as long as pings
keep arriving. The keeper pings on a timer of its own until it is told to `rest`.

This is a keep-alive, the shape of a Raft follower's election timer under heartbeats.
`Tests/Fair.lean` runs it under the fair scheduler.
-/

namespace Tests.Fixtures.Watchdog

open Lanes

lanes_data inductive Id where
  | keeper
  | dog
  deriving DecidableEq, Repr, Hashable, Enum

inductive KeeperMsg where
  | tick
  | rest
  deriving DecidableEq, Repr, Hashable

inductive DogMsg where
  | ping
  | silence
  deriving DecidableEq, Repr, Hashable

abbrev Msg : Id → Type
  | .keeper => KeeperMsg
  | .dog => DogMsg

instance : ∀ i, DecidableEq (Msg i) := by instance_by_cases

/-- The one input tells the keeper to rest, and the one output is a bark. -/
abbrev sig : Signature where
  Id := Id
  Msg := Msg
  In := Unit
  Out := Unit

structure Config where
  interval_ms : Nat := 50
  /-- How long the dog waits for a ping. Longer than `interval_ms`, or it barks at a keeper
  that is on time. -/
  patience_ms : Nat := 150

def keeper (config : Config) : sig.Actor .keeper Unit where
  init := ()
  step _
    | .tick => ((), [.send .dog .ping, .after config.interval_ms .tick])
    | .rest => ((), [.cancel .tick])
  recover _ := ((), [.after config.interval_ms .tick])

def dog (config : Config) : sig.Actor .dog Unit where
  init := ()
  step _
    | .ping => ((), [.after config.patience_ms .silence])
    | .silence => ((), [.emit ()])
  recover _ := ((), [.after config.patience_ms .silence])

abbrev system (config : Config := {}) : System sig where
  State _ := Unit
  actor
    | .keeper => keeper config
    | .dog => dog config
  accept _ := ⟨.keeper, .rest⟩
  boot := [.keeper, .dog]

def ping : Envelope sig := ⟨some .keeper, .dog, .ping⟩

/-- The step in which the dog barks. -/
def bark : Event sig := .timeout .dog .silence

end Tests.Fixtures.Watchdog
