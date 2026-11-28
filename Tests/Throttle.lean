/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
The throttling model (`Lanes/Outside/Throttle.lean`) against a caller with two requests to make
and at most `maxAttempts` calls for each. The service takes one call a tick and answers one
beyond that `429` with a `Retry-After` of one or two ticks. A caller that retries at once calls
while it was told to wait, and within its attempts never gets through; one that holds every call
until the wait it was told has passed calls only when it may, and both requests get through.
-/

namespace Tests.Throttle

open Lanes

abbrev Answer := Lanes.Throttle.Answer Nat

inductive In where
  | want (n : Nat)
  | reply (call : Nat) (reply : Rpc.Reply Answer)
  | tick
  deriving DecidableEq, Repr, Hashable

inductive Out where
  | call (c : Rpc.Call Nat)
  | done (n : Nat)
  | gaveUp (n : Nat)
  deriving DecidableEq, Repr, Hashable

abbrev sig : Signature where
  Id := Unit
  Msg _ := In
  In := In
  Out := Out

def maxAttempts : Nat := 3

/-- The next call id, the ticks seen, the tick the service said to wait for, the calls open
with their request and attempt, and the requests held until then with their next attempt. -/
structure Caller where
  next : Nat := 0
  now : Nat := 0
  retryAt : Nat := 0
  calls : List (Nat × Nat × Nat) := []
  held : List (Nat × Nat) := []
  deriving DecidableEq, Repr, Hashable

def Caller.call (s : Caller) (n attempt : Nat) : Caller × List (Effect sig ()) :=
  ({ s with next := s.next + 1, calls := (s.next, n, attempt) :: s.calls },
    [.emit (.call ⟨s.next, 1000, n⟩)])

def Caller.callAll (s : Caller) : List (Nat × Nat) → Caller × List (Effect sig ())
  | [] => (s, [])
  | (n, attempt) :: rest =>
    let (s, e) := s.call n attempt
    let (s, e') := s.callAll rest
    (s, e ++ e')

/-- `backoff` off seeds the bug: a throttled call is made again at once. -/
def step (backoff : Bool) (s : Caller) : In → Caller × List (Effect sig ())
  | .want n => if backoff && s.now < s.retryAt then ({ s with held := s.held ++ [(n, 1)] }, [])
    else s.call n 1
  | .reply id reply =>
    match s.calls.find? (·.1 == id) with
    | none => (s, [])
    | some (_, n, attempt) =>
      let s := { s with calls := s.calls.filter (·.1 != id) }
      match reply with
      | .answer (.ok _) => (s, [.emit (.done n)])
      | .answer (.throttled retryAfter) =>
        if maxAttempts ≤ attempt then (s, [.emit (.gaveUp n)])
        else if backoff then
          ({ s with retryAt := max s.retryAt (s.now + retryAfter),
                    held := s.held ++ [(n, attempt + 1)] }, [])
        else s.call n (attempt + 1)
      | .unknown => (s, [.emit (.gaveUp n)])
  | .tick =>
    let s := { s with now := s.now + 1 }
    if s.retryAt ≤ s.now then { s with held := [] }.callAll s.held else (s, [])

abbrev caller (backoff : Bool) : System sig where
  State _ := Caller
  actor _ := { init := {}, step := step backoff, recover := fun s => (s, []) }
  accept x := ⟨(), x⟩

instance : sig.Inspect := {}
instance (backoff : Bool) : (caller backoff).Inspect := {}

/-- The service behind the limit answers each call with its request. -/
def echo : Rpc.Server (List (Nat × Nat)) Nat Nat Unit where
  init := []
  receive d call := (call.id, call.request) :: d
  answer d call a := if (call, a) ∈ d then some d else none

def port : Rpc.Port sig Nat Answer (Lanes.Throttle.Event Unit) where
  called | .call c => some c | _ => none
  replied | .reply id r => some (id, r) | _ => none
  notified | .tick => some .tick | _ => none

def config : Lanes.Throttle.Config := { maxRetryAfter := 2, maxTicks := 3, burst := some 1 }

abbrev Service := Rpc.State (Lanes.Throttle.State (List (Nat × Nat)))

def clients : Outside sig (List Nat) where
  init := []
  allow d
    | .want n => if n ∈ d ∨ 2 ≤ n then none else some (n :: d)
    | _ => none

def world := clients.both (Rpc.outside port (Lanes.Throttle.server config echo)) (· matches .want _)

def samples (d : List Nat × Service) : List In :=
  [.want 0, .want 1, .tick] ++ d.2.pending.flatMap fun id =>
    let request := (d.2.server.inner.lookup id).getD 0
    [.reply id (.answer (.ok request)), .reply id (.answer (.throttled 1)),
      .reply id (.answer (.throttled 2))]

def gaveUp (w : World (caller backoff) (List Nat × Service)) : Bool :=
  w.state.outbox.any (· matches .gaveUp _)

def check (backoff : Bool) (props : List (Check.Property (World (caller backoff) (List Nat × Service)))) :=
  Check.system (caller backoff) { driver := world.driver samples } props

def polite (backoff : Bool) : Check.Property (World (caller backoff) (List Nat × Service)) :=
  .always "no call is made while the service asked to wait" fun w => w.driver.2.server.early == 0

def through (backoff : Bool) : Check.Property (World (caller backoff) (List Nat × Service)) :=
  .always "no request is given up" fun w => !gaveUp w

def steps {S L : Type} : Option (Check.Failure S L) → Nat
  | some (.violated _ t) => t.steps.length
  | _ => 0

def callOut (id n : Nat) : Lanes.Event sig := .output (.call ⟨id, 1000, n⟩)

def tests : List (String × Bool) :=
  let hammers := check false [polite false]
  let never := check false [through false]
  let fixed := check true [polite true, through true,
    .sometimes "a throttled request gets through" fun w =>
      w.driver.2.server.retryAt > 0 && (w.state.state ()).calls.isEmpty
        && (w.state.state ()).held.isEmpty && !gaveUp w && w.driver.1.length == 2]
  let model := Rpc.outside port (Lanes.Throttle.server config echo)
  [ (s!"throttle model: a caller that retries at once calls while told to wait "
        ++ s!"({steps hammers.failure} steps)",
      match hammers.failure with
      | some (.violated "no call is made while the service asked to wait" _) => true
      | _ => false),
    (s!"throttle model: and gives up without getting through ({steps never.failure} steps)",
      match never.failure with
      | some (.violated "no request is given up" _) => true
      | _ => false),
    (s!"throttle model: one that waits as told calls only when it may, and gets through "
        ++ s!"({fixed.states} states)",
      fixed.ok),
    ("throttle model: a call within the limit is not throttled, one beyond it is",
      !model.allows [callOut 0 0, .input (.reply 0 (.answer (.throttled 1)))]
        && model.allows [callOut 0 0, callOut 1 1, .input (.reply 1 (.answer (.throttled 1))),
          .input .tick, callOut 2 1, .input (.reply 2 (.answer (.ok 1)))]
        && !model.allows [callOut 0 0, callOut 1 1, .input (.reply 1 (.answer (.ok 1)))]),
    ("throttle model: no Retry-After longer than the most it gives",
      !model.allows [callOut 0 0, callOut 1 1, .input (.reply 1 (.answer (.throttled 3)))]) ]

end Tests.Throttle
