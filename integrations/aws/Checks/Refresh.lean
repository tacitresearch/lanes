/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Aws

/-!
The refresh policy model-checked (Lanes rule 5.1) as an actor against a model of the metadata
service (`Rpc.outside`): each fetch answered once with credentials it issues, `unknown`, late or
never, and a clock that reads any time from the last on, up to a horizon. The edge's loop is
lock-step: it tells the machine one thing, then waits for what it says (a fetch, and when to
wake), so the clock's model sends nothing while an answer is pending. The actor may crash and
start empty, as a process does.

Against every such outside: only credentials the service gave are held, none is handed out
within `skew_ms` of its expiry, the wait after failures stays within `maxBackoff_ms`, and the
next fetch after a failure is within it. Against a service that always answers within the
deadline with credentials longer than the margin, and a clock that never passes the wake the
machine asked for: once credentials are held, some are handed out at every moment. With the
margin shorter than the deadline and the skew, the checker finds a moment without credentials.
-/

namespace Checks.Refresh

open Lanes Aws.Refresh

inductive In where
  | tick (now : Nat)
  | reply (now call : Nat) (reply : Rpc.Reply (Held Nat)) (jitter : Nat)
  deriving DecidableEq, Repr, Hashable

/-- What a step says: the fetch to make, if any, and when to tick next. One output, so the
clock's model sees both at once. -/
inductive Out where
  | step (fetch : Option (Rpc.Call Unit)) (wake_ms : Nat)
  deriving DecidableEq, Repr, Hashable

abbrev sig : Signature where
  Id := Unit
  Msg _ := In
  In := In
  Out := Out

def In.msg : In → Msg Nat
  | .tick now => .tick now
  | .reply now call r jitter => .reply now call r jitter

def In.time : In → Nat
  | .tick now | .reply now .. => now

/-- The machine as an actor. Its state is volatile: a crash starts it empty. -/
abbrev refresher (cfg : Config) : System sig where
  State _ := State Nat
  actor _ :=
    { init := {}
      step := fun s x =>
        let (s', call) := step cfg s x.msg
        (s', [.emit (.step call s'.wake)]) }
  accept x := ⟨(), x⟩

instance : sig.Inspect := {}
instance (cfg : Config) : (refresher cfg).Inspect := {}

/-- The service issues credentials numbered in order, each good for at least `minLife_ms` from
when it answers. -/
def metadata (minLife_ms : Nat) : Rpc.Server (List (Held Nat)) Unit (Nat × Held Nat) Empty where
  init := []
  receive s _ := s
  answer s _ | (now, h) => if h.creds = s.length ∧ now + minLife_ms ≤ h.expires_ms then some (s ++ [h]) else none

def port : Rpc.Port sig Unit (Nat × Held Nat) Empty where
  called | .step call _ => call
  replied
    | .reply now call (.answer h) _ => some (call, .answer (now, h))
    | .reply _ call .unknown _ => some (call, .unknown)
    | .tick _ => none

structure Clock where
  now : Nat := 0
  wake : Nat := 0
  busy : Bool := false
  /-- When each call still open was made. -/
  sent : List (Nat × Nat) := []
  service : Rpc.State (List (Held Nat))
  deriving DecidableEq, Hashable

instance : BEq Clock := instBEqOfDecidableEq

/-- The clock and the service. `onTime`: the clock never passes the wake asked for, and the
service answers every call by its deadline, never `unknown`, before the clock reaches it. -/
def world (cfg : Config) (minLife_ms : Nat) (onTime : Bool) : Outside sig Clock :=
  let service := Rpc.outside port (metadata minLife_ms)
  { init := { service := service.init }
    allow := fun d x =>
      let t := x.time
      if d.busy || t < d.now then none
      else match x with
        | .tick _ =>
          if onTime && (d.wake < t || (!d.service.pending.isEmpty && d.wake ≤ t)) then none
          else some { d with now := t, busy := true }
        | .reply _ call r _ =>
          let late := ((d.sent.lookup call).map fun s => decide (s + cfg.deadline_ms < t)).getD true
          if onTime && (late || r == .unknown) then none
          else (service.allow d.service x).map fun s =>
            { d with now := t, busy := true, service := s, sent := d.sent.filter (·.1 ∈ s.pending) }
    observe := fun d out =>
      match out with
      | .step call w =>
        { d with wake := w, busy := false, service := service.observe d.service out
                 sent := (call.map fun c => (c.id, d.now)).toList ++ d.sent } }

def samples (cfg : Config) (horizon : Nat) (lifetimes jitters : List Nat) (d : Clock) : List In :=
  let times := ([d.now + 1, d.wake, d.wake + 1].filter (· ≤ horizon)).eraseDups
  let issued := d.service.server.length
  let replies := d.service.pending.eraseDups.flatMap fun call =>
    let sentAt := (d.sent.lookup call).getD d.now
    let at_ := ([d.now, sentAt + cfg.deadline_ms].filter (· ≤ horizon)).eraseDups
    at_.flatMap fun t => In.reply t call .unknown 0 ::
      lifetimes.flatMap fun life => jitters.map fun j => In.reply t call (.answer ⟨issued, t + life⟩) j
  times.map .tick ++ replies

def small : Config :=
  { margin_ms := 5, jitter_ms := 1, skew_ms := 1, deadline_ms := 2, backoff_ms := 1, maxBackoff_ms := 4 }

def env : EnvModel sig where
  mayCrash _ := true

abbrev W (cfg : Config) := World (refresher cfg) Clock

def held (w : W cfg) : Option (Held Nat) := (w.state.state ()).held

def faults (cfg : Config := small) (horizon : Nat := 9) :=
  Check.system (refresher cfg)
    { env, driver := (world cfg 0 false).driver (samples cfg horizon [3, 9] [1]), maxCrashes := 1 }
    [ .always "only credentials the service gave are held" fun w =>
        (held w).all (· ∈ w.driver.service.server),
      .always "nothing within skew_ms of its expiry is handed out" fun w =>
        match current cfg (w.state.state ()) w.driver.now with
        | some c => w.driver.service.server.any fun h =>
            h.creds == c && w.driver.now + cfg.skew_ms < h.expires_ms
        | none => true,
      .always "the wait after failures stays within maxBackoff_ms" fun w =>
        (w.state.state ()).backoff_ms ≤ cfg.maxBackoff_ms,
      .always "after a failure the next fetch is within maxBackoff_ms" fun w =>
        w.driver.busy || (w.state.state ()).backoff_ms == 0 ||
          match (w.state.state ()).phase with
          | .waiting wake => wake ≤ w.driver.now + cfg.maxBackoff_ms
          | .fetching .. => true,
      .sometimes "credentials are refreshed" fun w => (held w).any (·.creds ≥ 1),
      .sometimes "a fetch fails while credentials held are handed out" fun w =>
        (w.state.state ()).backoff_ms > 0 && (current cfg (w.state.state ()) w.driver.now).isSome,
      .sometimes "the wait reaches maxBackoff_ms" fun w =>
        (w.state.state ()).backoff_ms == cfg.maxBackoff_ms ]

def answering (cfg : Config := small) (horizon : Nat := 22) :=
  Check.system (refresher cfg)
    { driver := (world cfg 9 true).driver (samples cfg horizon [9, 12] [0, 1]) }
    [ .always "once credentials are held, some are handed out at every moment" fun w =>
        w.driver.busy || w.driver.service.server.isEmpty ||
          (current cfg (w.state.state ()) w.driver.now).isSome,
      .sometimes "credentials are refreshed twice" fun w => (held w).any (·.creds ≥ 2) ]

/-- The margin shorter than the deadline and the skew: a configuration `Config.Valid` refuses. -/
def tight : Config := { small with margin_ms := 2 }

def tests : List (String × Bool) :=
  let f := faults
  let a := answering
  let gap := match (answering tight).failure with
    | some (.violated "once credentials are held, some are handed out at every moment" _) => true
    | _ => false
  [ ("refresh: under faults, only fresh credentials the service gave are handed out, and the backoff is bounded",
      f.ok && f.complete && f.witnesses.length == 3),
    ("refresh: answered in time, credentials are never missing once held",
      a.ok && a.complete && a.witnesses.length == 1),
    ("refresh: with the margin shorter than the deadline, the checker finds a moment without them",
      gap && decide small.Valid && !decide tight.Valid) ]

def report : String :=
  faults.renderSystem ++ "\n" ++ answering.renderSystem

end Checks.Refresh
