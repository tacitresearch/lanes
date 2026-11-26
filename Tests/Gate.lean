/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
Model checks of the HTTP gate in front of a one-actor echo service. Timers may fire at any
moment in the model, so every race between a response and its deadline is explored.
-/

namespace Tests.Gate

open Lanes Lanes.Http

abbrev echoSig : Signature := Server.sig ReqId ReqId

def echo : Service echoSig Unit where
  init := ()
  step _ id := ((), [id])

def bridge : Bridge echoSig where
  decode id request := if request.path == ["bad"] then .error (.text "bad" 400) else .ok id
  encode id := some (id, .text "ok")

instance : (gatedSig echoSig).Inspect where
  reprMsg
    | none => inferInstanceAs (Repr (GateMsg echoSig))
    | some _ => inferInstanceAs (Repr ReqId)
  hashMsg
    | none => inferInstanceAs (Hashable (GateMsg echoSig))
    | some _ => inferInstanceAs (Hashable ReqId)

instance (config : GateConfig) : (gated (Server.system echo) bridge config).Inspect where
  beqState
    | none => inferInstanceAs (BEq (List ReqId))
    | some _ => inferInstanceAs (BEq Unit)
  reprState
    | none => inferInstanceAs (Repr (List ReqId))
    | some _ => inferInstanceAs (Repr Unit)
  hashState
    | none => inferInstanceAs (Hashable (List ReqId))
    | some _ => inferInstanceAs (Hashable Unit)

/-- The outside world: requests still to send, and the status each answered request got. -/
structure Client where
  toSend : List (ReqId × Request)
  answered : List (ReqId × Nat)
  deriving DecidableEq, Hashable

def client (requests : List (ReqId × Request)) : Driver (gatedSig echoSig) Client where
  init := { toSend := requests, answered := [] }
  inputs c := (List.range c.toSend.length).filterMap fun k =>
    c.toSend[k]?.map fun x => (x, { c with toSend := c.toSend.eraseIdx k })
  observe c out := { c with answered := (out.1, out.2.status) :: c.answered }

def get (path : List String) : Request := { method := .get, path }

abbrev GatedWorld (config : GateConfig) := World (gated (Server.system echo) bridge config) Client

/-- The ingredients of `Http.pending_leaves`, which the checker cannot check as a whole: the
deadline of a pending request is enabled while the gate is up, and firing it removes the
request. -/
def deadlinesFire {config : GateConfig} (env : EnvModel (gatedSig echoSig))
    (w : GatedWorld config) : Bool :=
  !w.state.up none ||
    (w.state.state none).all fun id =>
      match w.state.step env (.timeout none (.expire id)) with
      | some c => !(c.state none).contains id
      | none => false

def pendingWhileUp {config : GateConfig} (w : GatedWorld config) : Bool :=
  w.state.up none && !(w.state.state none).isEmpty

/-- A request leaves the pending list only in a step that emits its answer. -/
def leavingIsAnswered : Bool :=
  let messages : List (GateMsg echoSig) :=
    [.arrive 1 (get []), .arrive 3 (get []), .answer 1, .answer 3, .expire 1, .expire 2,
      .expire 3]
  [[], [1], [1, 2], [2, 1]].all fun pending => messages.all fun msg =>
    let (pending', effects) := (gate (Server.system echo) bridge {}).step pending msg
    pending.all fun id => pending'.contains id || effects.any fun
      | .emit out => out.1 == id
      | _ => false

def check (config : GateConfig) (requests : List (ReqId × Request)) (mustSee : Nat := 200)
    (env : EnvModel (gatedSig echoSig) := {}) (maxCrashes : Nat := 0) :=
  Check.system (gated (Server.system echo) bridge config)
    { env, driver := client requests, maxCrashes }
    [ .sometimes s!"a request gets {mustSee}" fun w => w.driver.answered.any (·.2 == mustSee),
      .always "no request is answered twice" fun w =>
        (w.driver.answered.map (·.1)).eraseDups.length == w.driver.answered.length,
      .sometimes "a request is answered by the system" fun w =>
        w.driver.answered.any (·.2 == 200),
      .sometimes "a request times out" fun w => w.driver.answered.any (·.2 == 504),
      .always "a gate that cannot crash stays up" fun w => env.mayCrash none || w.state.up none,
      .always "a pending request's deadline can fire, and firing it removes the request"
        (deadlinesFire env),
      .sometimes "a request is pending while the gate is up" pendingWhileUp ]
    { checkDeadlock := true
      terminal := fun w => w.driver.toSend.isEmpty
        && requests.all fun r => w.driver.answered.any (·.1 == r.1) }

def answeredAtMostAsOftenAsArrived {config : GateConfig} (requests : List (ReqId × Request))
    (w : GatedWorld config) : Bool :=
  requests.all fun (id, _) =>
    w.driver.answered.countP (·.1 == id) + w.driver.toSend.countP (·.1 == id)
      ≤ requests.countP (·.1 == id)

def deadlinesArmed {config : GateConfig} (w : GatedWorld config) : Bool :=
  !w.state.up none ||
    (w.state.state none).all fun id => (w.state.timers none).contains (.expire id)

/-- The gate crashes and restarts and every link loses and reorders. `answered_le_arrived`
allows all of it, and duplication on every link but the one from outside to the gate. -/
def hostile (duplicating : Option (Option Unit) → Option Unit → Bool) :
    EnvModel (gatedSig echoSig) where
  link src dst := { ordered := false, lossy := true, duplicating := duplicating src dst }
  mayCrash _ := true
  restarts _ := true

def checkArrivals (requests : List (ReqId × Request)) (env : EnvModel (gatedSig echoSig))
    (maxDepth : Option Nat := none) :=
  Check.system (gated (Server.system echo) bridge {})
    { env, driver := client requests, maxCrashes := 1 }
    [ .always "no request is answered more often than it arrived"
        (answeredAtMostAsOftenAsArrived requests),
      .always "every pending request has its deadline armed" deadlinesArmed,
      .always "a pending request's deadline can fire, and firing it removes the request"
        (deadlinesFire env),
      .sometimes "a request is pending while the gate is up" pendingWhileUp,
      .sometimes "an id that arrived twice is answered twice" fun w =>
        w.driver.answered.countP (·.1 == 1) == 2 ]
    { maxDepth }

def tests : List (String × Bool) :=
  let two := check {} [(1, get []), (2, get [])]
  let refused := check {} [(1, get ["bad"]), (2, get [])] (mustSee := 400)
  let full := check { maxPending := 1 } [(1, get []), (2, get [])] (mustSee := 503)
  let reused := check {} [(1, get []), (1, get [])]
  let crashing := check {} [(1, get [])] (env := { mayCrash := (·.isNone) }) (maxCrashes := 1)
  let twice := [(1, get []), (1, get ["bad"])]
  let lossy := checkArrivals twice (hostile fun _ _ => false)
  let duplicating := checkArrivals twice (hostile fun src dst => src.isSome || dst.isSome)
    (maxDepth := some 12)
  let duplicatedOutside := checkArrivals [(1, get ["bad"])] (hostile fun _ _ => true)
    (maxDepth := some 8)
  [ ("gate: each request is answered exactly once, whatever the timers do",
      two.ok && two.complete && two.witnesses.length == 4),
    ("gate: a request the bridge refuses is answered without entering the system",
      refused.ok && refused.complete),
    ("gate: beyond maxPending a request gets 503 and is still answered exactly once",
      full.ok && full.complete),
    ("gate: exactly once needs distinct request ids, which the adapter allocates",
      !reused.ok),
    ("gate: exactly once needs a gate that does not crash, which one shard guarantees",
      match crashing.failure with
      | some (.deadlock _) => true
      | _ => false),
    ("gate: no id is answered more often than it arrived and pending deadlines stay armed, "
        ++ "though the gate crashes and links lose and reorder",
      lossy.ok && lossy.complete && lossy.witnesses.length == 2),
    ("gate: the same when every link but the one from outside duplicates, to depth 12",
      duplicating.ok && duplicating.witnesses.length == 2),
    ("gate: at most once per arrival needs the link from outside not to duplicate",
      match duplicatedOutside.failure with
      | some (.violated "no request is answered more often than it arrived" _) => true
      | _ => false),
    ("gate: a pending request's deadline can fire and firing it removes the request, with and "
        ++ "without faults, and a gate that cannot crash stays up",
      two.ok && two.complete && full.ok && full.complete && lossy.ok && lossy.complete),
    ("gate: a request leaves the pending list only in a step that emits its answer",
      leavingIsAnswered) ]

end Tests.Gate
