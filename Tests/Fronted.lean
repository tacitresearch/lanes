/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Tests.Gate

/-!
Model checks of `Http.fronted`: the gate joined by `System.join` in front of a service that
also puts out what is no answer (a `memo`) and takes an input that is no request (a `note`).
The properties are those `Tests/Gate.lean` checks of the hand-built `gated`.
-/

namespace Tests.Fronted

open Lanes Lanes.Http

inductive Ask where
  | ask (id : ReqId)
  | note (n : Nat)
  deriving DecidableEq, Repr, Hashable

inductive Told where
  | reply (id : ReqId)
  | memo (n : Nat)
  deriving DecidableEq, Repr, Hashable

abbrev deskSig : Signature := Server.sig Ask Told

/-- Answers each request and writes a memo beside the answer; a note gives a memo alone. -/
def desk : Service deskSig Unit where
  init := ()
  step _
    | .ask id => ((), [.reply id, .memo id])
    | .note n => ((), [.memo n])

def bridge : Bridge deskSig where
  decode id request :=
    if request.path == ["bad"] then .error (.text "bad" 400) else .ok (.ask id)
  encode
    | .reply id => some (id, .text "ok")
    | .memo _ => none

abbrev Fronted (config : GateConfig) := fronted (Server.system desk) bridge config

instance : deskSig.Inspect := {}
instance : (Server.system desk).Inspect := {}

instance : (gateSig deskSig).Inspect where
  reprMsg _ := inferInstanceAs (Repr (GateMsg deskSig))
  hashMsg _ := inferInstanceAs (Hashable (GateMsg deskSig))

instance (config : GateConfig) : (gateSystem bridge config).Inspect where
  beqState _ := inferInstanceAs (BEq (List ReqId))
  reprState _ := inferInstanceAs (Repr (List ReqId))
  hashState _ := inferInstanceAs (Hashable (List ReqId))

instance : (joinSig (gateSig deskSig) deskSig).Inspect := .join
instance : (frontedSig deskSig).Inspect := .withIO
instance (config : GateConfig) :
    ((gateSystem bridge config).join (Server.system desk) (frontWiring bridge)).Inspect := .join
instance (config : GateConfig) : (Fronted config).Inspect := .filterMapIO

abbrev gateId : (frontedSig deskSig).Id := .inl ()

/-- The outside world: inputs still to send, the status each answered request got, and the
memos seen. -/
structure Client where
  toSend : List (frontedSig deskSig).In
  answered : List (ReqId × Nat)
  memos : List Nat
  deriving DecidableEq, Hashable

def client (inputs : List (frontedSig deskSig).In) : Driver (frontedSig deskSig) Client where
  init := { toSend := inputs, answered := [], memos := [] }
  inputs c := (List.range c.toSend.length).filterMap fun k =>
    c.toSend[k]?.map fun x => (x, { c with toSend := c.toSend.eraseIdx k })
  observe c
    | .inl (id, response) => { c with answered := (id, response.status) :: c.answered }
    | .inr (.memo n) => { c with memos := n :: c.memos }
    | .inr (.reply _) => c

def get (id : ReqId) (path : List String := []) : (frontedSig deskSig).In :=
  .inl (id, { method := .get, path })

def requestIds (inputs : List (frontedSig deskSig).In) : List ReqId :=
  inputs.filterMap fun
    | .inl (id, _) => some id
    | .inr _ => none

abbrev FrontedWorld (config : GateConfig) := World (Fronted config) Client

def pending {config : GateConfig} (w : FrontedWorld config) : List ReqId :=
  w.state.state gateId

def deadlinesFire {config : GateConfig} (env : EnvModel (frontedSig deskSig))
    (w : FrontedWorld config) : Bool :=
  !w.state.up gateId ||
    (pending w).all fun id =>
      match w.state.step env (.timeout gateId (.expire id)) with
      | some c => !(c.state gateId).contains id
      | none => false

def deadlinesLeftAlone {config : GateConfig} (w : FrontedWorld config) : Bool :=
  let leaves (ev : Event (frontedSig deskSig)) : Bool :=
    (pending w).all fun id => !(w.state.arms ev).contains (.timeout gateId (.expire id))
  !w.state.up gateId ||
    (w.state.net.all fun e => leaves (.deliver e))
      && (w.state.timers gateId).all fun msg => leaves (.timeout gateId msg)

def deadlinesOfPending {config : GateConfig} (w : FrontedWorld config) : Bool :=
  (w.state.timers gateId).all fun
    | .expire id => (pending w).contains id
    | _ => false

def pendingWhileUp {config : GateConfig} (w : FrontedWorld config) : Bool :=
  w.state.up gateId && !(pending w).isEmpty

def check (config : GateConfig) (inputs : List (frontedSig deskSig).In) (mustSee : Nat := 200)
    (env : EnvModel (frontedSig deskSig) := {}) (maxCrashes : Nat := 0) :=
  Check.system (Fronted config) { env, driver := client inputs, maxCrashes }
    [ .sometimes s!"a request gets {mustSee}" fun w => w.driver.answered.any (·.2 == mustSee),
      .always "no request is answered twice" fun w =>
        (w.driver.answered.map (·.1)).eraseDups.length == w.driver.answered.length,
      .sometimes "a request is answered by the system" fun w =>
        w.driver.answered.any (·.2 == 200),
      .sometimes "a request times out" fun w => w.driver.answered.any (·.2 == 504),
      .always "a gate that cannot crash stays up" fun w => env.mayCrash gateId || w.state.up gateId,
      .always "a pending request's deadline can fire, and firing it removes the request"
        (deadlinesFire env),
      .always "an armed deadline is that of a pending request" deadlinesOfPending,
      .always "no step arms a pending request's deadline again" deadlinesLeftAlone,
      .sometimes "a request is pending while the gate is up" pendingWhileUp,
      .always "a response comes out through the gate only" fun w =>
        w.state.outbox.all fun out => !(out matches .inr (.reply _)),
      .sometimes "a memo passes the gate by" fun w => !w.driver.memos.isEmpty ]
    { checkDeadlock := true
      terminal := fun w => w.driver.toSend.isEmpty
        && (requestIds inputs).all fun id => w.driver.answered.any (·.1 == id) }

def answeredAtMostAsOftenAsArrived {config : GateConfig} (inputs : List (frontedSig deskSig).In)
    (w : FrontedWorld config) : Bool :=
  (requestIds inputs).all fun id =>
    w.driver.answered.countP (·.1 == id) + (requestIds w.driver.toSend).count id
      ≤ (requestIds inputs).count id

def deadlinesArmed {config : GateConfig} (w : FrontedWorld config) : Bool :=
  !w.state.up gateId ||
    (pending w).all fun id => (w.state.timers gateId).contains (.expire id)

/-- Every actor crashes and restarts and every link loses and reorders. -/
def hostile (duplicating : Option (frontedSig deskSig).Id → (frontedSig deskSig).Id → Bool) :
    EnvModel (frontedSig deskSig) where
  link src dst := { ordered := false, lossy := true, duplicating := duplicating src dst }
  mayCrash _ := true
  restarts _ := true

def checkArrivals (inputs : List (frontedSig deskSig).In) (env : EnvModel (frontedSig deskSig))
    (maxDepth : Option Nat := none) :=
  Check.system (Fronted {}) { env, driver := client inputs, maxCrashes := 1 }
    [ .always "no request is answered more often than it arrived"
        (answeredAtMostAsOftenAsArrived inputs),
      .always "every pending request has its deadline armed" deadlinesArmed,
      .always "a pending request's deadline can fire, and firing it removes the request"
        (deadlinesFire env),
      .always "an armed deadline is that of a pending request" deadlinesOfPending,
      .always "no step arms a pending request's deadline again" deadlinesLeftAlone,
      .sometimes "a request is pending while the gate is up" pendingWhileUp,
      .sometimes "an id that arrived twice is answered twice" fun w =>
        w.driver.answered.countP (·.1 == 1) == 2 ]
    { maxDepth }

def tests : List (String × Bool) :=
  let two := check {} [get 1, get 2]
  let noted := check {} [get 1, .inr (.note 7)]
  let refused := check {} [get 1 ["bad"], get 2] (mustSee := 400)
  let full := check { maxPending := 1 } [get 1, get 2] (mustSee := 503)
  let reused := check {} [get 1, get 1]
  let crashing := check {} [get 1] (env := { mayCrash := (· == gateId) }) (maxCrashes := 1)
  let twice := [get 1, get 1 ["bad"]]
  let lossy := checkArrivals twice (hostile fun _ _ => false)
  let duplicating := checkArrivals twice (hostile fun src dst => src.isSome || dst != gateId)
    (maxDepth := some 12)
  let duplicatedOutside := checkArrivals [get 1 ["bad"]] (hostile fun _ _ => true)
    (maxDepth := some 8)
  [ ("fronted: each request is answered exactly once, whatever the timers do, and its memo "
        ++ "passes the gate by",
      two.ok && two.complete && two.witnesses.length == 5),
    ("fronted: an input that is no request reaches the system behind the gate",
      noted.ok && noted.complete
        && noted.witnesses.any fun (name, _) => name == "a memo passes the gate by"),
    ("fronted: a request the bridge refuses is answered without entering the system",
      refused.ok && refused.complete),
    ("fronted: beyond maxPending a request gets 503 and is still answered exactly once",
      full.ok && full.complete),
    ("fronted: a request id used twice is answered twice, and the check says so",
      match reused.failure with
      | some (.violated "no request is answered twice" _) => true
      | _ => false),
    ("fronted: exactly once needs a gate that does not crash",
      match crashing.failure with
      | some (.deadlock _) => true
      | _ => false),
    ("fronted: no id is answered more often than it arrived and pending deadlines stay armed, "
        ++ "though actors crash and links lose and reorder",
      lossy.ok && lossy.complete && lossy.witnesses.length == 2),
    ("fronted: the same when every link but the one from outside to the gate duplicates, "
        ++ "to depth 12",
      duplicating.ok && duplicating.witnesses.length == 2),
    ("fronted: at most once per arrival needs the link from outside to the gate not to duplicate",
      match duplicatedOutside.failure with
      | some (.violated "no request is answered more often than it arrived" _) => true
      | _ => false) ]

end Tests.Fronted
