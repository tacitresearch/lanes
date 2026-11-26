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
  deriving BEq, Hashable

def client (requests : List (ReqId × Request)) : Driver (gatedSig echoSig) Client where
  init := { toSend := requests, answered := [] }
  inputs c := (List.range c.toSend.length).filterMap fun k =>
    c.toSend[k]?.map fun x => (x, { c with toSend := c.toSend.eraseIdx k })
  observe c out := { c with answered := (out.1, out.2.status) :: c.answered }

def get (path : List String) : Request := { method := .get, path }

def check (config : GateConfig) (requests : List (ReqId × Request)) (mustSee : Nat := 200)
    (env : EnvModel (gatedSig echoSig) := {}) (maxCrashes : Nat := 0) :=
  Check.system (gated (Server.system echo) bridge config)
    { env, driver := client requests, maxCrashes }
    [ .sometimes s!"a request gets {mustSee}" fun w => w.driver.answered.any (·.2 == mustSee),
      .always "no request is answered twice" fun w =>
        (w.driver.answered.map (·.1)).eraseDups.length == w.driver.answered.length,
      .sometimes "a request is answered by the system" fun w =>
        w.driver.answered.any (·.2 == 200),
      .sometimes "a request times out" fun w => w.driver.answered.any (·.2 == 504) ]
    { checkDeadlock := true
      terminal := fun w => w.driver.toSend.isEmpty
        && requests.all fun r => w.driver.answered.any (·.1 == r.1) }

def tests : List (String × Bool) :=
  let two := check {} [(1, get []), (2, get [])]
  let refused := check {} [(1, get ["bad"]), (2, get [])] (mustSee := 400)
  let full := check { maxPending := 1 } [(1, get []), (2, get [])] (mustSee := 503)
  let reused := check {} [(1, get []), (1, get [])]
  let crashing := check {} [(1, get [])] (env := { mayCrash := (·.isNone) }) (maxCrashes := 1)
  [ ("gate: each request is answered exactly once, whatever the timers do",
      two.ok && two.complete && two.witnesses.length == 3),
    ("gate: a request the bridge refuses is answered without entering the system",
      refused.ok && refused.complete),
    ("gate: beyond maxPending a request gets 503 and is still answered exactly once",
      full.ok && full.complete),
    ("gate: exactly once needs distinct request ids, which the adapter allocates",
      !reused.ok),
    ("gate: exactly once needs a gate that does not crash, which one shard guarantees",
      match crashing.failure with
      | some (.deadlock _) => true
      | _ => false) ]

end Tests.Gate
