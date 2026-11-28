/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std.Time
public import Lanes.Runtime.IO.Shell
public import Lanes.Web.Http.Ops

/-!
The IO of what the HTTP server tells its operators. It keeps the server's counts in a reference,
times each request, writes its line of the access log and tags its response with a request id,
and answers the operators' requests with what `Http.Ops` decides. What is counted, which request
is the operators', what each answers, what an id may be and what a line holds are decided there,
pure and proved.

It never enters a system and never changes what enters one: an operator's request is answered
here, before the request is prepared or has an id; any other request goes on as it came
(`docs/decisions/D69-observability.md`). With nothing configured, `front` returns what it is
given.
-/

public section

namespace Lanes.Http

/-- What a server keeps for its operators. -/
structure Ops where
  private mk ::
  config : OpsConfig
  private stats : IO.Ref (Ops.Stats config.latencyBounds_us)
  private draining : IO.Ref Bool

namespace Ops

/-- What the server reads of itself when an operator asks. -/
structure Probe where
  recovered : Bool
  stopping : Bool
  connections : Nat
  inflight : Nat
  inbox : Nat

def new (config : OpsConfig) : BaseIO Ops :=
  return { config, stats := ← IO.mkRef {}, draining := ← IO.mkRef false }

/-- From now on readiness answers `503`, so that a load balancer stops sending requests. -/
def drain (ops : Ops) : BaseIO Unit :=
  ops.draining.set true

/-- A connection was closed at `connections_max`. -/
def refused (ops : Ops) : BaseIO Unit := do
  if ops.config.counting then ops.stats.modify (·.refuse)

def write (sink : LogSink) (line : String) : BaseIO Unit :=
  match sink with
  | .off => pure ()
  | .stderr =>
    let put : IO Unit := do
      let err ← IO.getStderr
      err.putStr (line ++ "\n")
      err.flush
    discard put.toBaseIO
  | .call f => discard (f line).toBaseIO

def health (ops : Ops) (probe : Probe) : BaseIO Health :=
  return { recovered := probe.recovered, stopping := probe.stopping || (← ops.draining.get) }

/-- The metrics page. -/
def page (ops : Ops) (probe : Probe) : BaseIO String := do
  let ready := (← ops.health probe).ready
  let gauges := { connections := probe.connections, inflight := probe.inflight, inbox := probe.inbox
                  ready }
  return Metrics.render (families (← ops.stats.get) gauges)

/-- A new request id, from eight random bytes. -/
def freshId : BaseIO String := do
  match ← (IO.getRandomBytes 8).toBaseIO with
  | .ok bytes => return RequestId.ofBytes bytes.data.toList
  | .error _ => return toString (← IO.monoNanosNow)

def wallMs : BaseIO Nat := do
  match ← Std.Time.Timestamp.now.toBaseIO with
  | .ok t => return t.toMillisecondsSinceUnixEpoch.toInt.toNat
  | .error _ => return 0

/--
`submit` with the operators' part around it, for a connection from `peer`: an operator's request
is answered here, from `probe`; any other goes to `submit`. Either way its answer is counted,
logged and tagged with its request id before it is handed on.
-/
def front (ops : Ops) (probe : BaseIO Probe) (peer : Option Ip.Addr)
    (submit : Request → (Response → BaseIO Unit) → BaseIO Unit) :
    Request → (Response → BaseIO Unit) → BaseIO Unit :=
  if !ops.config.active then submit
  else fun request answer => do
    let config := ops.config
    let start ← IO.monoNanosNow
    let tagged := config.requestIds || config.accessLog.isOn
    let id ← if !tagged then pure "" else
      match (request.header? "x-request-id").bind (RequestId.accept? config.requestIdMax) with
      | some id => pure id
      | none => freshId
    let finish (response : Response) : BaseIO Unit := do
      let duration_us := ((← IO.monoNanosNow) - start) / 1000
      if config.counting then
        ops.stats.modify (·.answered request.method response.status duration_us)
      if config.accessLog.isOn then
        write config.accessLog <| Access.line {
          time_ms := ← wallMs, method := request.method, path := request.path
          status := response.status, duration_us, bytes := response.body.size, requestId := id }
      answer (if config.requestIds then RequestId.tag id response else response)
    match route? config peer request with
    | some endpoint =>
      let probe ← probe
      let page ← if endpoint == .metrics then ops.page probe else pure ""
      finish (Ops.answer endpoint (← ops.health probe) page)
    | none => submit request finish

end Ops

end Lanes.Http
