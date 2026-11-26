/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std.Http
public import Std.Data.HashMap
public import Lanes.Actors.Runtime
public import Lanes.Http.Gate

/-!
The HTTP server adapter: the IO around `Lanes.Http.gate`. It reads a request, gives it an id no
other request has, hands it to the gated system as an input, and writes the one response the
gate gives for it. Which requests are waiting, when one times out and when the system is too
busy are the gate's decisions, not this file's.

Two refusals are made here: `405` for a method an application cannot handle, and `503` when the
shard's inbox is full. TLS is not handled: terminate it in a reverse proxy.
-/

public section

namespace Lanes.Http

open Std Std.Async

variable {σ : Signature}

/-- Every limit is explicit (rule 2.6). -/
structure ServerConfig where
  /-- The IPv4 address to bind. -/
  host : String := "127.0.0.1"
  /-- `0` picks a free port. -/
  port : UInt16 := 8080
  /-- Larger request bodies are refused with `413`. -/
  maxBodyBytes : Nat := 1048576
  gate : GateConfig := {}

/-- The runtime is private because the gate answers each request once only if request ids are
never reused, and `serve` is what allocates them. -/
structure Server (sys : System σ) (bridge : Bridge σ) (config : ServerConfig)
    [Hashable σ.Id] where
  private mk ::
  private runtime : Runtime (gated sys bridge config.gate)
  private http : Std.Http.Server

private def toMethod? : Std.Http.Method → Option Method
  | .get => some .get
  | .head => some .head
  | .post => some .post
  | .put => some .put
  | .patch => some .patch
  | .delete => some .delete
  | .options => some .options
  | _ => none

/-- Header names or values that are not valid HTTP are left out. -/
private def respond (r : Response) : ContextAsync (Std.Http.Response Std.Http.Body.Any) := do
  let status := (Std.Http.Status.ofCode none r.status.toUInt16).getD .internalServerError
  let builder := r.headers.foldl (init := Std.Http.Response.new.status status) fun b (name, value) =>
    match Std.Http.Header.Name.ofString? name.toLower, Std.Http.Header.Value.ofString? value with
    | some name, some value => b.header name value
    | _, _ => b
  builder.fromBytes r.body

private def readRequest (maxBodyBytes : Nat) (req : Std.Http.Request Std.Http.Body.Stream) :
    ContextAsync (Option Request) := do
  let some method := toMethod? req.line.method | return none
  let query := req.line.uri.query.toArray.toList.filterMap fun (key, value) => do
    let key ← key.decode
    let value ← match value with
      | some value => value.decode
      | none => some ""
    return (key, value)
  let body : ByteArray ← req.body.readAll (maximumSize := some maxBodyBytes.toUInt64)
  return some {
    method
    path := req.line.uri.path.toDecodedSegments.toList
    query
    headers := req.line.headers.toList.map fun (name, value) => (name.value, value.value)
    body }

/-- Returns once the server is listening. Each request is answered exactly once by the gate. -/
def serve (sys : System σ) [Hashable σ.Id] (bridge : Bridge σ) (config : ServerConfig := {})
    (runtimeConfig : Runtime.Config := {}) : Async (Server sys bridge config) := do
  let some addr := Std.Net.IPv4Addr.ofString config.host
    | throw (IO.userError s!"lanes: {config.host} is not an IPv4 address")
  let waiting : Mutex (Std.HashMap ReqId (IO.Promise Response)) ← Mutex.new {}
  let nextId ← IO.mkRef (0 : Nat)
  let runtime ← Runtime.start (gated sys bridge config.gate) runtimeConfig fun (id, response) => do
    let waiter ← waiting.atomically do
      let waiter := (← get).get? id
      modify (·.erase id)
      return waiter
    if let some waiter := waiter then waiter.resolve response
  let handler := Std.Http.Server.Handler.ofFn fun req => do
    let some request ← readRequest config.maxBodyBytes req
      | respond (Response.text "method not allowed\n" 405)
    let id ← nextId.modifyGet fun n => (n, n + 1)
    let waiter ← IO.Promise.new
    waiting.atomically (modify (·.insert id waiter))
    if ← runtime.tryInput (id, request) then respond (← await waiter)
    else
      waiting.atomically (modify (·.erase id))
      respond busy
  let httpConfig : Std.Http.Config := { maxBodySize := config.maxBodyBytes }
  let http ← Std.Http.Server.serve (.v4 ⟨addr, config.port⟩) handler httpConfig
  return { runtime, http }

namespace Server

variable {sys : System σ} {bridge : Bridge σ} {config : ServerConfig} [Hashable σ.Id]

def port (server : Server sys bridge config) : Option UInt16 :=
  server.http.localAddr.map (·.port)

/-- Stop accepting connections and wait for the open ones to end. Requests in flight are
answered `503` by the underlying server. -/
def stop (server : Server sys bridge config) : Async Unit := do
  server.http.shutdownAndWait
  server.runtime.stop

def wait (server : Server sys bridge config) : Async Unit :=
  server.http.waitShutdown

end Server

end Lanes.Http
