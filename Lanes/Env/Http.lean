/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std.Http
public import Std.Data.HashMap
public import Lanes.Actors.Runtime
public import Lanes.Http.Basic

/-!
# The HTTP server adapter

Puts a running system behind an HTTP/1.1 server. Each request becomes one external input and is
answered by one output of the system:

1. the adapter reads and decodes the request into `Http.Request` (plain data),
2. `Bridge.decode` parses it into an input of the system, or answers directly (rule 2.2: raw
   input is parsed once, at the edge);
3. the input goes to the runtime;
4. when the system emits an output that `Bridge.encode` maps to this request, the adapter writes
   the response. A request that is not answered within the deadline gets `504`.

The environment model of this adapter: one input per request, at most one response per request,
and a response or a timeout always arrives.

TLS is not handled here. Terminate it in a reverse proxy.

## Main definitions

- `Http.Bridge`: how requests become inputs and outputs become responses.
- `Http.ServerConfig`: address and limits.
- `Http.serve`: start a system and its HTTP server.
-/

public section

namespace Lanes.Http

open Std Std.Async

variable {σ : Signature}

/-- Identifies one HTTP request for as long as it is being served. -/
abbrev ReqId := Nat

/-- How a system meets HTTP. Both functions are pure. -/
structure Bridge (σ : Signature) where
  /-- Parse a request into an input, or answer it directly without entering the system (for
  example `404` or `400`). The identifier must travel with the input so the matching output can
  name it. -/
  decode : ReqId → Request → Except Response σ.In
  /-- The request an output answers and the response to write, or `none` for an output that is
  not an HTTP response. -/
  encode : σ.Out → Option (ReqId × Response)

/-- Where the server listens and what it accepts. Every limit is explicit (rule 2.6). -/
structure ServerConfig where
  /-- The IPv4 address to bind. -/
  host : String := "127.0.0.1"
  /-- The port to bind. `0` picks a free port. -/
  port : UInt16 := 8080
  /-- A request the system has not answered after this long gets `504`. -/
  requestTimeout_ms : Nat := 30000
  /-- Larger request bodies are refused with `413`. -/
  maxBodyBytes : Nat := 1048576

/-- A system being served over HTTP. -/
structure Server (sys : System σ) [Hashable σ.Id] where
  /-- The running system. -/
  runtime : Runtime sys
  /-- The underlying HTTP server. -/
  http : Std.Http.Server

/-- Convert the method, or `none` for one applications do not handle. -/
private def toMethod? : Std.Http.Method → Option Method
  | .get => some .get
  | .head => some .head
  | .post => some .post
  | .put => some .put
  | .patch => some .patch
  | .delete => some .delete
  | .options => some .options
  | _ => none

/-- Write a response. Header names or values that are not valid HTTP are left out. -/
private def respond (r : Response) : ContextAsync (Std.Http.Response Std.Http.Body.Any) := do
  let status := (Std.Http.Status.ofCode none r.status.toUInt16).getD .internalServerError
  let builder := r.headers.foldl (init := Std.Http.Response.new.status status) fun b (name, value) =>
    match Std.Http.Header.Name.ofString? name.toLower, Std.Http.Header.Value.ofString? value with
    | some name, some value => b.header name value
    | _, _ => b
  builder.fromBytes r.body

/-- Read and decode a request. `none` if its method is not one applications handle. -/
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

/--
Start `sys` and serve it over HTTP. Returns once the server is listening; requests are handled in
the background until `Server.stop`.
-/
def serve (sys : System σ) [Hashable σ.Id] (bridge : Bridge σ) (config : ServerConfig := {})
    (runtimeConfig : Runtime.Config σ := {}) : Async (Server sys) := do
  let some addr := Std.Net.IPv4Addr.ofString config.host
    | throw (IO.userError s!"lanes: {config.host} is not an IPv4 address")
  let waiting : Mutex (Std.HashMap ReqId (Std.Channel Response)) ← Mutex.new {}
  let nextId ← IO.mkRef (0 : Nat)
  let runtime ← Runtime.start sys runtimeConfig fun out => do
    let some (id, response) := bridge.encode out | return
    let waiter ← waiting.atomically do
      let waiter := (← get).get? id
      modify (·.erase id)
      return waiter
    if let some waiter := waiter then
      discard <| waiter.trySend response
  let handler := Std.Http.Server.Handler.ofFn fun req => do
    let some request ← readRequest config.maxBodyBytes req
      | respond (Response.text "method not allowed\n" 405)
    let id ← nextId.modifyGet fun n => (n, n + 1)
    match bridge.decode id request with
    | .error response => respond response
    | .ok x =>
      let waiter : Std.Channel Response ← Std.Channel.new (some 1)
      waiting.atomically (modify (·.insert id waiter))
      runtime.input x
      let answer ← Selectable.one #[
        .case waiter.recvSelector (fun response => pure (some response)),
        .case (← Selector.sleep (.ofNat config.requestTimeout_ms)) (fun _ => pure none)]
      match answer with
      | some response => respond response
      | none =>
        waiting.atomically (modify (·.erase id))
        respond (Response.text "the system did not answer in time\n" 504)
  let httpConfig : Std.Http.Config := { maxBodySize := config.maxBodyBytes }
  let http ← Std.Http.Server.serve (.v4 ⟨addr, config.port⟩) handler httpConfig
  return { runtime, http }

namespace Server

variable {sys : System σ} [Hashable σ.Id]

/-- The port the server is listening on. -/
def port (server : Server sys) : Option UInt16 :=
  server.http.localAddr.map (·.port)

/-- Stop accepting connections and wait for the open ones to end. Requests in flight are
answered `503` by the underlying server. -/
def stop (server : Server sys) : Async Unit :=
  server.http.shutdownAndWait

/-- Wait until the server has been stopped. -/
def wait (server : Server sys) : Async Unit :=
  server.http.waitShutdown

end Server

end Lanes.Http
