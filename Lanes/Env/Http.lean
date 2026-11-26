/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std.Http
public import Lanes.Env.Journal
public import Lanes.Http.Front
public import Lanes.Http.Waiting

/-!
The HTTP server adapter: the IO around the gate. It reads a request, prepares it as the bridge
says (`Bridge.prepare`), gives it an id no other request has, hands it as an input to a system
that has the gate in it, and writes the one response the gate gives for it. Which requests are waiting, when one times out and when the
system is too busy are the gate's decisions, not this file's.

There is one loop, `serveOn`, for both systems with a gate: `served sys`, whose only outputs are
responses (`serve`, `serveWith`), and `fronted sys`, which also puts out what is no response and
takes inputs that are no request (`serveFronted`).

Two refusals are made here: `405` for a method an application cannot handle, and `503` when the
shard's inbox is full. TLS is not handled: terminate it in a reverse proxy.
-/

public section

namespace Lanes.Http

open Std Std.Async

variable {σ τ : Signature}

/-- Every limit is explicit (rule 2.6). -/
structure ServerConfig where
  /-- The IPv4 address to bind. -/
  host : String := "127.0.0.1"
  /-- `0` picks a free port. -/
  port : UInt16 := 8080
  /-- Larger request bodies are refused with `413`. -/
  maxBodyBytes : Nat := 1048576
  gate : GateConfig := {}
  /-- Where to keep a journal. With one, the system behind the server survives the process:
  it starts in the state it was in (`DECISIONS.md` D24). -/
  journal : Option System.FilePath := none
  /-- The application's name for the system and the version of its step functions. A journal
  written under another name is refused: replayed through other step functions it would give
  another state. -/
  system : String := ""

/-- The runtime is private because the gate answers each request once only if request ids are
never reused, and the server is what allocates them. -/
structure Server (system : System τ) [Hashable τ.Id] where
  private mk ::
  private runtime : Runtime system
  private http : Std.Http.Server
  private waiting : Mutex (Waiting (IO.Promise Response))

/-- `HEAD` is handled as `GET`; its response is sent without the body. -/
private def toMethod? : Std.Http.Method → Option Method
  | .get | .head => some .get
  | .post => some .post
  | .put => some .put
  | .patch => some .patch
  | .delete => some .delete
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

/--
The server's loop, for any system with a gate in it: `enter` is how a request enters
`system`, and `onOutput` says of each output whether it is the gate's response to one or
something else to do. A shard that ends on an error takes the server down with it: requests in
flight are answered `503`, and `Server.wait` throws.

Which id a request gets, who waits on it and who is answered is `Waiting`, pure and proved: ids
are handed out in order from the start it is given, never twice, and a request the shard does
not take gives its id back. Here the start is the number of entries in the shard's history.
Every request that leaves a trace in the system has an entry of its own, so the history at the
next start is longer than the last such id, and ids stay fresh across restarts and after the
journal is cut.
-/
private def serveOn (system : System τ) [Hashable τ.Id] (config : ServerConfig)
    (runtimeConfig : Runtime.Config) (log : Option (Journal.Log system))
    (prepare : Request → Request) (enter : ReqId × Request → τ.In) (onOutput : τ.Out → (ReqId × Response) ⊕ Async Unit) :
    Async (Server system) := do
  let some addr := Std.Net.IPv4Addr.ofString config.host
    | throw (IO.userError s!"lanes: {config.host} is not an IPv4 address")
  let waiting ← Mutex.new (Waiting.start ((log.map (·.index)).getD 0))
  let runtime ← Runtime.start system runtimeConfig (journal := log) fun out => do
    match onOutput out with
    | .inr other => other
    | .inl (id, response) =>
      if let some waiter := (← waiting.atomically (modifyGet (·.answer id))) then
        waiter.resolve response
  let handler := Std.Http.Server.Handler.ofFn fun req => do
    let some request ← readRequest config.maxBodyBytes req
      | respond (Response.text "method not allowed\n" 405)
    let request := prepare request
    let headOnly := req.line.method == .head
    let send := fun (r : Response) => respond (if headOnly then { r with body := .empty } else r)
    let waiter ← IO.Promise.new
    let admitted ← waiting.atomically do
      let id ← modifyGet (·.wait waiter)
      if ← runtime.tryInput (enter (id, request)) then return true
      modify (·.release id)
      return false
    if admitted then send ((← await waiter.result?).getD busy) else send busy
  let httpConfig : Std.Http.Config := { maxBodySize := config.maxBodyBytes }
  let http ← try Std.Http.Server.serve (.v4 ⟨addr, config.port⟩) handler httpConfig
    catch e =>
      runtime.stop
      throw e
  background do
    if (← runtime.ended).isSome then
      for (_, waiter) in ← waiting.atomically (modifyGet Waiting.drain) do waiter.resolve busy
      http.shutdown
  return { runtime, http, waiting }

/-- `serve` on a journal that is already open. -/
def serveWith (sys : System σ) [Hashable σ.Id] (bridge : Bridge σ) (config : ServerConfig := {})
    (runtimeConfig : Runtime.Config := {})
    (log : Option (Journal.Log (served sys bridge config.gate))) :
    Async (Server (served sys bridge config.gate)) :=
  serveOn (served sys bridge config.gate) config runtimeConfig log bridge.prepare id .inl

/-- Serve `sys` behind a gate it shares the process with other things: an output of `sys` that
the bridge does not read as a response comes to `onOutput`, and `Server.tryInput` hands `sys`
an input that is no request. `config.journal` is not used: open `log` yourself. -/
def serveFronted (sys : System σ) [Hashable σ.Id] (bridge : Bridge σ) (config : ServerConfig := {})
    (runtimeConfig : Runtime.Config := {}) (onOutput : σ.Out → Async Unit := fun _ => pure ())
    (log : Option (Journal.Log (fronted sys bridge config.gate)) := none) :
    Async (Server (fronted sys bridge config.gate)) :=
  serveOn (fronted sys bridge config.gate) config runtimeConfig log bridge.prepare .inl
    (Sum.map id onOutput)

/-- What `serve` needs to save the kernel and cut the journal: how the system's actors and its
outputs are written. -/
structure Saving (sys : System σ) where
  actors : Kernel.Image.Codecs sys
  out : Codec σ.Out

/-- The name `serve` writes in its journal: the application's, and the configuration the gate's
step function reads. A journal of another gate, or of the gate `serve` ran before D42, is
refused. -/
def ServerConfig.journalName (config : ServerConfig) : String :=
  s!"{config.system}, behind a gate of {config.gate.requestTimeout_ms} ms and "
    ++ s!"{config.gate.maxPending} requests"

/-- Returns once the server is listening. Each request is answered exactly once by the gate.
With a journal and `saving`, the kernel is saved from time to time and the journal cut
(`Runtime.Config.snapshotEvery`); with a journal alone, the journal only grows. -/
def serve (sys : System σ) [Hashable σ.Id] (bridge : Bridge σ) (config : ServerConfig := {})
    (runtimeConfig : Runtime.Config := {}) (saving : Option (Saving sys) := none) :
    Async (Server (served sys bridge config.gate)) := do
  let log ← config.journal.mapM fun path =>
    Journal.Store.open (sys := served sys bridge config.gate)
      { path, input := Codec.pair Codec.nat Request.codec, system := config.journalName
        actors := saving.map fun s => servedActors s.actors s.out bridge config.gate }
  try serveWith sys bridge config runtimeConfig log
  catch e =>
    if let some log := log then discard log.close.toBaseIO
    throw e

namespace Server

variable {system : System τ} [Hashable τ.Id]

def port (server : Server system) : Option UInt16 :=
  server.http.localAddr.map (·.port)

/-- Stop accepting connections, wait for the open ones to end, and stop the shard. Requests in
flight are answered `503` by the underlying server. -/
def stop (server : Server system) : Async Unit := do
  server.http.shutdownAndWait
  server.runtime.stop
  for (_, waiter) in ← server.waiting.atomically (modifyGet Waiting.drain) do waiter.resolve busy

/-- The requests the shard has taken and the server has not yet answered. -/
def inFlight (server : Server system) : BaseIO Nat :=
  server.waiting.atomically (return (← get).waiters.size)

/-- The events performed, if the runtime was started with `record`. For conformance tests. -/
def trace (server : Server system) : BaseIO (Array (Event τ)) :=
  server.runtime.trace

/-- Returns when the server has shut down, and throws if the shard ended on an error, so that a
`main` that waits here exits with a failure and can be started again. -/
def wait (server : Server system) : Async Unit := do
  server.http.waitShutdown
  if let some e ← server.runtime.ended then throw e

/-- Hand the system behind the gate an input that is not a request, such as a parcel from
another process. `false` if the shard's inbox is full. A request cannot be handed in this way,
so request ids stay the server's. -/
def tryInput {sys : System σ} [Hashable σ.Id] {bridge : Bridge σ} {gate : GateConfig}
    (server : Server (fronted sys bridge gate)) (x : σ.In) : Async Bool :=
  server.runtime.tryInput (.inr x)

end Server

end Lanes.Http
