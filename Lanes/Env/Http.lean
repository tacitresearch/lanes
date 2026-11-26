/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std.Async
public import Lanes.Env.Journal
public import Lanes.Http.Conn
public import Lanes.Http.Front
public import Lanes.Http.Waiting

/-!
The HTTP server adapter: the IO around the gate and the connections. It accepts connections on
`Std.Net`, tells each one's `Conn` what happened and does what it answers: it reads the socket
when the connection wants bytes, hands each request it reads to a system that has the gate in
it, writes the responses it is given and closes. A request is prepared as the bridge says
(`Bridge.prepare`) and given an id no other request has before it enters the system. What the
bytes are as requests, in what order responses go out, when to answer `100 Continue`, when a
client has taken too long and when to close are `Conn.step`'s decisions; which requests are
waiting, when one times out and when the system is too busy are the gate's. Neither is this
file's.

There is one loop, `serveOn`, for both systems with a gate: `served sys`, whose only outputs are
responses (`serve`, `serveWith`), and `fronted sys`, which also puts out what is no response and
takes inputs that are no request (`serveFronted`).

One refusal is made here: `503` when the shard's inbox is full. TLS is not handled: terminate it
in a reverse proxy.
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
  /-- The other limits of a request; its `body_max` is `maxBodyBytes`. -/
  limits : Request.Limits := {}
  /-- Requests read from one connection whose responses are not yet written. -/
  inflight_max : Nat := 16
  /-- Connections open at once. One more is closed as soon as it is accepted. -/
  connections_max : Nat := 1024
  /-- How long a connection with nothing in flight is kept open for the next request. -/
  idle_ms : Nat := 10000
  head_ms : Nat := 10000
  body_ms : Nat := 30000
  /-- A response that the client has not taken in this long ends the connection. -/
  write_ms : Nat := 30000
  /-- How long what the client still sends is read and dropped before the socket is closed, so
  that the client reads the last response rather than a reset. -/
  linger_ms : Nat := 2000
  gate : GateConfig := {}
  /-- Where to keep a journal. With one, the system behind the server survives the process:
  it starts in the state it was in (`docs/decisions/` D24). -/
  journal : Option System.FilePath := none
  /-- The application's name for the system and the version of its step functions. A journal
  written under another name is refused: replayed through other step functions it would give
  another state. -/
  system : String := ""

private def ServerConfig.conn (config : ServerConfig) : Conn.Config where
  limits := { config.limits with body_max := config.maxBodyBytes }
  inflight_max := config.inflight_max
  idle_ms := config.idle_ms
  head_ms := config.head_ms
  body_ms := config.body_ms

/-- What the server keeps of a connection: where to tell it of an answer or of `stop`, and how
to know it has ended. -/
private structure Open where
  inbox : CloseableChannel Conn.Event
  ended : IO.Promise Unit

private structure Connections where
  count : Conn.Count := {}
  alive : Std.HashMap Nat Open := {}
  next : Nat := 0

/-- The runtime is private because the gate answers each request once only if request ids are
never reused, and the server is what allocates them. -/
structure Server (system : System τ) [Hashable τ.Id] where
  private mk ::
  private runtime : Runtime system
  private listener : TCP.Socket.Server
  private waiting : Mutex (Waiting (Response → BaseIO Unit))
  private connections : Mutex Connections
  private down : IO.Promise Unit
  private localPort : UInt16

/-- Whether the bytes were written within `write_ms`. A write that is done at once is not
raced, so that the usual one costs no timer. -/
private def write (socket : TCP.Socket.Client) (write_ms : Nat) (bytes : ByteArray) :
    Async Bool := do
  try
    let promise ← socket.native.send #[bytes]
    if ← IO.hasFinished promise.result? then
      return promise.result?.get matches some (.ok ())
    Async.race ((fun _ => true) <$> Async.ofPromise (pure promise))
      ((fun _ => false) <$> Async.sleep (.ofNat write_ms))
  catch _ => return false

/-- Everything written is sent before the end of the connection, and what the client still
sends is read and dropped for a while, so that its last response is not lost to a reset. -/
private def hangUp (socket : TCP.Socket.Client) (linger_ms : Nat) : Async Unit := do
  try socket.shutdown catch _ => pure ()
  background do
    let drain : Async Unit := do
      repeat
        let some _ ← socket.recv? 65536 | break
    try Async.race drain (Async.sleep (.ofNat linger_ms)) catch _ => pure ()
    socket.close

/-- Do what the connection asks after `event`. When a write fails, what the connection asks
after `broken` is done in place of the rest. -/
private def react (config : ServerConfig) (socket : TCP.Socket.Client)
    (submit : Nat → Request → Async Unit) (conn : Conn) (event : Conn.Event) : Async Conn := do
  let (conn, actions) := conn.step config.conn (← IO.monoMsNow) event
  let mut conn := conn
  let mut todo := actions
  repeat
    match todo with
    | [] => break
    | action :: rest =>
      todo := rest
      match action with
      | .submit seq request => submit seq request
      | .interim _ bytes | .write _ bytes =>
        unless ← write socket config.write_ms bytes do
          let (broken, actions) := conn.step config.conn (← IO.monoMsNow) .broken
          conn := broken
          todo := actions
      | .close => hangUp socket config.linger_ms
  return conn

/-- One connection: wait for what the connection waits for, and tell it what happened. -/
private def converse (config : ServerConfig) (socket : TCP.Socket.Client)
    (inbox : CloseableChannel Conn.Event) (submit : Nat → Request → Async Unit) : Async Unit := do
  let mut conn : Conn := { since_ms := ← IO.monoMsNow }
  repeat
    if conn.closed then break
    let mut cases : Array (Selectable Conn.Event) :=
      #[.case inbox.recvSelector fun event => pure (event.getD .stop)]
    if conn.wantsInput config.conn then
      let size := (min (conn.room config.conn) 65536).toUInt64
      cases := cases.push (.case (socket.recvSelector size) fun
        | some bytes => pure (.received bytes)
        | none => pure .ended)
    if let some t := conn.deadline config.conn then
      let left := t - (← IO.monoMsNow)
      cases := cases.push (.case (← Selector.sleep (.ofNat (max 1 left))) fun _ => pure .tick)
    let event ← try Selectable.one cases catch _ => pure .broken
    conn ← react config socket submit conn event

private def shutDown {system : System τ} [Hashable τ.Id] (server : Server system) :
    Async Unit := do
  try server.listener.close catch _ => pure ()
  let alive ← server.connections.atomically do
    modify fun c => { c with count.stopping := true }
    return (← get).alive.toList
  for (_, c) in alive do discard <| c.inbox.trySend .stop

private def awaitConnections {system : System τ} [Hashable τ.Id] (server : Server system) :
    Async Unit := do
  for (_, c) in ← server.connections.atomically (return (← get).alive.toList) do
    discard <| await c.ended.result?

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
    (prepare : Request → Request) (enter : ReqId × Request → τ.In)
    (onOutput : τ.Out → (ReqId × Response) ⊕ Async Unit) :
    Async (Server system) := do
  let some addr := Std.Net.IPv4Addr.ofString config.host
    | throw (IO.userError s!"lanes: {config.host} is not an IPv4 address")
  let waiting ← Mutex.new (Waiting.start ((log.map (·.index)).getD 0))
  let runtime ← Runtime.start system runtimeConfig (journal := log) fun out => do
    match onOutput out with
    | .inr other => other
    | .inl (id, response) =>
      if let some waiter := (← waiting.atomically (modifyGet (·.answer id))) then
        waiter response
  let listener ← try
      let listener ← TCP.Socket.Server.mk
      listener.bind (.v4 ⟨addr, config.port⟩)
      listener.listen 1024
      pure listener
    catch e =>
      runtime.stop
      throw e
  try listener.noDelay catch _ => pure ()
  let server : Server system := {
    runtime, listener, waiting, connections := ← Mutex.new {}, down := ← IO.Promise.new
    localPort := (← listener.getSockName).port }
  let submit (inbox : CloseableChannel Conn.Event) (seq : Nat) (request : Request) :
      Async Unit := do
    let request := prepare request
    let answer : Response → BaseIO Unit := fun r => discard <| inbox.trySend (.answered seq r)
    let admitted ← waiting.atomically do
      let id ← modifyGet (·.wait answer)
      if ← runtime.tryInput (enter (id, request)) then return true
      modify (·.release id)
      return false
    unless admitted do answer busy
  let adopt (socket : TCP.Socket.Client) : Async Unit := do
    let inbox ← CloseableChannel.new
    let ended ← IO.Promise.new
    let admitted ← server.connections.atomically do
      let c ← get
      let (admitted, count) := c.count.admit config.connections_max
      if admitted then set { c with count, alive := c.alive.insert c.next { inbox, ended }, next := c.next + 1 }
      return if admitted then some c.next else none
    match admitted with
    | none => socket.close
    | some id =>
      try socket.noDelay catch _ => pure ()
      background do
        try converse config socket inbox (submit inbox) catch _ => socket.close
        server.connections.atomically do
          modify fun c => { c with count := c.count.leave, alive := c.alive.erase id }
        discard <| (inbox.close : EIO _ Unit).toBaseIO
        ended.resolve ()
  background do
    repeat
      match ← (try some <$> listener.accept catch _ => pure none) with
      | some socket => adopt socket
      | none =>
        if (← server.connections.atomically (return (← get).count.stopping)) then break
        Async.sleep 50
  background do
    if (← runtime.ended).isSome then
      for (_, waiter) in ← waiting.atomically (modifyGet Waiting.drain) do waiter busy
      shutDown server
      awaitConnections server
      server.down.resolve ()
  return server

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
step function reads. A journal of another gate, or of the gate `serve` ran when the gate was an
actor of the system behind it, is refused. -/
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
  some server.localPort

/-- Stop accepting connections and stop the shard; requests in flight are answered `503`.
Returns once every connection has written what it owes and closed. -/
def stop (server : Server system) : Async Unit := do
  shutDown server
  server.runtime.stop
  for (_, waiter) in ← server.waiting.atomically (modifyGet Waiting.drain) do waiter busy
  awaitConnections server
  server.down.resolve ()

/-- The requests the shard has taken and the server has not yet answered. -/
def inFlight (server : Server system) : BaseIO Nat :=
  server.waiting.atomically (return (← get).waiters.size)

/-- The events performed, if the runtime was started with `record`. For conformance tests. -/
def trace (server : Server system) : BaseIO (Array (Event τ)) :=
  server.runtime.trace

/-- Returns when the server has shut down, and throws if the shard ended on an error, so that a
`main` that waits here exits with a failure and can be started again. -/
def wait (server : Server system) : Async Unit := do
  discard <| await server.down.result?
  if let some e ← server.runtime.ended then throw e

/-- Hand the system behind the gate an input that is not a request, such as a parcel from
another process. `false` if the shard's inbox is full. A request cannot be handed in this way,
so request ids stay the server's. -/
def tryInput {sys : System σ} [Hashable σ.Id] {bridge : Bridge σ} {gate : GateConfig}
    (server : Server (fronted sys bridge gate)) (x : σ.In) : Async Bool :=
  server.runtime.tryInput (.inr x)

end Server

end Lanes.Http
