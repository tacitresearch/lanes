/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std.Async
public import Lanes.Durable.IO.Journal
public import Lanes.Web.Http.Conn
public import Lanes.Web.Http.Front
public import Lanes.Web.Http.Waiting

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
  /-- How often deadlines are looked at: a connection is told one has passed up to this late. -/
  tick_ms : Nat := 25
  /-- Threads of the server's own that run the connections, each connection on one of them for
  its whole life, dealt in turn as they are accepted. With `0`, a connection's loop runs on
  whichever of Lean's task threads tells it something. Four by default: on the warm machine they
  serve 21–30% more requests a second than `0` for a quarter less CPU (`bench/README.md`). -/
  ioThreads : Nat := 4
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

/-- What a connection's loop is told. -/
private inductive Ev where
  | conn (e : Conn.Event)
  /-- The read the loop started has ended: bytes, the end of them, or an error. -/
  | read (r : Option (Except IO.Error (Option ByteArray)))
  /-- Look again: the connection has begun, or the write the loop waited for has ended. -/
  | resume
  /-- A deadline the loop gave may have passed. -/
  | alarm

/-- What the loop of a connection and those who tell it something share. The loop runs on the
thread that tells it something while it is not running, and never waits. -/
private structure Box where
  /-- Newest first. -/
  events : List Ev := []
  running : Bool := false
  /-- When to tell the loop `alarm`. -/
  alarm_ms : Option Nat := none

private abbrev ReadEnd := IO.Promise (Except IO.Error (Option ByteArray))
private abbrev WriteEnd := IO.Promise (Except IO.Error Unit)

/-- What only the running loop touches. -/
private structure Loop where
  conn : Conn
  /-- The read started that has not ended. One at a time. -/
  reading : Option ReadEnd := none
  /-- The last write and when it began. While it has not ended nothing is read, so that what
  waits to be written is bounded by what is in flight. -/
  writing : Option (WriteEnd × Nat) := none
  resumeSet : Bool := false
  left : Bool := false

/-- A thread of the server's own that runs the loops of the connections dealt to it, one after
another, and parks when none has anything to do. -/
private structure Lane where
  parker : Parker
  ready : Mutex (Array (BaseIO Unit))
  done : IO.Promise Unit

private def Lane.post (lane : Lane) (job : BaseIO Unit) : BaseIO Unit := do
  lane.ready.atomically (modify (·.push job))
  lane.parker.unpark

/-- Run what is posted until `down` is resolved. -/
private def Lane.run (lane : Lane) : BaseIO Unit := do
  repeat
    let jobs ← lane.ready.atomically (modifyGet fun jobs => (jobs, #[]))
    if jobs.isEmpty then
      if ← IO.hasFinished lane.done.result? then break
      lane.parker.park
    else
      for job in jobs do job

private structure Line where
  socket : TCP.Socket.Client
  box : Mutex Box
  loop : IO.Ref Loop
  ended : IO.Promise Unit
  /-- The thread this connection's loop runs on, if the server has threads of its own. -/
  lane : Option Lane := none

/-- What the server keeps of a connection. -/
private structure Open where
  line : Line
  tell : Ev → BaseIO Unit

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
  private lanes : Array Lane

/-- Everything written is sent before the end of the connection, and what the client still
sends is read and dropped for a while, so that its last response is not lost to a reset. The
read in progress, if any, is the first of those. -/
private def hangUp (socket : TCP.Socket.Client) (reading : Option ReadEnd) (linger_ms : Nat) :
    BaseIO Unit :=
  discard <| EAsync.toBaseIO (ε := IO.Error) do
    try socket.shutdown catch _ => pure ()
    let drain : Async Unit := do
      if let some r := reading then
        let some (.ok (some _)) ← await r.result? | return
      repeat
        let some _ ← socket.recv? 65536 | break
    try Async.race drain (Async.sleep (.ofNat linger_ms)) catch _ => pure ()
    socket.close

/-- How a connection's loop reaches the rest of the server. -/
private structure Ctx where
  config : ServerConfig
  /-- Hand a request to the system, with whom to tell its answer. -/
  submit : Request → (Response → BaseIO Unit) → BaseIO Unit
  /-- Forget the connection, which has closed. -/
  leave : BaseIO Unit

/-- Whether the last write has failed. One still going on has not. -/
private def failedWrite (loop : Loop) : BaseIO Bool := do
  let some (w, _) := loop.writing | return false
  if !(← IO.hasFinished w.result?) then return false
  return !(w.result?.get matches some (.ok ()))

/-- When the last write is to have ended, while it has not. -/
private def writeBy (write_ms : Nat) (loop : Loop) : BaseIO (Option Nat) := do
  let some (w, start) := loop.writing | return none
  return if ← IO.hasFinished w.result? then none else some (start + write_ms)

mutual

/-- Tell the connection's loop `ev`. If the loop is not running it runs now: on its lane if it
has one, else on this thread when `here`, else on a task of its own. -/
private partial def tell (ctx : Ctx) (line : Line) (here : Bool) (ev : Ev) : BaseIO Unit := do
  let start ← line.box.atomically do
    modifyGet fun b => (!b.running, { b with events := ev :: b.events, running := true })
  if start then
    match line.lane with
    | some lane => lane.post (run ctx line)
    | none => if here then run ctx line else discard <| BaseIO.asTask (run ctx line)

/-- Do what the connection asks after `event`. When a write fails, what the connection asks
after `broken` is done in place of the rest. -/
private partial def react (ctx : Ctx) (line : Line) (loop : Loop) (event : Conn.Event) :
    BaseIO Loop := do
  let config := ctx.config
  let event := if ← failedWrite loop then .broken else event
  let (conn, actions) := loop.conn.step config.conn (← IO.monoMsNow) event
  let mut loop := { loop with conn }
  let mut todo := actions
  repeat
    match todo with
    | [] => break
    | action :: rest =>
      todo := rest
      match action with
      | .submit seq request =>
        ctx.submit request fun r => tell ctx line false (.conn (.answered seq r))
      | .interim _ bytes | .write _ bytes =>
        let failed ← failedWrite loop
        let sent ← (line.socket.native.send #[bytes]).toBaseIO
        match failed, sent with
        | false, .ok w => loop := { loop with writing := some (w, ← IO.monoMsNow) }
        | _, _ =>
          let (broken, actions) := loop.conn.step config.conn (← IO.monoMsNow) .broken
          loop := { loop with conn := broken }
          todo := actions
      | .close => hangUp line.socket loop.reading config.linger_ms
  return loop

private partial def handle (ctx : Ctx) (line : Line) (loop : Loop) : Ev → BaseIO Loop
  | .conn e => react ctx line loop e
  | .read r =>
    react ctx line { loop with reading := none } <| match r with
      | some (.ok (some bytes)) => .received bytes
      | some (.ok none) => .ended
      | _ => .broken
  | .resume => return { loop with resumeSet := false }
  | .alarm => do
    let now ← IO.monoMsNow
    let late := (← writeBy ctx.config.write_ms loop).any (· ≤ now)
    react ctx line loop (if late then .broken else .tick)

/-- After the events: read if the connection wants bytes and the last write has ended, say when
to be told `alarm`, and once it has closed, leave. -/
private partial def settle (ctx : Ctx) (line : Line) (loop : Loop) : BaseIO Loop := do
  let config := ctx.config
  let conn := loop.conn
  if conn.closed then
    unless loop.left do
      ctx.leave
      line.ended.resolve ()
    line.box.atomically (modify fun b => { b with alarm_ms := none })
    return { loop with left := true }
  let mut loop := loop
  let writing ← writeBy config.write_ms loop
  if conn.wantsInput config.conn && loop.reading.isNone then
    if writing.isNone then
      let size := (min (conn.room config.conn) 65536).toUInt64
      match ← (line.socket.native.recv? size).toBaseIO with
      | .ok r =>
        loop := { loop with reading := some r }
        discard <| BaseIO.mapTask (t := r.result?) (sync := line.lane.isSome) fun res =>
          tell ctx line true (.read res)
      | .error e => tell ctx line true (.read (some (.error e)))
    else if !loop.resumeSet then
      if let some (w, _) := loop.writing then
        loop := { loop with resumeSet := true }
        discard <| BaseIO.mapTask (t := w.result?) (sync := line.lane.isSome) fun _ =>
          tell ctx line true .resume
  let alarm_ms := match conn.deadline config.conn, writing with
    | some a, some b => some (min a b)
    | a, b => a <|> b
  line.box.atomically (modify fun b => { b with alarm_ms })
  return loop

/-- Handle what the connection has been told, oldest first, until nothing more is. -/
private partial def run (ctx : Ctx) (line : Line) : BaseIO Unit := do
  repeat
    let taken ← line.box.atomically do
      modifyGet fun b =>
        if b.events.isEmpty then ([], { b with running := false })
        else (b.events, { b with events := [] })
    if taken.isEmpty then break
    let mut loop ← line.loop.get
    for ev in taken.reverse do loop ← handle ctx line loop ev
    loop ← settle ctx line loop
    line.loop.set loop

end

/-- The server is down, and its lanes end. -/
private def Server.finish {system : System τ} [Hashable τ.Id] (server : Server system) :
    BaseIO Unit := do
  server.down.resolve ()
  for lane in server.lanes do lane.parker.unpark

private def shutDown {system : System τ} [Hashable τ.Id] (server : Server system) :
    Async Unit := do
  try server.listener.close catch _ => pure ()
  let alive ← server.connections.atomically do
    modify fun c => { c with count.stopping := true }
    return (← get).alive.toList
  for (_, c) in alive do c.tell (.conn .stop)

private def awaitConnections {system : System τ} [Hashable τ.Id] (server : Server system) :
    Async Unit := do
  for (_, c) in ← server.connections.atomically (return (← get).alive.toList) do
    discard <| await c.line.ended.result?

/-- Every `tick_ms`, tell each connection whose alarm has passed, until the server is down. -/
private def ticker {system : System τ} [Hashable τ.Id] (server : Server system) (tick_ms : Nat) :
    IO Unit := do
  repeat
    IO.sleep (max 1 tick_ms).toUInt32
    if ← IO.hasFinished server.down.result? then break
    let now ← IO.monoMsNow
    for (_, c) in ← server.connections.atomically (return (← get).alive.toList) do
      if let some t ← c.line.box.atomically (return (← get).alarm_ms) then
        if t ≤ now then c.tell .alarm

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
  let down ← IO.Promise.new
  let lanes ← (List.range config.ioThreads).toArray.mapM fun _ => do
    let lane : Lane := { parker := ← Parker.new, ready := ← Mutex.new #[], done := down }
    discard <| IO.asTask (prio := .dedicated) lane.run
    return lane
  let server : Server system := {
    runtime, listener, waiting, connections := ← Mutex.new {}, down
    localPort := (← listener.getSockName).port, lanes }
  let submit (request : Request) (answer : Response → BaseIO Unit) : BaseIO Unit := do
    let request := prepare request
    let admitted ← waiting.atomically do
      let id ← modifyGet (·.wait answer)
      if ← runtime.tryInput (enter (id, request)) then return true
      modify (·.release id)
      return false
    unless admitted do answer busy
  let adopt (socket : TCP.Socket.Client) : Async Unit := do
    try socket.noDelay catch _ => pure ()
    let next ← server.connections.atomically (return (← get).next)
    let line : Line := {
      socket, box := ← Mutex.new {}, loop := ← IO.mkRef { conn := { since_ms := ← IO.monoMsNow } }
      ended := ← IO.Promise.new, lane := server.lanes[next % max 1 server.lanes.size]? }
    let admitted ← server.connections.atomically do
      let c ← get
      let (admitted, count) := c.count.admit config.connections_max
      if !admitted then return none
      let id := c.next
      let ctx : Ctx := {
        config, submit
        leave := server.connections.atomically do
          modify fun c => { c with count := c.count.leave, alive := c.alive.erase id } }
      set { c with count, alive := c.alive.insert id { line, tell := tell ctx line false },
                   next := c.next + 1 }
      return some ctx
    match admitted with
    | none => socket.close
    | some ctx => tell ctx line false .resume
  discard <| IO.asTask (prio := .dedicated) (ticker server config.tick_ms)
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
      server.finish
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
  server.finish

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
