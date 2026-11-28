/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std.Async
public import Lanes.Web.Http.Admit
public import Lanes.Web.Http.Compress
public import Lanes.Web.Http.Conn
public import Lanes.Web.Http.View
public import Lanes.Web.Http.Waiting
public import Lanes.Web.IO.Ops
public import Lanes.Web.Http.Shutdown
public import Lanes.Runtime.IO.Signal

/-!
The HTTP server adapter: the IO around the gate and the connections. It accepts connections on
`Std.Net`, tells each one's `Conn` what happened and does what it answers: it reads the socket
when the connection wants bytes, puts each request it reads before the gate, hands the shard
what the gate admits, writes the responses it is given and closes. A request is prepared as the
bridge says (`Bridge.prepare`) and given an id no other request has before the gate sees it;
before that, work it needs in IO is done by `arrive`, if it is given, on a task of its own.
What the bytes are as requests, in what order responses go out, when to answer `100 Continue`,
when a client has taken too long and when to close are `Conn.step`'s decisions; which requests
are waiting, when one times out and when the system is too busy are the gate's (`Gate.step`).
Neither is this file's.

The gate is not an actor of the shard (`docs/decisions/D96-runtime-contract.md`): its decisions
are made here, under the lock of the table of waiting requests, on the thread of the request,
the shard's answer or the ticker. The shard runs `admitted sys` (`serve`, `serveWith`) or
`admittedFronted sys`, which also takes inputs that are no request and puts out what is no
response (`serveFronted`); both are `sys` with no actor that every request goes through. What
is trusted is that this file does what `Gate.step` returns, as `Lanes/Web/Http/AdmitSound.lean`
models it.

A request the application's `view` names is a read (`Http.View`): it never enters the system.
It waits behind a gate of its own (`readBridge`, bounded by `ServerConfig.reads`) for a peek of
the actors it reads, each between two of its steps (`Runtime.tryPeek`), and is answered from
their states off the workers' threads, or `504` at its deadline. It takes an id from the same
table as every request.

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
  /-- Requests whose `arrive` runs at once, each on a thread of its own; one more is answered
  `503` before its work begins. -/
  arriving_max : Nat := 64
  /-- How long a connection with nothing in flight is kept open for the next request. -/
  idle_ms : Nat := 10000
  head_ms : Nat := 10000
  body_ms : Nat := 30000
  /-- Which requests stream, by their head (`Conn.Config.streams`): the body is handed to the
  system in pieces, and the answer may open a response whose parts the system gives one at a
  time. -/
  streams : Option (Request → Bool) := none
  piece_max : Nat := 65536
  streamBody_max : Nat := 1099511627776
  part_max : Nat := 1048576
  poll_ms : Nat := 1000
  heartbeat_ms : Nat := 15000
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
  /-- The gate's bounds. -/
  gate : GateConfig := {}
  /-- The bounds of the reads, the requests a view answers from the state: how long one waits for
  the shard's peek before it is answered `504`, and how many may wait at once. -/
  reads : GateConfig := {}
  /-- Metrics, health and the access log, answered and written by the server: all off by
  default (`Lanes/Web/IO/Ops.lean`). -/
  ops : OpsConfig := {}
  /-- Responses compressed with gzip for clients that take it, on the connection's thread
  (`Lanes/Web/Http/Compress.lean`). Off by default: see BREACH there. -/
  compression : Option Compression := none

private def ServerConfig.conn (config : ServerConfig) : Conn.Config where
  limits := { config.limits with body_max := config.maxBodyBytes }
  inflight_max := config.inflight_max
  idle_ms := config.idle_ms
  head_ms := config.head_ms
  body_ms := config.body_ms
  streams := config.streams
  piece_max := config.piece_max
  streamBody_max := config.streamBody_max
  part_max := config.part_max
  poll_ms := config.poll_ms
  heartbeat_ms := config.heartbeat_ms

/-- What a connection's loop is told. -/
private inductive Ev where
  | conn (e : Conn.Event)
  /-- The read the loop started has ended: bytes, the end of them, or an error. -/
  | read (r : Option (Except IO.Error (Option ByteArray)))
  /-- Look again: the connection has begun, or the write the loop waited for has ended. -/
  | resume
  /-- A deadline the loop gave may have passed. -/
  | alarm
  /-- The write the loop waited for to tell the connection it was sent has ended. -/
  | sent
  /-- The answer to a request, to be compressed as its `Accept-Encoding` allows before the
  connection is told it. -/
  | answer (seq : Nat) (acceptEncoding : Option String) (r : Response)

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
  /-- The ids the heads of the requests that stream entered the system with, by number. -/
  heads : List (Nat × ReqId) := []
  /-- The connection will be told `sent` when the last write ends. -/
  sentSet : Bool := false
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

/-- The server's front: who waits on which id, and the gate's state, the requests waiting for
the system (`Gate.step`) with when each is due. -/
private structure Desk where
  waiting : Waiting (Response → BaseIO Unit)
  pending : List ReqId := []
  /-- The reads waiting for their peek: the state of their gate. -/
  reads : List ReqId := []
  deadlines : Std.HashMap ReqId Nat := {}

/-- What the lock's cell holds while its desk is out of it. -/
private def Desk.hole : Desk := { waiting := Waiting.start 0 }

/-- Do what the gate decided, but pass nothing on: arm and disarm deadlines, and take the
waiters of the requests it answers, with their answers. -/
private def Desk.apply {σ : Signature} (d : Desk) (due_ms : Nat) :
    List (Gate.Act σ) → Desk × List (BaseIO Unit)
  | [] => (d, [])
  | act :: acts =>
    let (d, now) : Desk × List (BaseIO Unit) := match act with
      | .respond id response =>
        let (waiter, waiting) := d.waiting.answer id
        ({ d with waiting }, (waiter.map (· response)).toList)
      | .forward _ => (d, [])
      | .arm id => ({ d with deadlines := d.deadlines.insert id due_ms }, [])
      | .disarm id => ({ d with deadlines := d.deadlines.erase id }, [])
    let (d, later) := d.apply due_ms acts
    (d, now ++ later)

/-- The runtime is private because the gate answers each request once only if request ids are
never reused, and the server is what allocates them. -/
structure Server (system : System τ) [Hashable τ.Id] where
  private mk ::
  private runtime : Runtime system
  private listener : TCP.Socket.Server
  private desk : Mutex Desk
  private connections : Mutex Connections
  private down : IO.Promise Unit
  private localPort : UInt16
  private lanes : Array Lane
  private ops : Ops

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
  /-- Hand a request that streams, or a piece or a pull of one, to the system, with whom to tell
  its answer; the id it entered with, unless the system was too busy to take it. These pass by
  the operations front (`Ops.front`), whose answers are whole. -/
  submitStream : Request → (Response → BaseIO Unit) → BaseIO (Option ReqId)
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
        let accept := request.header? "accept-encoding"
        ctx.submit request fun r => tell ctx line false (.answer seq accept r)
      | .begin seq request =>
        let id ← ctx.submitStream request fun r => tell ctx line false (.conn (.responded seq r))
        let heads := loop.heads.filter (·.1 ≥ loop.conn.written)
        loop := { loop with heads := match id with
          | some id => (seq, id) :: heads
          | none => heads }
      | .piece seq index request =>
        let reply := fun r => tell ctx line false (.conn (.took seq index r))
        match loop.heads.lookup seq with
        | some id => discard <| ctx.submitStream (Stream.tag request id) reply
        | none => reply (.text "the request is not with the system\n" 400)
      | .pull seq index request =>
        let reply := fun r => tell ctx line false (.conn (.pulled seq index r))
        match loop.heads.lookup seq with
        | some id => discard <| ctx.submitStream (Stream.tag request id) reply
        | none => reply (.text "the request is not with the system\n" 400)
      | .interim _ bytes | .write _ bytes | .part _ bytes =>
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
  | .sent => react ctx line { loop with sentSet := false } .sent
  | .answer seq accept r =>
    react ctx line loop (.answered seq (match ctx.config.compression with
      | some c => c.respond accept r
      | none => r))
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
  if conn.unsent && !loop.sentSet then
    loop := { loop with sentSet := true }
    match loop.writing, writing with
    | some (w, _), some _ =>
      discard <| BaseIO.mapTask (t := w.result?) (sync := line.lane.isSome) fun _ =>
        tell ctx line true .sent
    | _, _ => tell ctx line true .sent
  let alarm_ms := Conn.earlier (Conn.earlier (conn.deadline config.conn) writing)
    (conn.wakeAt config.conn)
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

/-- The address a connection comes from, if the socket tells it. -/
private def peerOf (socket : TCP.Socket.Client) : BaseIO (Option Ip.Addr) := do
  match ← socket.getPeerName.toBaseIO with
  | .ok (.v4 a) => return some (.v4 (.ofNat _ (a.addr.octets.foldl (· * 256 + ·.toNat) 0)))
  | .ok (.v6 a) => return some (.v6 (.ofNat _ (a.addr.segments.foldl (· * 65536 + ·.toNat) 0)))
  | .error _ => return none

/-- Every `tick_ms`, pass the deadlines that have passed to the gate, and tell each connection
whose alarm has passed, until the server is down. -/
private def ticker {system : System τ} [Hashable τ.Id] (server : Server system) (tick_ms : Nat)
    (expire : Nat → BaseIO Unit) : IO Unit := do
  repeat
    IO.sleep (max 1 tick_ms).toUInt32
    if ← IO.hasFinished server.down.result? then break
    let now ← IO.monoMsNow
    expire now
    for (_, c) in ← server.connections.atomically (return (← get).alive.toList) do
      if let some t ← c.line.box.atomically (return (← get).alarm_ms) then
        if t ≤ now then c.tell .alarm

/--
The server's loop, for any shard behind the gate: `enter` is how a request the gate admitted
enters `system`, and `onOutput` says of each output whether it is a response, which the gate
reads (`Gate.step`'s `answer`), or something else to do. A shard that ends on an error takes
the server down with it: requests in flight are answered `503`, and `Server.wait` throws.

Which id a request gets, who waits on it and who is answered is `Waiting`, pure and proved: ids
are handed out in order from 0, never twice in one process. A restart starts the system afresh
too, so no id it holds is from before.

An arrival takes the table's lock once: it is given its id, decoded, and the gate decides
(`Gate.admit`); an admitted request is handed to the shard under the same lock, so that a refusal
by the shard's inbox (`503`) leaves the gate's state as it was. `decode` runs under the lock, as
it ran on the shard's one thread when the gate was an actor; taking it out would cost a second
lock an arrival. An answer is encoded on the shard's thread and read by the gate
under the lock (`Gate.receive`); deadlines are looked at by the ticker.

A read takes the lock as an arrival does, and its gate admits it (`Gate.admit` over `readSig`);
the peek is asked under the lock, so that a refusal by the inbox leaves that gate as it was. The
view's response is made on the task the peek's answer runs on, and read by the gate under the lock
(`Gate.receive`).
-/
private def serveOn (system : System τ) [Hashable τ.Id] (bridge : Bridge σ) (config : ServerConfig)
    (runtimeConfig : Runtime.Config)
    (enter : ReqId × Request → τ.In) (output : τ.Out → σ.Out)
    (other : σ.Out → Async Unit)
    (arrive : Option (Request → IO (Except Response Request)))
    (view : Request → Option (View system)) :
    Async (Server system) := do
  let some addr := Std.Net.IPv4Addr.ofString config.host
    | throw (IO.userError s!"lanes: {config.host} is not an IPv4 address")
  let ops ← Ops.new config.ops
  let gate := config.gate
  let desk ← Mutex.new ({ waiting := Waiting.start 0 } : Desk)
  /- Do what the gate decides on `msg`, but pass nothing on; answer whom it answers. -/
  let decide (now : Nat) (msg : Desk → List ReqId × List (Gate.Act σ)) : BaseIO Unit := do
    let calls ← desk.atomically (modifyGet fun d =>
      let (pending, acts) := msg d
      let (d, calls) := Desk.apply { d with pending } (now + gate.requestTimeout_ms) acts
      (calls, d))
    for call in calls do call
  /- The same, for the gate of reads. -/
  let decideRead (now : Nat) (msg : List ReqId → List ReqId × List (Gate.Act readSig)) :
      BaseIO Unit := do
    let calls ← desk.atomically (modifyGet fun d =>
      let (reads, acts) := msg d.reads
      let (d, calls) := Desk.apply { d with reads } (now + config.reads.requestTimeout_ms) acts
      (calls, d))
    for call in calls do call
  let runtime ← Runtime.startWith system runtimeConfig fun _ out => do
    let out := output out
    match bridge.encode out with
    | some answer => decide (← IO.monoMsNow) (Gate.receive Gate.acts ·.pending answer)
    | none => other out
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
    runtime, listener, desk, connections := ← Mutex.new {}, down
    localPort := (← listener.getSockName).port, lanes, ops }
  let read (v : View system) (answer : Response → BaseIO Unit) : BaseIO Unit := do
    let now ← IO.monoMsNow
    let calls ← desk.atomically do
      let d ← modifyGet fun d => (d, Desk.hole)
      let (id, waiting) := d.waiting.wait answer
      let d := { d with waiting }
      let (reads, acts) := Gate.admit (σ := readSig) config.reads Gate.acts d.reads id (.ok id)
      if acts.any (· matches .forward _) then
        let asked ← runtime.tryPeek v.reads (every := v.every) fun peek => do
          let response := match peek with
            | some peek => v.respond peek
            | none => busy
          decideRead (← IO.monoMsNow) (Gate.receive Gate.acts · (id, response))
        unless asked do
          let (waiter, waiting) := d.waiting.answer id
          set { d with waiting }
          return (waiter.map (· busy)).toList
      let (d', calls) := Desk.apply { d with reads } (now + config.reads.requestTimeout_ms) acts
      set d'
      return calls
    for call in calls do call
  let hand (request : Request) (answer : Response → BaseIO Unit) : BaseIO (Option ReqId) := do
    let request := bridge.prepare request
    if let some v := view request then
      read v answer
      return none
    let now ← IO.monoMsNow
    let (id, taken, calls) ← desk.atomically do
      -- Taken out of the lock's cell while it is held, so that its tables are updated in place.
      let d ← modifyGet fun d => (d, Desk.hole)
      let (id, waiting) := d.waiting.wait answer
      let d := { d with waiting }
      let (pending, acts) := Gate.admit gate Gate.acts d.pending id (bridge.decode id request)
      if acts.any (· matches .forward _) then
        unless ← runtime.tryInput (enter (id, request)) do
          let (waiter, waiting) := d.waiting.answer id
          set { d with waiting }
          return (id, false, (waiter.map (· busy)).toList)
      let (d', calls) := Desk.apply { d with pending } (now + gate.requestTimeout_ms) acts
      set d'
      return (id, true, calls)
    for call in calls do call
    return if taken then some id else none
  let arriving ← IO.mkRef (0 : Nat)
  let arrived (request : Request) (answer : Response → BaseIO Unit) : BaseIO Unit :=
    match arrive with
    | none => discard <| hand request answer
    | some work => do
      let taken ← arriving.modifyGet fun n =>
        if n < config.arriving_max then (true, n + 1) else (false, n)
      unless taken do return ← answer busy
      discard <| IO.asTask (prio := .dedicated) do
        let done ← (work request).toBaseIO
        arriving.modify (· - 1)
        match done with
        | .ok (.ok request) => discard <| hand request answer
        | .ok (.error response) => answer response
        | .error _ => answer (.text "the request could not be prepared\n" 500)
  let probe : BaseIO Ops.Probe := do
    let count ← server.connections.atomically (return (← get).count)
    return { recovered := ← runtime.hasRecovered, stopping := count.stopping
             connections := count.count, inbox := ← runtime.depth
             inflight := ← desk.atomically (return (← get).waiting.waiters.size) }
  let adopt (socket : TCP.Socket.Client) : Async Unit := do
    try socket.noDelay catch _ => pure ()
    let front := ops.front probe (← if config.ops.active then peerOf socket else pure none) arrived
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
        config, submit := front, submitStream := hand
        leave := server.connections.atomically do
          modify fun c => { c with count := c.count.leave, alive := c.alive.erase id } }
      set { c with count, alive := c.alive.insert id { line, tell := tell ctx line false },
                   next := c.next + 1 }
      return some ctx
    match admitted with
    | none =>
      ops.refused
      socket.close
    | some ctx => tell ctx line false .resume
  let expire (now : Nat) : BaseIO Unit := do
    let due ← desk.atomically do
      return (← get).deadlines.fold (fun due id at_ms => if at_ms ≤ now then id :: due else due) []
    for id in due do
      decide now fun d =>
        let (pending, acts) := Gate.step bridge gate Gate.acts d.pending (.expire id)
        (pending, .disarm id :: acts)
      decideRead now fun reads =>
        let (reads, acts) := Gate.step readBridge config.reads Gate.acts reads (.expire id)
        (reads, .disarm id :: acts)
  discard <| IO.asTask (prio := .dedicated) (ticker server config.tick_ms expire)
  background do
    repeat
      match ← (try some <$> listener.accept catch _ => pure none) with
      | some socket => adopt socket
      | none =>
        if (← server.connections.atomically (return (← get).count.stopping)) then break
        Async.sleep 50
  background do
    if (← runtime.ended).isSome then
      for (_, waiter) in ← desk.atomically (modifyGet fun d =>
          let (all, waiting) := d.waiting.drain
          (all, { d with waiting })) do waiter busy
      shutDown server
      awaitConnections server
      server.finish
  return server

/-- Serve `sys` behind a gate it shares the process with other things: an output of `sys` that
the bridge does not read as a response comes to `onOutput`, and `Server.tryInput` hands `sys` an
input that is no request. -/
def serveFronted (sys : System σ) [Hashable σ.Id] (bridge : Bridge σ) (config : ServerConfig := {})
    (runtimeConfig : Runtime.Config := {})
    (onOutput : σ.Out → Async Unit := fun _ => pure ())
    (arrive : Option (Request → IO (Except Response Request)) := none)
    (view : Request → Option (View sys) := fun _ => none) :
    Async (Server (admittedFronted sys bridge)) :=
  serveOn (admittedFronted sys bridge) bridge config runtimeConfig .inl id onOutput arrive
    fun request => (view request).map View.fronted

/-- Serve `sys` over HTTP: the gate stands before the shard, `bridge` turns requests into
inputs and outputs into responses, and `sys` runs on one shard (`Runtime`) as `admitted sys`.
Returns once the server is listening. Each request is answered exactly once by the gate.
`arrive` is work a request needs in IO before it is prepared, done on a task of its own: what it
returns enters as the request, or is the answer and nothing enters. The sign-in (`SignIn.arrive`) is such work.
Requests of one connection may then enter in another order than they were read; their answers
are still written in that order. A request `view` names, once prepared, is a read: it is
answered from the states of the actors it reads and never enters the system (`View`); with none,
every request enters. -/
def serve (sys : System σ) [Hashable σ.Id] (bridge : Bridge σ) (config : ServerConfig := {})
    (runtimeConfig : Runtime.Config := {})
    (arrive : Option (Request → IO (Except Response Request)) := none)
    (view : Request → Option (View sys) := fun _ => none) :
    Async (Server (admitted sys bridge)) :=
  serveOn (admitted sys bridge) bridge config runtimeConfig id id (fun _ => pure ()) arrive
    fun request => (view request).map View.admitted

namespace Server

variable {system : System τ} [Hashable τ.Id]

/-- The port the server listens on: the one picked when `ServerConfig.port` is `0`. -/
def port (server : Server system) : Option UInt16 :=
  some server.localPort

/-- Stop accepting connections and stop the shard; requests in flight are answered `503`.
Returns once every connection has written what it owes and closed. -/
def stop (server : Server system) : Async Unit := do
  shutDown server
  server.runtime.stop
  for (_, waiter) in ← server.desk.atomically (modifyGet fun d =>
      let (all, waiting) := d.waiting.drain
      (all, { d with waiting })) do waiter busy
  awaitConnections server
  server.finish

/-- Readiness answers `503` from now on, while the server goes on serving, so that a load
balancer stops sending it requests before `stop`. -/
def drain (server : Server system) : BaseIO Unit :=
  server.ops.drain

/-- The requests the shard has taken and the server has not yet answered. -/
def inFlight (server : Server system) : BaseIO Nat :=
  server.desk.atomically (return (← get).waiting.waiters.size)

/-- The events performed, if the runtime was started with `record`. For conformance tests. -/
def trace (server : Server system) : BaseIO (Array (Event τ)) :=
  server.runtime.trace

/-- Returns when the server has shut down, and throws if the shard ended on an error, so that a
`main` that waits here exits with a failure and can be started again. -/
def wait (server : Server system) : Async Unit := do
  discard <| await server.down.result?
  if let some e ← server.runtime.ended then throw e

/-- Wait as `wait` does, and on SIGTERM or SIGINT stop without dropping the requests in flight,
as `Http.Shutdown.step` decides: readiness answers `503` (`drain`) while the shard's answers to
the requests it has taken go out, until none is in flight or `drain_ms` has passed, then `stop`.
Returns then, so a `main` that ends here exits with status 0. A second signal ends the process at
once (`awaitStopSignal`). `listening` runs once the signals are caught. -/
def stopOnSignal (server : Server system) (drain_ms : Nat) (listening : IO Unit := pure ()) :
    Async Unit := do
  if (← awaitStopSignal (discard <| await server.down.result?) listening).isSome then
    return ← server.wait
  let mut phase := Shutdown.Phase.serving
  let mut event := Shutdown.Event.signal (← IO.monoMsNow)
  repeat
    let (next, actions) := Shutdown.step drain_ms phase event
    phase := next
    for a in actions do
      match a with
      | .drain => server.drain
      | .stop => server.stop
    if phase == .stopping then break
    Async.sleep 10
    event := .tick (← IO.monoMsNow) (← server.inFlight)

/-- Hand the system behind the gate an input that is not a request, such as an adapter's answer.
`false` if the shard's inbox is full. A request cannot be handed in this way,
so request ids stay the server's. -/
def tryInput {sys : System σ} [Hashable σ.Id] {bridge : Bridge σ}
    (server : Server (admittedFronted sys bridge)) (x : σ.In) : Async Bool :=
  server.runtime.tryInput (.inr x)

end Server

end Lanes.Http
