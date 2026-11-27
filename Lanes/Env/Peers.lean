/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std.Async
public import Lanes.Actors.Runtime
public import Lanes.Actors.Courier

/-!
Shards of one system in different processes, joined by TCP. Each process runs `System.shard`
on the ordinary runtime and gives it this adapter: a parcel the shard puts out is sent to the
process that hosts its receiver, and a parcel that arrives becomes an input.

The link this gives is the one `Link.network` models, and no better: a parcel may be lost (the
connection is down, a queue is full, the receiver's inbox is full) and, when a shard is started
again from its journal, sent twice. Within one connection parcels arrive in order. A system
that runs on this must be correct over `Link.network`, which is what its checks and proofs
should assume for links between actors on different shards.

Nothing is decided here. `Lanes.Peers.Courier` decides, a pure function that the model checker
runs against a network that fails; this file tells it what happened and does what it answers.
Trusted here: that an event is reported when the thing happened, that an action is done as
asked, and that nothing arrives which was not sent. There is no authentication: listen only
where every sender is trusted.
-/

public section

namespace Lanes.Peers

open Std Std.Async

variable {σ : Signature}

structure Config (σ : Signature) where
  /-- Where this process takes parcels. Port `0` picks a free one. -/
  listen : Address
  /-- Where the process that hosts an actor listens, asked each time a parcel is sent, so that
  it may change. `none` for an actor nobody hosts: its parcels are dropped. -/
  home : σ.Id → BaseIO (Option Address)
  id : Codec σ.Id
  msg : ∀ i, Codec (σ.Msg i)
  limits : Limits := {}

private abbrev Happened := Event × Option TCP.Socket.Client

structure _root_.Lanes.Peers (σ : Signature) where
  private mk ::
  private config : Config σ
  private server : TCP.Socket.Server
  private events : CloseableChannel Happened
  private ended : IO.Promise Unit
  private complained : IO.Ref Bool
  /-- The port in use, which `listen` may have left to the system to choose. -/
  port : UInt16

private def address (a : Address) : Option Std.Net.SocketAddress :=
  (Std.Net.IPv4Addr.ofString a.host).map fun ip => .v4 ⟨ip, a.port⟩

private def quietly (action : Async Unit) : Async Unit :=
  try action catch _ => pure ()

/-- `false` once the transport has stopped: nobody will hear of the event. -/
private def post (events : CloseableChannel Happened) (event : Event)
    (fresh : Option TCP.Socket.Client := none) : BaseIO Bool :=
  events.trySend (event, fresh)

/-- Read a connection until it ends, and say so. A connection this side made carries nothing
back, and is read all the same: that is how a peer that has left is noticed before the next
parcel is written to it and lost. -/
private def listen (events : CloseableChannel Happened) (conn : Conn) (socket : TCP.Socket.Client)
    (hear : ByteArray → BaseIO Unit) : Async Unit := do
  try
    repeat
      let some bytes ← socket.recv? 65536 | break
      hear bytes
  catch _ => pure ()
  discard <| post events (.broken conn (← IO.monoMsNow))

/-- Tell the courier what happened and do what it answers, one event at a time. Every socket is
in `sockets` from the moment it exists, so the `close` the courier asks for at `stop` reaches
it whatever it was in the middle of. -/
private def run (config : Config σ) (deliver : Parcel σ → Async Unit)
    (events : CloseableChannel Happened) : Async Unit := do
  let mut courier : Courier := {}
  let mut sockets : Std.HashMap Conn TCP.Socket.Client := {}
  repeat
    let some (event, fresh) ← await (← events.recv) | break
    let (next, actions) := courier.step config.limits (Parcel.receive config.id config.msg) event
    courier := next
    for action in actions do
      match action with
      | .dial conn to =>
        match address to, ← (TCP.Socket.Client.mk).toBaseIO with
        | some target, .ok socket =>
          sockets := sockets.insert conn socket
          background do
            try
              socket.connect target
              discard <| post events (.connected conn)
              listen events conn socket fun _ => pure ()
            catch _ => discard <| post events (.broken conn (← IO.monoMsNow))
        | _, _ => discard <| post events (.broken conn (← IO.monoMsNow))
      | .write conn bytes =>
        match sockets[conn]? with
        | some socket => background do
          try
            socket.send bytes
            discard <| post events (.written conn)
          catch _ => discard <| post events (.broken conn (← IO.monoMsNow))
        | none => discard <| post events (.broken conn (← IO.monoMsNow))
      | .close conn =>
        if let some socket := sockets[conn]? then quietly socket.close
        sockets := sockets.erase conn
      | .adopt conn =>
        if let some socket := fresh then
          sockets := sockets.insert conn socket
          background (listen events conn socket fun bytes =>
            discard <| post events (.received conn bytes))
      | .refuse => if let some socket := fresh then quietly socket.close
      | .deliver parcel => deliver parcel
    if courier.stopped then break
  discard <| (events.close : EIO _ Unit).toBaseIO

/-- Listen for parcels and hand each to `deliver`. -/
def start (config : Config σ) (deliver : Parcel σ → Async Unit) : Async (Peers σ) := do
  let some listen := address config.listen
    | throw (IO.userError s!"lanes: {config.listen.host} is not an IPv4 address")
  let server ← TCP.Socket.Server.mk
  server.bind listen
  server.listen 128
  let events ← CloseableChannel.new
  let ended ← IO.Promise.new
  background do
    quietly (run config deliver events)
    ended.resolve ()
  background do
    repeat
      match ← (try some <$> server.accept catch _ => pure none) with
      | some client => unless ← post events .accepted (some client) do quietly client.close
      | none =>
        if ← events.isClosed then break
        Async.sleep 50
  return { config, server, events, ended, complained := ← IO.mkRef false
           port := (← server.getSockName).port }

/-- Send a parcel to the process that hosts its receiver. It does not wait for the network: the
courier queues the parcel or drops it. A parcel larger than the receiver would take is not sent
at all, and the first such parcel is reported: a system that keeps sending one is stuck. -/
def send (peers : Peers σ) (parcel : Parcel σ) : Async Unit := do
  let some home ← peers.config.home parcel.1 | return
  let bytes := Parcel.send peers.config.id peers.config.msg [parcel]
  if Parcel.fits peers.config.id peers.config.msg parcel
      && bytes.size ≤ peers.config.limits.maxParcelBytes then
    discard <| post peers.events (.send home bytes (← IO.monoMsNow))
  else if !(← peers.complained.modifyGet fun said => (said, true)) then
    IO.eprintln s!"lanes: a parcel of {bytes.size} bytes is over the limit of \
      {peers.config.limits.maxParcelBytes} and is dropped, as every such parcel will be"


/-- Stop listening and sending, and end every connection, so that whoever was sending here
finds out and connects again to whatever listens next. Returns when that is done. -/
def stop (peers : Peers σ) : Async Unit := do
  quietly peers.server.close
  discard <| post peers.events .stop
  discard <| await peers.ended.result?

/--
Run a shard of `sys` in this process: the actors `hosts` says, on a runtime, with parcels to
and from the other processes carried by `Peers`. An input from outside goes to `Runtime.input`
as `.inl`; an output of the system comes to `onOutput`. A parcel that finds the shard's inbox
full is dropped.
-/
def shard (sys : System σ) [Hashable σ.Id] (hosts : σ.Id → Bool) (config : Config σ)
    (runtimeConfig : Runtime.Config := {}) (onOutput : σ.Out → Async Unit := fun _ => pure ())
    (journal : Option (Journal.Log (sys.shard hosts)) := none) :
    Async (Runtime (sys.shard hosts) × Peers σ) := do
  let ready : IO.Promise (Parcel σ → Async Unit) ← IO.Promise.new
  let peers ← start config fun parcel => do
    if let some offer ← await ready.result? then offer parcel
  let rt ← Runtime.start (sys.shard hosts) runtimeConfig (journal := journal) fun
    | .inl out => onOutput out
    | .inr parcel => peers.send parcel
  ready.resolve fun parcel => (discard <| rt.tryInput (.inr parcel) : Async Unit)
  return (rt, peers)

end Lanes.Peers
