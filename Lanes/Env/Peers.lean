/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std.Async
public import Lanes.Actors.Runtime
public import Lanes.Actors.Shard

/-!
Shards of one system in different processes, joined by TCP. Each process runs `System.shard`
on the ordinary runtime and gives it this adapter: a parcel the shard puts out is sent to the
process that hosts its receiver, and a parcel that arrives becomes an input.

The link this gives is the one `Link.network` models, and no better: a parcel may be lost (the
connection is down, a queue is full, the receiver's inbox is full) and, when a shard is started
again from its journal, sent twice. Within one connection parcels arrive in order. A system
that runs on this must be correct over `Link.network`, which is what its checks and proofs
should assume for links between actors on different shards.

What a parcel is as bytes, and that a stream cut anywhere reads as the parcels sent before the
cut, is `Parcel.receive_send`, proved. Trusted here: connecting, sending, receiving, and that
nothing arrives which was not sent. There is no authentication: listen only where every sender
is trusted.
-/

public section

namespace Lanes.Peers

open Std Std.Async

variable {σ : Signature}

structure Address where
  /-- An IPv4 address. -/
  host : String := "127.0.0.1"
  port : UInt16
  deriving DecidableEq, Repr, Hashable

/-- Every limit is explicit (rule 2.6). -/
structure Config (σ : Signature) where
  /-- Where this process takes parcels. Port `0` picks a free one. -/
  listen : Address
  /-- Where the process that hosts an actor listens, asked each time a parcel is sent, so that
  it may change. `none` for an actor nobody hosts: its parcels are dropped. -/
  home : σ.Id → BaseIO (Option Address)
  id : Codec σ.Id
  msg : ∀ i, Codec (σ.Msg i)
  /-- Parcels waiting to be sent to one process. Beyond it they are dropped. -/
  queue : Nat := 1024
  /-- A parcel larger than this ends the connection it arrives on. -/
  maxParcelBytes : Nat := 16777216
  /-- How long to leave a process alone after failing to reach it. -/
  retry_ms : Nat := 100

structure _root_.Lanes.Peers (σ : Signature) where
  private mk ::
  private config : Config σ
  private server : TCP.Socket.Server
  private lanes : Mutex (Std.HashMap Address (CloseableChannel ByteArray))
  private accepted : IO.Ref (Nat × Std.HashMap Nat TCP.Socket.Client)
  private stopped : IO.Ref Bool
  /-- The port in use, which `listen` may have left to the system to choose. -/
  port : UInt16

private def address (a : Address) : Option Std.Net.SocketAddress :=
  (Std.Net.IPv4Addr.ofString a.host).map fun ip => .v4 ⟨ip, a.port⟩

/-- Sends what is queued for one process, in order. While the process cannot be reached, what
is queued is dropped, so that what is sent once it can be is fresh. -/
private def sender (retry_ms : Nat) (to : Std.Net.SocketAddress) (lane : CloseableChannel ByteArray) :
    Async Unit := do
  let mut socket : Option TCP.Socket.Client := none
  repeat
    let some bytes ← await (← lane.recv) | break
    try
      let live ← match socket with
        | some live => pure live
        | none => do
          let fresh ← TCP.Socket.Client.mk
          fresh.connect to
          pure fresh
      socket := some live
      live.send bytes
    catch _ =>
      if let some broken := socket then try broken.close catch _ => pure ()
      socket := none
      Async.sleep (.ofNat retry_ms)
      while (← lane.tryRecv).isSome do pure ()
  if let some live := socket then try live.close catch _ => pure ()

private def receiver (config : Config σ) (deliver : Parcel σ → Async Unit)
    (client : TCP.Socket.Client) : Async Unit := do
  let mut received := ByteArray.empty
  try
    repeat
      let some arrived ← client.recv? 65536 | break
      received := received ++ arrived
      let some (parcels, taken) := Parcel.receive config.id config.msg received | break
      for parcel in parcels do deliver parcel
      received := received.extract taken received.size
      if received.size > config.maxParcelBytes then break
  catch _ => pure ()
  try client.close catch _ => pure ()

/-- Listen for parcels and hand each to `deliver`. -/
def start (config : Config σ) (deliver : Parcel σ → Async Unit) : Async (Peers σ) := do
  let some listen := address config.listen
    | throw (IO.userError s!"lanes: {config.listen.host} is not an IPv4 address")
  let server ← TCP.Socket.Server.mk
  server.bind listen
  server.listen 128
  let stopped ← IO.mkRef false
  let accepted ← IO.mkRef (0, {})
  background do
    try
      repeat
        let client ← server.accept
        let key ← accepted.modifyGet fun (next, live) => (next, (next + 1, live.insert next client))
        background do
          receiver config deliver client
          accepted.modify fun (next, live) => (next, live.erase key)
    catch _ => pure ()
  return { config, server, stopped, accepted, lanes := ← Mutex.new {}
           port := (← server.getSockName).port }

/-- Send a parcel to the process that hosts its receiver. It does not wait for the network: the
parcel is queued, and dropped if the queue is full or nobody hosts the receiver. -/
def send (peers : Peers σ) (parcel : Parcel σ) : Async Unit := do
  let some home ← peers.config.home parcel.1 | return
  let some to := address home | return
  unless Parcel.fits peers.config.id peers.config.msg parcel do return
  if ← peers.stopped.get then return
  let lane ← peers.lanes.atomically do
    if let some lane := (← get).get? home then return lane
    let lane ← CloseableChannel.new (some peers.config.queue)
    modify (·.insert home lane)
    background (sender peers.config.retry_ms to lane)
    return lane
  discard <| lane.trySend (Parcel.send peers.config.id peers.config.msg [parcel])

/-- Stop listening and sending, and end every connection, so that whoever was sending here
finds out and connects again to whatever listens next. -/
def stop (peers : Peers σ) : Async Unit := do
  peers.stopped.set true
  try peers.server.close catch _ => pure ()
  for client in ← peers.accepted.modifyGet fun (next, live) => (live.values, (next, {})) do
    try client.close catch _ => pure ()
  let lanes ← peers.lanes.atomically (modifyGet fun lanes => (lanes.values, {}))
  for lane in lanes do discard <| (lane.close : EIO _ Unit).toBaseIO

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
  ready.resolve fun parcel => discard <| rt.tryInput (.inr parcel)
  return (rt, peers)

end Lanes.Peers
