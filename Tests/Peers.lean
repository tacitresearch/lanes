/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Tests.Fixtures.Bank
import Tests.Durable
import Tests.HttpClient

/-!
Shards joined by TCP: the bank with each account on a shard of its own, each shard listening on
its own port, credits travelling between them as parcels. The pure reading of a stream of
parcels, on the compiled code. And the transport alone, one end sending and another keeping
what it is sent: order, the size limit, and ends that leave, come back or are not there.
-/

namespace Tests.Peers

open Lanes Std Std.Async Tests.Fixtures.Bank

abbrev Bank3 := bank (Fin 3) 1000

abbrev σ := sig (Fin 3)

def idCodec : Codec σ.Id := Codec.fin

def msgCodec (i : σ.Id) : Codec (σ.Msg i) :=
  (actors (Codec.fin (n := 3)) 1000).msg i

def receive (bytes : ByteArray) : Option (List (Parcel σ) × Nat) :=
  Parcel.receive idCodec msgCodec bytes

def parcels : List (Parcel σ) :=
  [⟨0, .credit 5⟩, ⟨2, .transfer 7 1 300⟩, ⟨1, .query 9⟩, ⟨1, .credit 0⟩]

def tests : List (String × Bool) :=
  let stream := Parcel.send idCodec msgCodec parcels
  [ ("peers: a stream of parcels cut at any byte reads as the parcels sent before the cut",
      (List.range (stream.size + 1)).all fun n =>
        match receive (stream.extract 0 n) with
        | some (found, taken) =>
          taken ≤ n && found == parcels.take found.length
            && (n < stream.size || found.length == parcels.length)
        | none => false),
    ("peers: read in pieces of any size, a stream gives the parcels sent, in order",
      [1, 2, 7, 64].all fun piece => Id.run do
        let mut received := ByteArray.empty
        let mut found : List (Parcel σ) := []
        for start in List.range ((stream.size + piece - 1) / piece) do
          received := received ++ stream.extract (start * piece) ((start + 1) * piece)
          match receive received with
          | some (more, taken) =>
            found := found ++ more
            received := received.extract taken received.size
          | none => return false
        return found == parcels && received.isEmpty),
    ("peers: bytes that are not parcels end the reading",
      (receive (stream.set! (stream.size - 2) (stream[stream.size - 2]! ^^^ 1))).isNone) ]

structure Shard where
  input : Request (Fin 3) → Async Unit
  balance : Async Int
  stop : Async Unit

def startShard (ports : IO.Ref (Array UInt16)) (answered : IO.Ref Nat) (k : Nat) :
    Async Shard := do
  let config : Peers.Config σ := {
    listen := { port := (← ports.get)[k]?.getD 0 }
    home := fun i => return (← ports.get)[i.val]?.map fun port => { port }
    id := idCodec, msg := msgCodec }
  let (rt, peers) ← Peers.shard Bank3 (fun i => i.val == k) config {}
    (fun _ => answered.modify (· + 1))
  if (← ports.get).size ≤ k then ports.modify (·.push peers.port)
  return {
    input := fun x => rt.input (.inl x)
    balance := return (← rt.state (Fin.ofNat 3 k)).balance
    stop := do peers.stop; rt.stop }

def live : Async (List (String × Bool)) := do
  let ports ← IO.mkRef (#[] : Array UInt16)
  let answered ← IO.mkRef 0
  let mut shards : Array Shard := #[]
  for k in [0:3] do shards := shards.push (← startShard ports answered k)
  for round in [0:100] do
    for k in [0:3] do
      if let some shard := shards[k]? then
        shard.input (.transfer ⟨3 * round + k, Fin.ofNat 3 k, Fin.ofNat 3 (k + 1), 1 + k⟩)
  let mut settled := []
  for _ in [0:100] do
    settled ← shards.toList.mapM (·.balance)
    if settled.sum == 3000 then break
    Async.sleep 50
  let some (first, second) := (shards[0]?).bind fun a => (shards[1]?).map (a, ·)
    | return [("peers: the shards started", false)]
  second.stop
  let again ← startShard ports answered 1
  let mut reached := 0
  for round in [0:100] do
    first.input (.transfer ⟨1000 + round, 0, 1, 1⟩)
    Async.sleep 50
    reached ← again.balance
    if reached > 1000 then break
  for shard in shards.toList.eraseIdx 1 ++ [again] do shard.stop
  return [
    ("peers: three shards joined by TCP move every credit between them",
      settled == [1200, 900, 900] && (← answered.get) ≥ 300),
    ("peers: a shard started again on the same port is found by those that were sending",
      reached > 1000) ]

/-- A shard with peers, on a journal, stopped and started again. -/
def durable : Async (List (String × Bool)) := do
  let path ← Tests.Durable.scratch "peers"
  let first (account : Fin 3) : Bool := account == 0
  let balanceAfter (requests : List (Request (Fin 3))) : Async (Option Int) := do
    try
      let log ← Journal.Store.open (sys := Bank3.shard first)
        { path, input := Codec.sum (Request.codec Codec.fin) (Codec.sigma idCodec msgCodec) }
      let (rt, peers) ← Peers.shard Bank3 first
        { listen := { port := 0 }, home := fun _ => pure none, id := idCodec, msg := msgCodec }
        (journal := some log)
      for request in requests do rt.input (.inl request)
      rt.idle
      let balance := (← rt.state 0).balance
      peers.stop
      rt.stop
      return some balance
    catch _ => return none
  let before ← balanceAfter [.transfer ⟨1, 0, 1, 5⟩]
  let after ← balanceAfter []
  Tests.Durable.remove path
  return [("peers: a shard with peers on a journal comes back in the state it was in",
    before == some 995 && after == some 995)]

/-! The transport alone. -/

structure End where
  peers : Peers σ
  got : IO.Ref (Array (Parcel σ))

/-- A transport that sends every parcel to the port in `home` and keeps what it is sent. -/
def endpoint (home : IO.Ref UInt16) (port : UInt16 := 0)
    (limits : Peers.Limits := { retry_ms := 20 }) : Async End := do
  let got ← IO.mkRef #[]
  let peers ← Peers.start {
    listen := { port }
    home := fun _ => return some { port := ← home.get }
    id := idCodec, msg := msgCodec, limits } fun parcel => got.modify (·.push parcel)
  return { peers, got }

/-- What the end has been sent, once that is `count` parcels or two seconds have passed. -/
def End.collected (side : End) (count : Nat) : Async (List (Parcel σ)) := do
  for _ in [0:200] do
    if (← side.got.get).size ≥ count then break
    Async.sleep 10
  return (← side.got.get).toList

def connect (port : UInt16) : Async TCP.Socket.Client := do
  let socket ← TCP.Socket.Client.mk
  socket.connect (.v4 ⟨.ofParts 127 0 0 1, port⟩)
  return socket

def credit (amount : Nat) : Parcel σ := ⟨1, .credit amount⟩

def orderTest : Async (List (String × Bool)) := do
  let home ← IO.mkRef 0
  let receiver ← endpoint home
  home.set receiver.peers.port
  let sender ← endpoint home
  let sent := (List.range 300).map credit
  for parcel in sent do sender.peers.send parcel
  let arrived ← receiver.collected sent.length
  receiver.got.set #[]
  let socket ← connect receiver.peers.port
  socket.send (Parcel.send idCodec msgCodec parcels)
  let together ← receiver.collected parcels.length
  socket.close
  let before ← Tests.HttpClient.openFiles
  let visits := 20
  for _ in [0:visits] do (← connect receiver.peers.port).close
  let after ← Tests.HttpClient.openFilesSettled (before.getD 0 + 2)
  sender.peers.stop
  receiver.peers.stop
  return [
    ("transport: three hundred parcels on one connection arrive, each once, in the order sent",
      arrived == sent),
    ("transport: parcels that arrive in one piece are handed on in the order they have in it",
      together == parcels),
    (s!"transport: the socket of a peer that left is closed ({before} files before, {after} "
      ++ "after)",
      match before, after with
      | some before, some after => after < before + visits
      | _, _ => true) ]

def limitTest : Async (List (String × Bool)) := do
  let home ← IO.mkRef 0
  let receiver ← endpoint home
  home.set receiver.peers.port
  let small := credit 5
  let large : Parcel σ := ⟨2, .transfer 70000 1 30000000⟩
  let size (parcel : Parcel σ) := (Parcel.send idCodec msgCodec [parcel]).size
  let sender ← endpoint home (limits := { maxParcelBytes := size small })
  for parcel in [small, large, credit 6] do sender.peers.send parcel
  let arrived ← receiver.collected 2
  sender.peers.stop
  receiver.peers.stop
  return [("transport: a parcel over the limit is not sent, and those before and after it are",
    size small < size large && arrived == [small, credit 6])]

def leavingTest : Async (List (String × Bool)) := do
  let home ← IO.mkRef 0
  let first ← endpoint home
  home.set first.peers.port
  let sender ← endpoint home
  sender.peers.send (credit 1)
  let met ← first.collected 1
  first.peers.stop
  let second ← endpoint home (port := first.peers.port)
  Async.sleep 200
  sender.peers.send (credit 2)
  let found ← second.collected 1
  second.peers.stop
  let nobody := second.peers.port
  let other ← endpoint home
  home.set nobody
  other.peers.send (credit 3)
  Async.sleep 100
  let late ← endpoint home (port := nobody)
  Async.sleep 100
  other.peers.send (credit 4)
  let reached ← late.collected 1
  for side in [sender, other, late] do side.peers.stop
  return [
    ("transport: a peer that leaves a connection nothing is being sent on is noticed, and the "
      ++ "next parcel reaches whoever listens there now",
      met == [credit 1] && found == [credit 2]),
    ("transport: a peer that was not there is tried again, and found once it is",
      reached == [credit 4]) ]

def transport : Async (List (String × Bool)) := do
  return (← orderTest) ++ (← limitTest) ++ (← leavingTest)

end Tests.Peers
