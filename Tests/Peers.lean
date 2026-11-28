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
parcels, and the handshake, on the compiled code. And the transport alone, one end sending and
another keeping what it is sent: order, the size limit, ends that leave, come back or are not
there, and ends refused at the handshake.
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

/-! The handshake, pure. -/

def key : ByteArray := "the key the tests' peers share..".toUTF8

def system : String := "the bank on three shards"

def schema : String := "Tests.Fixtures.Bank"

def nonce (n : Nat) : ByteArray := Sha256.hash (toString n).toUTF8

def setupOf (role : Peers.Handshake.Role) (n : Nat) (key : ByteArray := key)
    (version := Peers.Handshake.version) (system := system) (schema := schema) :
    Peers.Handshake.Setup :=
  { role, key, maxHelloBytes := 4096
    ours := { version, system, digest := Sha256.hash schema.toUTF8, nonce := nonce n } }

def written (actions : List Peers.Handshake.Action) : ByteArray :=
  actions.foldl (fun acc action => match action with
    | .write bytes => acc ++ bytes
    | _ => acc) .empty

/-- How a side's handshake ended: the bytes after it, or why it refused. -/
def outcome (actions : List Peers.Handshake.Action) :
    Option (Peers.Handshake.Refusal ⊕ ByteArray) :=
  actions.findSome? fun
    | .ready rest => some (.inr rest)
    | .refuse why => some (.inl why)
    | .write _ => none

/-- Two sides of a handshake, each handed what the other writes in pieces of `piece` bytes:
everything each answered. -/
def converse (a b : Peers.Handshake.Setup) (piece : Nat) :
    List Peers.Handshake.Action × List Peers.Handshake.Action := Id.run do
  let (sa, aa) := Peers.Handshake.start a
  let (sb, ab) := Peers.Handshake.start b
  let mut (sa, sb, doneA, doneB) := (sa, sb, aa, ab)
  let mut (toA, toB) := (written ab, written aa)
  for _ in [0:1000] do
    if toA.isEmpty && toB.isEmpty then break
    unless toA.isEmpty do
      let (next, acts) := Peers.Handshake.step a sa (.received (toA.extract 0 piece))
      toA := toA.extract piece toA.size
      (sa, doneA, toB) := (next, doneA ++ acts, toB ++ written acts)
    unless toB.isEmpty do
      let (next, acts) := Peers.Handshake.step b sb (.received (toB.extract 0 piece))
      toB := toB.extract piece toB.size
      (sb, doneB, toA) := (next, doneB ++ acts, toA ++ written acts)
  return (doneA, doneB)

/-- What a side answers when it is handed `bytes`, all at once. -/
def handed (s : Peers.Handshake.Setup) (bytes : ByteArray) : List Peers.Handshake.Action :=
  let (st, first) := Peers.Handshake.start s
  first ++ (Peers.Handshake.step s st (.received bytes)).2

def refusedWith (a b : Peers.Handshake.Setup) (whyA whyB : Peers.Handshake.Refusal) : Bool :=
  [1, 5, 1000].all fun piece =>
    let (doneA, doneB) := converse a b piece
    outcome doneA == some (.inl whyA) && outcome doneB == some (.inl whyB)

def handshakeTests : List (String × Bool) :=
  let dialer := setupOf .dialer 1
  let acceptor := setupOf .acceptor 2
  let recorded := written (converse dialer acceptor 1000).1
  let fresh := setupOf .acceptor 3
  let digest (schema : String) := Sha256.hash schema.toUTF8
  [ ("handshake: two sides with the same version, system, schema and key connect, however the \
      bytes are cut",
      [1, 2, 7, 32, 1000].all fun piece =>
        let (doneA, doneB) := converse dialer acceptor piece
        outcome doneA == some (.inr .empty) && outcome doneB == some (.inr .empty)),
    ("handshake: another version is refused by both sides, each naming both versions",
      refusedWith (setupOf .dialer 1 (version := 2)) acceptor (.version 2 1) (.version 1 2)
        && (Peers.Handshake.Refusal.version 1 2).message.contains "version 2"
        && (Peers.Handshake.Refusal.version 1 2).message.contains "version 1"),
    ("handshake: another system is refused by both sides, each naming both systems",
      refusedWith (setupOf .dialer 1 (system := "other")) acceptor (.system "other" system)
        (.system system "other")),
    ("handshake: another schema is refused by both sides, each naming both digests",
      refusedWith (setupOf .dialer 1 (schema := "other")) acceptor
        (.digest (digest "other") (digest schema)) (.digest (digest schema) (digest "other"))
        && ((Peers.Handshake.Refusal.digest (digest schema) (digest "other")).message.contains
          (Bytes.hex (digest "other")))),
    ("handshake: a side with another key is refused by both",
      refusedWith (setupOf .dialer 1 (key := "another key of thirty-two bytes!".toUTF8)) acceptor
        .proof .proof),
    ("handshake: what a dialer wrote, played again to an acceptor, is refused",
      outcome (handed fresh recorded) == some (.inl .proof)
        && outcome (handed acceptor recorded) == some (.inr .empty)),
    ("handshake: what an acceptor wrote, played again to a dialer, is refused",
      outcome (handed (setupOf .dialer 4) (written (converse dialer acceptor 1000).2))
        == some (.inl .proof)),
    ("handshake: a dialer's own hello and proof, sent back to it, are refused",
      let (st, first) := Peers.Handshake.start dialer
      let (st, second) := Peers.Handshake.step dialer st (.received (written first))
      outcome (Peers.Handshake.step dialer st (.received (written second))).2
        == some (.inl .proof)),
    ("handshake: bytes that are not a hello are refused as not a peer's",
      outcome (handed acceptor "GET / HTTP/1.1\r\n\r\n".toUTF8)
        == some (.inl (.foreign "GET / HT".toUTF8))),
    ("handshake: a hello longer than the limit is refused",
      outcome (handed acceptor (Peers.Handshake.Hello.write
        { system := String.ofList (List.replicate 5000 'x'), digest := .empty, nonce := .empty }))
        == some (.inl (.tooLong 4096))),
    ("handshake: the bytes after the proof are handed on",
      let (st, first) := Peers.Handshake.start acceptor
      let (doneD, _) := converse dialer acceptor 1000
      let bytes := written doneD ++ "parcels".toUTF8
      outcome (first ++ (Peers.Handshake.step acceptor st (.received bytes)).2)
        == some (.inr "parcels".toUTF8)),
    ("handshake: a side that leaves or takes too long is refused",
      let (st, _) := Peers.Handshake.start acceptor
      outcome (Peers.Handshake.step acceptor st .ended).2 == some (.inl .ended)
        && outcome (Peers.Handshake.step acceptor st .timeout).2 == some (.inl .timeout)),
    ("handshake: of the refusals, only a connection that ends is not reported",
      Peers.Handshake.Refusal.ended.quiet
        && ([.proof, .timeout, .malformed, .version 1 2] : List Peers.Handshake.Refusal).all
          (!·.quiet)) ]

def tests : List (String × Bool) :=
  handshakeTests ++
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
    id := idCodec, msg := msgCodec, system, schema, key }
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
        { listen := { port := 0 }, home := fun _ => pure none, id := idCodec, msg := msgCodec
          system, schema, key }
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
  refused : IO.Ref (Array Peers.Handshake.Refusal)

/-- A transport that sends every parcel to the port in `home` and keeps what it is sent, and
the refusals of its handshakes. -/
def endpoint (home : IO.Ref UInt16) (port : UInt16 := 0)
    (limits : Peers.Limits := { retry_ms := 20 }) (key : ByteArray := key) : Async End := do
  let got ← IO.mkRef #[]
  let refused ← IO.mkRef #[]
  let peers ← Peers.start {
    listen := { port }
    home := fun _ => return some { port := ← home.get }
    id := idCodec, msg := msgCodec, system, schema, key, limits
    refused := fun why => refused.modify (·.push why) } fun parcel => got.modify (·.push parcel)
  return { peers, got, refused }

/-- What the end has been sent, once that is `count` parcels or two seconds have passed. -/
def End.collected (side : End) (count : Nat) (tries : Nat := 200) : Async (List (Parcel σ)) := do
  for _ in [0:tries] do
    if (← side.got.get).size ≥ count then break
    Async.sleep 10
  return (← side.got.get).toList

def connect (port : UInt16) : Async TCP.Socket.Client := do
  let socket ← TCP.Socket.Client.mk
  socket.connect (.v4 ⟨.ofParts 127 0 0 1, port⟩)
  return socket

def credit (amount : Nat) : Parcel σ := ⟨1, .credit amount⟩

/-- Do a handshake on a socket as `s` says; what the socket read after it, or why it ended. -/
def shake (s : Peers.Handshake.Setup) (socket : TCP.Socket.Client) :
    Async (Peers.Handshake.Refusal ⊕ ByteArray) := do
  let (first, actions) := Peers.Handshake.start s
  let mut state := first
  let mut todo := actions
  for _ in [0:100] do
    for action in todo do
      match action with
      | .write bytes => socket.send bytes
      | .ready rest => return .inr rest
      | .refuse why => return .inl why
    let event := match ← socket.recv? 65536 with
      | some bytes => Peers.Handshake.Event.received bytes
      | none => .ended
    (state, todo) := Peers.Handshake.step s state event
  return .inl .timeout

/-- What the end has refused, once that is something or a second has passed. -/
def End.refusals (side : End) : Async (List Peers.Handshake.Refusal) := do
  for _ in [0:100] do
    unless (← side.refused.get).isEmpty do break
    Async.sleep 10
  return (← side.refused.get).toList

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
  let shaken ← shake (setupOf .dialer 7) socket
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
      shaken == .inr .empty && together == parcels),
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

/-- Ends with different keys: a parcel sent from one to the other never arrives, and each
refuses the other. -/
def keyTest : Async (List (String × Bool)) := do
  let home ← IO.mkRef 0
  let receiver ← endpoint home
  home.set receiver.peers.port
  let sender ← endpoint home (key := "another key of thirty-two bytes!".toUTF8)
  sender.peers.send (credit 1)
  let refusedThere ← receiver.refusals
  let refusedHere ← sender.refusals
  let arrived ← receiver.collected 1 (tries := 20)
  sender.peers.stop
  receiver.peers.stop
  return [("transport: an end with another key is refused, and nothing it sends arrives",
    arrived.isEmpty && refusedThere.take 1 == [.proof] && refusedHere.take 1 == [.proof])]

/-- A client that speaks another version of the handshake is refused, and is told this one's. -/
def versionTest : Async (List (String × Bool)) := do
  let home ← IO.mkRef 0
  let receiver ← endpoint home
  let socket ← connect receiver.peers.port
  let shaken ← shake (setupOf .dialer 8 (version := 2)) socket
  try socket.send (Parcel.send idCodec msgCodec parcels) catch _ => pure ()
  let refused ← receiver.refusals
  let arrived ← receiver.collected 1 (tries := 20)
  socket.close
  receiver.peers.stop
  return [("transport: a peer of another version is refused, each side naming both versions",
    shaken == .inl (.version 2 Peers.Handshake.version) && arrived.isEmpty
      && refused == [.version Peers.Handshake.version 2])]

/-- Listen on a port as one side of the handshake would, and keep every byte the first peer
that connects sends, the handshake included, for `ms`. -/
def eavesdrop (ms : Nat) : Async (UInt16 × IO.Promise ByteArray) := do
  let server ← TCP.Socket.Server.mk
  server.bind (.v4 ⟨.ofParts 127 0 0 1, 0⟩)
  server.listen 1
  let heard ← IO.Promise.new
  background do
    let client ← server.accept
    let (first, actions) := Peers.Handshake.start (setupOf .acceptor 9)
    for action in actions do if let .write bytes := action then client.send bytes
    let mut all := ByteArray.empty
    let mut state := first
    let mut ready := false
    let mut after := ByteArray.empty
    let deadline := (← IO.monoMsNow) + ms
    while (← IO.monoMsNow) < deadline do
      let some bytes ← client.recv? 65536 | break
      all := all ++ bytes
      if ready then after := after ++ bytes
      else
        let (next, acts) := Peers.Handshake.step (setupOf .acceptor 9) state (.received bytes)
        state := next
        for action in acts do
          match action with
          | .write out => client.send out
          | .ready rest => ready := true; after := rest
          | .refuse _ => pure ()
      if ready && (Parcel.receive idCodec msgCodec after).any (·.1.length > 0) then break
    heard.resolve all
    client.close
    server.close
  return ((← server.getSockName).port, heard)

/-- The bytes a real dialer sent on one connection, handshake and parcel, played again to
another end with the same key: refused, and the parcel never arrives. -/
def replayTest : Async (List (String × Bool)) := do
  let (port, heard) ← eavesdrop 2000
  let home ← IO.mkRef port
  let sender ← endpoint home
  sender.peers.send (credit 1)
  let some recorded ← await heard.result? | return [("transport: a dialer was heard", false)]
  sender.peers.stop
  let receiver ← endpoint home
  let socket ← connect receiver.peers.port
  socket.send recorded
  let refused ← receiver.refusals
  let arrived ← receiver.collected 1 (tries := 20)
  socket.close
  receiver.peers.stop
  return [("transport: a dialer's handshake and parcel, played again to another end, are refused",
    recorded.size > 0 && arrived.isEmpty && refused == [.proof])]

def transport : Async (List (String × Bool)) := do
  return (← orderTest) ++ (← limitTest) ++ (← leavingTest) ++ (← keyTest) ++ (← versionTest)
    ++ (← replayTest)

end Tests.Peers
