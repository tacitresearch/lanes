/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
The courier against a network that fails. The model here is the handler and the network
together: connections that take time to make and may not be made, writes that may fail, a peer
that leaves, time that passes, bytes that arrive in pieces, and `stop` at any moment. The
search explores every order of these and checks what the transport promises.

It does not promise that parcels arrive in the order sent. A write on a connection that then
fails may still have gone out, and the next parcel goes on a new connection: the search showed
this when the property claimed order, and it is why the link is modelled as unordered.
-/

namespace Tests.Courier

open Lanes Lanes.Check Lanes.Peers

abbrev wireSig : Signature where
  Id := Unit
  Msg _ := Nat

def peer : Address := { port := 1 }

def limits : Limits := { queue := 2, maxParcelBytes := 4, retry_ms := 1 }

/-- A parcel is two bytes on this wire: a 7, then the number. Anything else is not a parcel. -/
def read (bytes : ByteArray) : Option (List (Parcel wireSig) × Nat) :=
  let whole := bytes.size / 2
  let pairs := (List.range whole).map fun k => (bytes[2 * k]!, bytes[2 * k + 1]!)
  if pairs.all (·.1 == 7) then some (pairs.map fun (_, n) => ⟨(), n.toNat⟩, 2 * whole) else none

def stream : ByteArray := ⟨#[7, 1, 7, 2, 7, 3]⟩

structure World where
  courier : Courier := {}
  /-- The connections the handler holds a socket for. -/
  sockets : List Conn := []
  dialing : List Conn := []
  writing : List (Conn × Nat) := []
  asked : List Nat := []
  started : List Nat := []
  wrote : List Nat := []
  now : Nat := 0
  breaks : Nat := 0
  /-- A parcel found the queue full. -/
  full : Bool := false
  /-- A write was asked for on a connection the handler has no socket for. -/
  stray : Bool := false
  adopted : Option Conn := none
  refused : Bool := false
  /-- How much of `stream` has arrived. -/
  arrived : Nat := 0
  delivered : List Nat := []
  stopped : Bool := false
  /-- A connection asked for before `stop` was made after it. -/
  late : Bool := false
  /-- The peer is left alone until then, after a connection to it failed. -/
  barred : Nat := 0
  /-- A connection was asked for while the peer was to be left alone. -/
  hasty : Bool := false

def key (w : World) :=
  let wire := w.courier.wire peer
  let byConn {α : Type} (l : List (Conn × α)) := l.mergeSort fun a b => a.1 ≤ b.1
  ((wire.line, wire.waiting.toList, byConn w.courier.dialed.toList, byConn w.courier.inbound.toList,
      w.courier.nextConn, w.courier.stopped),
    (w.sockets, w.dialing, w.writing, w.asked, w.started, w.wrote, w.now, w.breaks),
    (w.full, w.stray, w.adopted, w.refused, w.arrived, w.delivered, w.stopped, w.late, w.barred, w.hasty))

instance : BEq World := ⟨fun a b => key a == key b⟩
instance : Hashable World := ⟨fun w => hash (key w)⟩

def perform (w : World) : Action wireSig → World
  | .dial conn _ =>
    { w with sockets := conn :: w.sockets, dialing := conn :: w.dialing
             hasty := w.hasty || w.now < w.barred }
  | .write conn bytes =>
    { w with
      writing := (conn, bytes[0]!.toNat) :: w.writing
      started := w.started ++ [bytes[0]!.toNat]
      stray := w.stray || !w.sockets.contains conn }
  | .close conn => { w with sockets := w.sockets.erase conn }
  | .adopt conn => { w with sockets := conn :: w.sockets, adopted := some conn }
  | .refuse => { w with refused := true }
  | .deliver parcel => { w with delivered := w.delivered ++ [parcel.2] }

def tell (w : World) (event : Event) : World :=
  let (courier, actions) := w.courier.step limits read event
  let w := match event with
    | .broken conn now_ms =>
      if w.courier.dialed.contains conn then { w with barred := now_ms + limits.retry_ms } else w
    | _ => w
  actions.foldl perform { w with courier }

def next (w : World) : List (String × World) :=
  let wire := w.courier.wire peer
  let waits := wire.waiting.length ≥ limits.queue
    && (wire.line matches .dialing _ | .up _ true)
  (if w.asked.length < 3 then
    [("send", tell { w with asked := w.asked ++ [w.asked.length], full := w.full || waits }
      (.send peer ⟨#[w.asked.length.toUInt8]⟩ w.now))] else [])
  ++ (if w.now < 2 then [("tick", { w with now := w.now + 1 })] else [])
  ++ w.dialing.flatMap (fun conn =>
    let w := { w with dialing := w.dialing.erase conn }
    [("connected", tell { w with late := w.late || w.stopped } (.connected conn)),
      ("unreachable", tell { w with breaks := w.breaks + 1 } (.broken conn w.now))])
  ++ w.writing.flatMap (fun (conn, n) =>
    let w := { w with writing := w.writing.erase (conn, n) }
    [("written", tell { w with wrote := w.wrote ++ [n] } (.written conn))]
      ++ if w.breaks < 2 then
        [("write fails", tell { w with breaks := w.breaks + 1 } (.broken conn w.now))] else [])
  ++ (if w.breaks < 2 then
    w.sockets.map fun conn =>
      ("peer leaves", tell { w with breaks := w.breaks + 1 } (.broken conn w.now)) else [])
  ++ (if w.adopted.isNone && !w.refused then [("accepted", tell w .accepted)] else [])
  ++ (match w.adopted with
    | some conn =>
      if w.arrived < stream.size && w.sockets.contains conn then
        [1, 3].map fun piece =>
          ("received", tell { w with arrived := min stream.size (w.arrived + piece) }
            (.received conn (stream.extract w.arrived (w.arrived + piece))))
      else []
    | none => [])
  ++ (if w.stopped then [] else [("stop", tell { w with stopped := true } .stop)])

def model : Model World String where
  init := [{}]
  next := next

def quiet (w : World) : Bool :=
  w.dialing.isEmpty && w.writing.isEmpty && (w.courier.wire peer).waiting.isEmpty

def report := search model
  [ .always "one write at a time on a connection" fun w => (w.writing.map (·.1)).eraseDups.length
      == w.writing.length,
    .always "no write on a connection the handler has closed" fun w => !w.stray,
    .always "writes are started in the order asked, each parcel at most once" fun w =>
      w.started.isSublist w.asked,
    .always "what was written had been started, once" fun w =>
      w.wrote.all (w.started.contains ·) && w.wrote.eraseDups.length == w.wrote.length,
    .always "no more wait than the limit" fun w =>
      (w.courier.wire peer).waiting.length ≤ limits.queue,
    .always "after stop no socket is open" fun w => !w.stopped || w.sockets.isEmpty,
    .always "a peer that could not be reached is left alone for a while" fun w => !w.hasty,
    .always "nothing is lost unless a connection failed, the queue was full or it stopped" fun w =>
      w.breaks > 0 || w.full || w.stopped || !quiet w || w.wrote == w.asked,
    .always "what is delivered is what arrived, in order" fun w =>
      w.delivered == ([1, 2, 3].take (w.arrived / 2)) || w.stopped,
    .sometimes "three parcels are written" fun w => w.wrote.length == 3,
    .sometimes "a parcel is written after a connection failed" fun w =>
      w.breaks > 0 && w.wrote.getLast? == some 2 && w.wrote.length < 3,
    .sometimes "a parcel finds the queue full" fun w => w.full,
    .sometimes "a connection is made after stop, and nothing is open" fun w =>
      w.late && w.sockets.isEmpty,
    .sometimes "a whole stream is delivered" fun w => w.delivered == [1, 2, 3] ]
  {} id

def tests : List (String × Bool) :=
  [ ("courier: against a network that fails at any moment, every promise holds",
      report.ok && report.complete),
    ("courier: bytes that are not a parcel end the connection they arrive on",
      let adopted := tell {} .accepted
      let after := tell adopted (.received 0 ⟨#[7, 1, 9, 9]⟩)
      adopted.sockets == [0] && after.sockets.isEmpty && after.delivered.isEmpty),
    ("courier: more bytes than the limit without a whole parcel end the connection",
      let big : Limits := { maxParcelBytes := 0 }
      let (courier, _) := ({} : Courier).step (σ := wireSig) big read .accepted
      let (_, actions) := courier.step (σ := wireSig) big read (.received 0 ⟨#[7]⟩)
      actions.any fun
        | .close 0 => true
        | _ => false),
    ("courier: a queue of no room holds nothing, also while the connection is made",
      let none : Limits := { queue := 0 }
      let (courier, actions) := ({} : Courier).step (σ := wireSig) none read (.send peer stream 0)
      (courier.wire peer).waiting.length == 0 && actions matches [.dial 0 _]),
    ("courier: bytes on a connection it made do not end it, and the next parcel goes on it",
      let up := tell (tell (tell {} (.send peer ⟨#[0]⟩ 0)) (.connected 0)) (.written 0)
      let after := tell (tell up (.received 0 ⟨#[7, 1]⟩)) (.send peer ⟨#[1]⟩ 0)
      after.sockets == [0] && !after.stray && after.started == [0, 1]) ]

end Tests.Courier
