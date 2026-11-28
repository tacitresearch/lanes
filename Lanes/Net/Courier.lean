/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std.Data.HashMap
public import Lanes.Runtime.Shard
public import Lanes.Data.Fifo

/-!
The courier: every decision of the transport between processes, as a pure function. The
handler (`Lanes.Peers`) tells it what happened (`Event`) and does what it answers (`Action`),
and decides nothing: when to connect, what waits and what is dropped, one write at a time on a
connection, how long to leave a process alone after failing to reach it, what a stream of bytes
is as parcels, and what `stop` ends.

Because it is a function, what it promises is proved of it for every limit and every sequence
of events (`Lanes/Net/CourierSound.lean`), and the model checker runs it together with a
handler and a network that may fail at any moment (`Tests/Courier.lean`).
-/

@[expose] public section

namespace Lanes.Peers

variable {σ : Signature}

structure Address where
  /-- An IPv4 address. -/
  host : String := "127.0.0.1"
  port : UInt16
  deriving DecidableEq, Repr, Hashable

/-- A connection, named by the courier when it asks for one or is told of one. -/
abbrev Conn := Nat

inductive Line where
  | idle
  | dialing (conn : Conn)
  /-- `busy` while a write is under way on it. -/
  | up (conn : Conn) (busy : Bool)
  /-- The process could not be reached, and is left alone until then. -/
  | resting (until_ms : Nat)
  deriving DecidableEq, Repr, Hashable

/-- What the courier knows of one other process. -/
structure Wire where
  line : Line := .idle
  /-- Parcels waiting for the connection, oldest first. -/
  waiting : Fifo ByteArray := {}

/-- Every limit is explicit (rule 2.6). -/
structure Limits where
  /-- Parcels waiting to be sent to one process. Beyond it they are dropped. -/
  queue : Nat := 1024
  /-- A parcel larger than this is not sent, and more bytes than this without a whole parcel end
  the connection they arrive on. The same for every process of a system. -/
  maxParcelBytes : Nat := 16777216
  /-- How long to leave a process alone after failing to reach it. -/
  retry_ms : Nat := 100
  /-- How long the handshake that opens a connection may take (`Lanes.Peers.Handshake`). -/
  handshake_ms : Nat := 5000
  /-- The most bytes the other side's hello may take. -/
  helloBytes : Nat := 4096

structure Courier where
  wires : Std.HashMap Address Wire := {}
  /-- The process each connection the courier asked for leads to. -/
  dialed : Std.HashMap Conn Address := {}
  /-- What has arrived on each connection it was told of and is not yet a whole parcel. -/
  inbound : Std.HashMap Conn ByteArray := {}
  nextConn : Conn := 0
  stopped : Bool := false

inductive Event where
  | send (to : Address) (bytes : ByteArray) (now_ms : Nat)
  | connected (conn : Conn)
  | written (conn : Conn)
  /-- A connection could not be made, a write failed, or the other side left. -/
  | broken (conn : Conn) (now_ms : Nat)
  /-- Somebody connected. The courier names the connection (`Action.adopt`) or refuses it. -/
  | accepted
  | received (conn : Conn) (bytes : ByteArray)
  | stop

inductive Action (σ : Signature) where
  | dial (conn : Conn) (to : Address)
  | write (conn : Conn) (bytes : ByteArray)
  | close (conn : Conn)
  | adopt (conn : Conn)
  | refuse
  | deliver (parcel : Parcel σ)

namespace Courier

def wire (c : Courier) (to : Address) : Wire :=
  c.wires.getD to {}

def setWire (c : Courier) (to : Address) (wire : Wire) : Courier :=
  { c with wires := c.wires.insert to wire }

def dial (limits : Limits) (c : Courier) (to : Address) (bytes : ByteArray) :
    Courier × List (Action σ) :=
  ({ c with nextConn := c.nextConn + 1, dialed := c.dialed.insert c.nextConn to }.setWire to
      { line := .dialing c.nextConn,
        waiting := if limits.queue = 0 then {} else Fifo.push {} bytes },
    [.dial c.nextConn to])

def enqueue (limits : Limits) (c : Courier) (to : Address) (w : Wire)
    (bytes : ByteArray) : Courier :=
  if w.waiting.length < limits.queue then c.setWire to { w with waiting := w.waiting.push bytes }
  else c

/-- Write the oldest waiting parcel, if there is one and the connection is free. -/
def next (c : Courier) (to : Address) (conn : Conn) (w : Wire) :
    Courier × List (Action σ) :=
  match w.waiting.pop? with
  | some (bytes, rest) => (c.setWire to { line := .up conn true, waiting := rest }, [.write conn bytes])
  | none => (c.setWire to { w with line := .up conn false }, [])

/--
What the transport does about one thing that happened. `read` says what received bytes are as
parcels (`Parcel.receive`).

After `stop` it asks for nothing more: `stop` closes every connection it asked for or was told
of, also those still being made, so one that turns up late is already closed.
-/
def step (limits : Limits) (read : ByteArray → Option (List (Parcel σ) × Nat))
    (c : Courier) : Event → Courier × List (Action σ)
  | .send to bytes now_ms =>
    if c.stopped then (c, [])
    else
      let w := c.wire to
      match w.line with
      | .idle => dial limits c to bytes
      | .resting until_ms => if until_ms ≤ now_ms then dial limits c to bytes else (c, [])
      | .dialing _ => (enqueue limits c to w bytes, [])
      | .up conn false => (c.setWire to { w with line := .up conn true }, [.write conn bytes])
      | .up _ true => (enqueue limits c to w bytes, [])
  | .connected conn =>
    match c.dialed[conn]? with
    | some to =>
      let w := c.wire to
      if w.line = .dialing conn then next c to conn w else (c, [])
    | none => (c, [])
  | .written conn =>
    match c.dialed[conn]? with
    | some to =>
      let w := c.wire to
      if w.line = .up conn true then next c to conn w else (c, [])
    | none => (c, [])
  | .broken conn now_ms =>
    match c.dialed[conn]? with
    | some to =>
      let c := { c with dialed := c.dialed.erase conn }
      let w := c.wire to
      if w.line = .dialing conn ∨ w.line = .up conn true ∨ w.line = .up conn false then
        (c.setWire to { line := .resting (now_ms + limits.retry_ms) }, [.close conn])
      else (c, [.close conn])
    | none =>
      if c.inbound.contains conn then ({ c with inbound := c.inbound.erase conn }, [.close conn])
      else (c, [])
  | .accepted =>
    if c.stopped then (c, [.refuse])
    else
      ({ c with nextConn := c.nextConn + 1, inbound := c.inbound.insert c.nextConn .empty },
        [.adopt c.nextConn])
  | .received conn bytes =>
    match c.inbound[conn]? with
    | some earlier =>
      let all := earlier ++ bytes
      match read all with
      | some (parcels, taken) =>
        let rest := all.extract taken all.size
        if rest.size > limits.maxParcelBytes then
          ({ c with inbound := c.inbound.erase conn }, parcels.map .deliver ++ [.close conn])
        else ({ c with inbound := c.inbound.insert conn rest }, parcels.map .deliver)
      | none => ({ c with inbound := c.inbound.erase conn }, [.close conn])
    | none => if c.dialed.contains conn then (c, []) else (c, [.close conn])
  | .stop =>
    ({ stopped := true, nextConn := c.nextConn },
      (c.dialed.keys ++ c.inbound.keys).map .close)

end Courier

end Lanes.Peers
