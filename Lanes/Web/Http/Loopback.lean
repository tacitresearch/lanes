/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Runtime.Kernel
public import Lanes.Web.Http.Admit
public import Lanes.Web.Http.Conn
public import Lanes.Web.Http.View

/-!
An application's front end with no socket, for tests: the bytes of a request go through the
connection the server runs (`Conn.step`), the requests it hands on through the bridge's
`prepare` to the gate (`Gate.step`), what the gate admits into `admitted sys` on a kernel of its
own, and the bytes written back are read by the client's reader (`Response.read`). What the
server's loop does with these is IO; everything it decides is here, run as it runs there. Time
passes only when nothing else can happen: then the next timer of the kernel or the next
deadline of the gate is due, so a request the system never answers gets the gate's `504`.

A request the `view` names is a read, as the server answers it: its gate admits it, and it is
answered from the kernel's states at the end of the next batch of work, without entering the
kernel.

Each exchange is a connection of its own; the system's state carries over from one to the next.
-/

@[expose] public section

namespace Lanes.Http

variable {σ : Signature}

structure Loopback (sys : System σ) [Hashable σ.Id] (bridge : Bridge σ) (gate : GateConfig) where
  kernel : Kernel (admitted sys bridge)
  /-- The gate's state: the requests waiting for the system. -/
  pending : List ReqId := []
  /-- When each waiting request is due. -/
  deadlines : List (ReqId × Nat) := []
  /-- The gate's answers not yet told to the connection, oldest first. -/
  answers : List (ReqId × Response) := []
  /-- Which requests are reads, and how each is answered from the state (`Http.View`). -/
  view : Request → Option (View sys) := fun _ => none
  /-- The bounds of the gate of reads. -/
  readGate : GateConfig := {}
  /-- The gate of reads' state: the reads waiting for their peek. -/
  reads : List ReqId := []
  /-- The reads admitted, to be answered at the end of the next batch. -/
  peeks : List (ReqId × View sys) := []
  conn : Conn.Config := {}
  nextId : ReqId := 0
  now_ms : Nat := 0
  /-- The host a request is written to. -/
  host : String := "localhost"
  /-- Units of kernel work, and waits for a timer, before an exchange gives up. -/
  fuel : Nat := 100000
  /-- How long an exchange lets time pass, for a stream that does not end. -/
  wait_ms : Nat := 600000

namespace Loopback

variable {sys : System σ} [Hashable σ.Id] {bridge : Bridge σ} {gate : GateConfig}

def start (sys : System σ) [Hashable σ.Id] (bridge : Bridge σ) (gate : GateConfig := {})
    (conn : Conn.Config := {}) (view : Request → Option (View sys) := fun _ => none)
    (readGate : GateConfig := {}) : Loopback sys bridge gate :=
  { kernel := (Kernel.boot (admitted sys bridge)).1, conn, view, readGate }

/-- Do what the gate decided; what it passes on is `entry`, the arrival it decided on. -/
def act (lb : Loopback sys bridge gate) (entry : Option (ReqId × Request)) :
    List (Gate.Act σ) → Loopback sys bridge gate
  | [] => lb
  | a :: acts =>
    let lb := match a, entry with
      | .respond id response, _ => { lb with answers := lb.answers ++ [(id, response)] }
      | .forward _, some entry => { lb with kernel := (lb.kernel.accept entry).kernel }
      | .forward _, none => lb
      | .arm id, _ =>
        { lb with deadlines := lb.deadlines ++ [(id, lb.now_ms + gate.requestTimeout_ms)] }
      | .disarm id, _ => { lb with deadlines := lb.deadlines.filter (·.1 != id) }
    act lb entry acts

/-- Let the gate decide on `msg`, as the server does. -/
def decide (lb : Loopback sys bridge gate) (msg : GateMsg σ) : Loopback sys bridge gate :=
  let (pending, acts) := Gate.step bridge gate Gate.acts lb.pending msg
  let entry := match msg with
    | .arrive id request => some (id, request)
    | _ => none
  { lb with pending }.act entry acts

/-- Let the gate of reads decide on `msg`, as the server does; what it admits is read by `v`. -/
def decideRead (lb : Loopback sys bridge gate) (msg : GateMsg readSig) (v : Option (View sys)) :
    Loopback sys bridge gate :=
  let (reads, acts) := Gate.step readBridge lb.readGate Gate.acts lb.reads msg
  acts.foldl (init := { lb with reads }) fun lb a =>
    match a, v with
    | .respond id response, _ => { lb with answers := lb.answers ++ [(id, response)] }
    | .forward id, some v => { lb with peeks := lb.peeks ++ [(id, v)] }
    | .forward _, none => lb
    | .arm id, _ =>
      { lb with deadlines := lb.deadlines ++ [(id, lb.now_ms + lb.readGate.requestTimeout_ms)] }
    | .disarm id, _ => { lb with deadlines := lb.deadlines.filter (·.1 != id) }

/-- Answer the reads waiting for a peek from the kernel's states, at the end of a batch. -/
def answerPeeks (lb : Loopback sys bridge gate) : Loopback sys bridge gate :=
  lb.peeks.foldl (init := { lb with peeks := [] }) fun lb (id, v) =>
    lb.decideRead (.answer (id, (v.admitted (bridge := bridge)).respond
      (Batch.Peek.of lb.kernel (v.reads.map .inr) (frontEvery v.every)))) none

/-- Pass the deadlines due by `now_ms` to the gates. -/
def expire (lb : Loopback sys bridge gate) (now_ms : Nat) : Loopback sys bridge gate :=
  let (due, rest) := lb.deadlines.partition (·.2 ≤ now_ms)
  due.foldl (fun lb (id, _) => (lb.decide (.expire id)).decideRead (.expire id) none)
    { lb with deadlines := rest }

/-- What a connection's loop would be told and what the client has received so far. -/
structure Exchange where
  conn : Conn
  /-- What the connection is told of the answer to each id the system was handed. -/
  asked : List (ReqId × (Response → Conn.Event)) := []
  written : ByteArray := .empty
  closed : Bool := false
  /-- The ids the heads of the requests that stream entered the system with, by number. -/
  heads : List (Nat × ReqId) := []
  /-- Time does not pass beyond this. -/
  until_ms : Nat := 0

/-- Put a request before the gate, as the server does: prepared, under the next id. `reply` is
what the connection is told when the gate answers that id. -/
def submit (lb : Loopback sys bridge gate) (x : Exchange) (request : Request)
    (reply : Response → Conn.Event) : Loopback sys bridge gate × Exchange :=
  let id := lb.nextId
  let request := bridge.prepare request
  let lb := match lb.view request with
    | some v => lb.decideRead (.arrive id request) (some v)
    | none => lb.decide (.arrive id request)
  ({ lb with nextId := id + 1 }, { x with asked := x.asked ++ [(id, reply)] })

/-- The events an answer gives: the connection is told it under the number it was asked as. -/
def told (x : Exchange) (out : ReqId × Response) : Exchange × Option Conn.Event :=
  match x.asked.find? (·.1 == out.1) with
  | some (_, reply) => ({ x with asked := x.asked.filter (·.1 != out.1) }, some (reply out.2))
  | none => (x, none)

/-- Do what the connection asks: write, hand on, close. -/
def perform (lb : Loopback sys bridge gate) (x : Exchange) :
    List Conn.Action → Loopback sys bridge gate × Exchange
  | [] => (lb, x)
  | action :: rest =>
    let (lb, x) := match action with
      | .submit seq request => lb.submit x request (.answered seq)
      | .begin seq request =>
        let (lb', x) := lb.submit x request (.responded seq)
        (lb', { x with heads := (seq, lb.nextId) :: x.heads })
      | .piece seq index request => match x.heads.lookup seq with
        | some id => lb.submit x (Stream.tag request id) (.took seq index)
        | none => (lb, x)
      | .pull seq index request => match x.heads.lookup seq with
        | some id => lb.submit x (Stream.tag request id) (.pulled seq index)
        | none => (lb, x)
      | .interim _ bytes | .write _ bytes | .part _ bytes =>
        (lb, { x with written := x.written ++ bytes })
      | .close => (lb, { x with closed := true })
    perform lb x rest

/-- Tell the connection `e` and do what it asks. What it writes is sent at once, and it is told
so. -/
def tell (lb : Loopback sys bridge gate) (x : Exchange) (e : Conn.Event) (fuel : Nat := 8) :
    Loopback sys bridge gate × Exchange :=
  let (conn, actions) := x.conn.step lb.conn lb.now_ms e
  let (lb, x) := lb.perform { x with conn } actions
  match fuel with
  | 0 => (lb, x)
  | fuel + 1 => if x.conn.unsent then tell lb x .sent fuel else (lb, x)

/-- Tell the connection the gate's answers. -/
def tellAnswers (lb : Loopback sys bridge gate) (x : Exchange) : Loopback sys bridge gate × Exchange :=
  let answers := lb.answers
  answers.foldl (init := ({ lb with answers := [] }, x)) fun (lb, x) out =>
    match told x out with
    | (x, some e) => tell lb x e
    | (x, none) => (lb, x)

/-- Let the kernel work, the gate read its outputs and the connection hear the answers, until
all are quiet: then, with `timers`, let time pass to the next timer of the kernel, deadline of
the gate or alarm of the connection, and go on, until the connection closes or `fuel` runs
out. -/
def settle (lb : Loopback sys bridge gate) (x : Exchange) (timers : Bool) :
    Nat → Loopback sys bridge gate × Exchange
  | 0 => (lb, x)
  | fuel + 1 =>
    if x.closed then (lb, x)
    else if !lb.answers.isEmpty then
      let (lb, x) := lb.tellAnswers x
      settle lb x timers fuel
    else
      let step := lb.kernel.runBatch 64
      let peeked := !lb.peeks.isEmpty
      let lb := step.outputs.foldl (fun lb out => lb.decide (.answer out))
        { lb with kernel := step.kernel }
      let lb := lb.answerPeeks
      if step.outputs.isEmpty && step.events.isEmpty && !peeked then
        let timer := match lb.kernel.wait with
          | .for_ms ms => some (lb.now_ms + ms)
          | _ => none
        let deadline := (lb.deadlines.map (·.2)).min?
        match Conn.earlier (Conn.earlier timer deadline) (x.conn.wakeAt lb.conn) with
        | some at_ms =>
          if !timers || x.until_ms < at_ms then (lb, x)
          else
            let now_ms := max lb.now_ms at_ms
            let lb := { lb with kernel := lb.kernel.advance now_ms, now_ms }.expire now_ms
            let (lb, x) := tell lb x .tick
            settle lb x timers fuel
        | none => (lb, x)
      else settle lb x timers fuel

/-- Send `pieces` on a new connection, each as the server would receive it, then the end of
them, and what the server writes back. -/
def converse (lb : Loopback sys bridge gate) (pieces : List ByteArray) :
    Loopback sys bridge gate × ByteArray :=
  let x : Exchange := { conn := { since_ms := lb.now_ms }, until_ms := lb.now_ms + lb.wait_ms }
  let (lb, x) := pieces.foldl (init := (lb, x)) fun (lb, x) bytes =>
    let (lb, x) := lb.tell x (.received bytes)
    lb.settle x false lb.fuel
  let (lb, x) := lb.settle x true lb.fuel
  let (lb, x) := lb.tell x .ended
  let (lb, x) := lb.settle x true lb.fuel
  (lb, x.written)

/-- One request on a connection of its own, and its response as the client reads it. -/
def send (lb : Loopback sys bridge gate) (request : Request) :
    Loopback sys bridge gate × Except String Response :=
  match request.wire lb.host with
  | none => (lb, .error "the request cannot be written")
  | some bytes =>
    let (lb, written) := lb.converse [bytes]
    match Response.read written.size written true with
    | .done (some response) => (lb, .ok response)
    | _ => (lb, .error s!"no response to /{"/".intercalate request.path}")

def get (lb : Loopback sys bridge gate) (path : List String)
    (headers : List (String × String) := []) :
    Loopback sys bridge gate × Except String Response :=
  lb.send { method := .get, path, headers }

/-- A form posted as `application/x-www-form-urlencoded`. -/
def post (lb : Loopback sys bridge gate) (path : List String) (fields : List (String × String))
    (headers : List (String × String) := []) :
    Loopback sys bridge gate × Except String Response :=
  lb.send { method := .post, path, body := (encodeForm fields).toUTF8
            headers := ("Content-Type", "application/x-www-form-urlencoded") :: headers }

end Loopback

end Lanes.Http
