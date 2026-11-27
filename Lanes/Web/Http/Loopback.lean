/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Runtime.Kernel
public import Lanes.Web.Http.Conn
public import Lanes.Web.Http.Front

/-!
An application's front end with no socket, for tests: the bytes of a request go through the
connection the server runs (`Conn.step`), the requests it hands on through the bridge's
`prepare` into `served sys` on a kernel of its own, and the bytes written back are read by the
client's reader (`Response.read`). What the server's loop does with these is IO; everything it
decides is here, run as it runs there. Time passes only when nothing else can happen: then the
kernel's next timer is due, so a request the system never answers gets the gate's `504`.

Each exchange is a connection of its own; the system's state carries over from one to the next.
-/

@[expose] public section

namespace Lanes.Http

variable {σ : Signature}

structure Loopback (sys : System σ) [Hashable σ.Id] (bridge : Bridge σ) (gate : GateConfig) where
  kernel : Kernel (served sys bridge gate)
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
    (conn : Conn.Config := {}) : Loopback sys bridge gate :=
  { kernel := (Kernel.boot (served sys bridge gate)).1, conn }

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

/-- Hand the system a request, as the server does: prepared, under the next id. `reply` is
what the connection is told when the gate answers that id. -/
def submit (lb : Loopback sys bridge gate) (x : Exchange) (request : Request)
    (reply : Response → Conn.Event) : Loopback sys bridge gate × Exchange :=
  let id := lb.nextId
  let step := lb.kernel.accept (id, bridge.prepare request)
  ({ lb with kernel := step.kernel, nextId := id + 1 },
    { x with asked := x.asked ++ [(id, reply)] })

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

/-- Let the kernel work and the connection hear the answers, until both are quiet: then, with
`timers`, let time pass to the next timer of the kernel or the connection, and go on, until the
connection closes or `fuel` runs out. -/
def settle (lb : Loopback sys bridge gate) (x : Exchange) (timers : Bool) :
    Nat → Loopback sys bridge gate × Exchange
  | 0 => (lb, x)
  | fuel + 1 =>
    if x.closed then (lb, x)
    else
      let step := lb.kernel.runBatch 64
      let lb := { lb with kernel := step.kernel }
      if step.outputs.isEmpty && step.events.isEmpty then
        let timer := match lb.kernel.wait with
          | .for_ms ms => some (lb.now_ms + ms)
          | _ => none
        match Conn.earlier timer (x.conn.wakeAt lb.conn) with
        | some at_ms =>
          if !timers || x.until_ms < at_ms then (lb, x)
          else
            let now_ms := max lb.now_ms at_ms
            let (lb, x) := tell { lb with kernel := lb.kernel.advance now_ms, now_ms } x .tick
            settle lb x timers fuel
        | none => (lb, x)
      else
        let (lb, x) := step.outputs.foldl (init := (lb, x)) fun (lb, x) out =>
          match told x out with
          | (x, some e) => tell lb x e
          | (x, none) => (lb, x)
        settle lb x timers fuel

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
