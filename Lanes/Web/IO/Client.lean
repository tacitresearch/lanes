/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std.Async
public import Lanes.Runtime.IO.Shell
public import Lanes.Outside.Basic
public import Lanes.Web.Http.Sse

/-!
The HTTP client as an adapter. A system calls another service with an output and gets the
response, or the news that there is none, as an input. `Client.outside` is what such a service
may do, which the checker explores; `Client.handler` does it over a socket.

HTTP/1.1 without TLS, one request per connection, IPv4 addresses. For anything past the local
network, call through a proxy that speaks TLS.
-/

public section

namespace Lanes.Http.Client

open Std Std.Async

variable {σ : Signature}

structure Call where
  /-- An IPv4 address. Names are not resolved. -/
  host : String
  port : UInt16
  request : Request
  deriving DecidableEq, Repr, Hashable

/-- Which outputs are calls and which inputs answer them. `none` for a response means there was
none: the service could not be reached, took too long, or answered what is not HTTP. -/
structure Port (σ : Signature) where
  called : σ.Out → Option (Nat × Call)
  reply : (call : Nat) → Option Response → σ.In
  replied : σ.In → Option Nat

/-- What a service may do: answer a call that is open, once, with any response or with none. It
may also never answer, so whoever calls keeps its own deadline. It remembers the open calls. -/
@[expose] def outside (port : Port σ) : Outside σ (List Nat) where
  init := []
  allow calls x :=
    match port.replied x with
    | some call => if call ∈ calls then some (calls.erase call) else none
    | none => none
  observe calls out :=
    match port.called out with
    | some (call, _) => call :: calls
    | none => calls

/-- Every limit is explicit (rule 2.6). -/
structure Config where
  timeout_ms : Nat := 10000
  maxResponseBytes : Nat := 1048576

private def converse (socket : TCP.Socket.Client) (address : Std.Net.SocketAddress)
    (request : ByteArray) (config : Config) : Async (Option Response) := do
  socket.connect address
  socket.send request
  let mut received := ByteArray.empty
  repeat
    let arrived ← socket.recv? 65536
    received := received ++ arrived.getD .empty
    if let .done answer := Response.read config.maxResponseBytes received arrived.isNone then
      return answer
  return none

/-- Make one call: its response, or `none` if there is none by the deadline. `Async.race` leaves
the loser running, so the socket is closed whoever wins: that fails what a call given up on
still waits for, and ends its task. -/
def exchange (call : Call) (config : Config) : Async (Option Response) := do
  let some addr := Std.Net.IPv4Addr.ofString call.host | return none
  let some request := call.request.wire call.host | return none
  let socket ← TCP.Socket.Client.mk
  let attempt : Async (Option Response) := do
    try converse socket (.v4 ⟨addr, call.port⟩) request config
    catch _ => pure none
  let patience := (fun _ => (none : Option Response)) <$> Async.sleep (.ofNat config.timeout_ms)
  try Async.race attempt patience
  finally socket.close

/-- One request to a server on this machine, for tests: its response, or an error that says why
there is none. -/
def fetch (port : UInt16) (request : Request) (config : Config := {}) (host := "127.0.0.1") :
    IO Response := do
  match ← (exchange { host, port, request } config).block with
  | some response => return response
  | none => throw (IO.userError s!"lanes: no response from {host}:{port} to {request.target}")

/-- A stream of events from a server on this machine, for tests: the events read once `enough`
holds of them, or when the server ends the stream, or at the deadline. -/
def events (port : UInt16) (request : Request) (enough : List Sse.Event → Bool)
    (timeout_ms : Nat := 5000) (host := "127.0.0.1") : IO (List Sse.Event) := do
  let some addr := Std.Net.IPv4Addr.ofString host | return []
  let some bytes := request.wire host | return []
  let socket ← TCP.Socket.Client.mk
  let received ← IO.mkRef ByteArray.empty
  let read : Async Unit := do
    socket.connect (.v4 ⟨addr, port⟩)
    socket.send bytes
    repeat
      let some more ← socket.recv? 65536 | break
      received.modify (· ++ more)
      if enough (Sse.received (← received.get)) then break
  try (Async.race (try read catch _ => pure ()) (Async.sleep (.ofNat timeout_ms))).block
  finally socket.close
  return Sse.received (← received.get)

/-- Makes the call on a task of its own, so the shard does not wait for the network, and hands
the answer back as an input. An answer that finds the inbox full is dropped. -/
def handler {sys : System σ} [Hashable σ.Id] (port : Port σ) (config : Config := {})
    (rt : Runtime sys) (out : σ.Out) : Async Unit := do
  if let some (id, call) := port.called out then
    background do
      let answer ← try exchange call config catch _ => pure none
      discard <| rt.tryInput (port.reply id answer)

end Lanes.Http.Client
