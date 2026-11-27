/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std.Async
public import Lanes.Actors.Runtime
public import Lanes.Actors.Outside
public import Lanes.Http.Wire

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

/-- Makes the call on a task of its own, so the shard does not wait for the network, and hands
the answer back as an input. An answer that finds the inbox full is dropped. -/
def handler {sys : System σ} [Hashable σ.Id] (port : Port σ) (config : Config := {})
    (rt : Runtime sys) (out : σ.Out) : Async Unit := do
  if let some (id, call) := port.called out then
    background do
      let answer ← try exchange call config catch _ => pure none
      discard <| rt.tryInput (port.reply id answer)

end Lanes.Http.Client
