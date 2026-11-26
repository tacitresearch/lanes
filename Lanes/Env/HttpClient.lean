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

private def exchange (call : Call) (config : Config) : Async (Option Response) := do
  let some addr := Std.Net.IPv4Addr.ofString call.host | return none
  let socket ← TCP.Socket.Client.mk
  socket.connect (.v4 ⟨addr, call.port⟩)
  socket.send (call.request.wire call.host)
  let mut received := ByteArray.empty
  repeat
    match ← socket.recv? 65536 with
    | some bytes =>
      received := received ++ bytes
      if received.size > config.maxResponseBytes then break
    | none => break
  socket.close
  return if received.size > config.maxResponseBytes then none else Response.parse received

/-- Makes the call on a task of its own, so the shard does not wait for the network, and hands
the answer back as an input. An answer that finds the inbox full is dropped. -/
def handler {sys : System σ} [Hashable σ.Id] (port : Port σ) (config : Config := {})
    (rt : Runtime sys) (out : σ.Out) : Async Unit := do
  if let some (id, call) := port.called out then
    background do
      let attempt : Async (Option Response) := do
        try exchange call config
        catch _ => pure none
      let patience : Async (Option Response) := do
        Async.sleep (.ofNat config.timeout_ms)
        return none
      discard <| rt.tryInput (port.reply id (← Async.race attempt patience))

end Lanes.Http.Client
