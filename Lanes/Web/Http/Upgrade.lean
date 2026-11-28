/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Web.Http.Basic

/-!
A protocol a connection switches to after `101 Switching Protocols`, as a pure machine that the
server's loop runs as it runs `Http.Conn`: it is told what happened (`Upgrade.Event`) and does
what the machine answers (`Upgrade.Action`).

A request the protocol `wants` is handed to the system by its head, and its connection reads
nothing more until the answer. An answer of `101` switches the connection: the machine starts
from the head and the answer, and once every earlier response is written it is given the socket
with the bytes read after the head (`Event.attached`). From then on it hands the system
requests of its own, through the gate, each tagged with the id the head entered with
(`Http.Stream.tag`), and the system reaches it with outputs that answer that id
(`Event.pushed`): the gate takes no answer to an id it has answered, so these come here instead
(`docs/decisions/` "WebSockets behind the gate").

`Upgrade.none` is the default: no request switches, and the server is as it was without it.
WebSockets are one such protocol (`Lanes.Web.Http.WebSocketSession`).
-/

@[expose] public section

namespace Lanes.Http

namespace Upgrade

inductive Event where
  /-- The connection is the protocol's, with the bytes read after the head. -/
  | attached (rest : ByteArray)
  | received (bytes : ByteArray)
  /-- The peer sends no more. -/
  | ended
  /-- The socket failed, or the connection closed before it was handed over. -/
  | broken
  /-- Everything written has been sent. -/
  | sent
  | tick
  /-- The server is stopping. -/
  | stop
  /-- The system's answer to the request `submit` handed it as `index`. -/
  | answered (index : Nat) (response : Response)
  /-- An output of the system that answers the id the head entered with. -/
  | pushed (response : Response)
  deriving Repr

inductive Action where
  | write (bytes : ByteArray)
  /-- Hand the system a request; its answer is `answered index`. -/
  | submit (index : Nat) (request : Request)
  /-- Close the socket, once what was written is sent. -/
  | close
  deriving Repr

end Upgrade

/-- A protocol that connections may switch to. -/
structure Upgrade where
  /-- Which requests may switch, by their head. -/
  wants : Request → Bool
  State : Type
  /-- The state once the system has answered the head `101`, before the socket is handed over. -/
  start : (now_ms : Nat) → (head : Request) → (response : Response) → State
  step : (now_ms : Nat) → State → Upgrade.Event → State × List Upgrade.Action
  wantsInput : State → Bool
  /-- How many bytes to read at most. -/
  room : State → Nat
  /-- When to be told `tick`. -/
  wakeAt : State → Option Nat
  /-- Whether to be told `sent` once the last write has ended. -/
  unsent : State → Bool
  /-- The socket is closed and the protocol has nothing more to do. -/
  closed : State → Bool

/-- No request switches. -/
def Upgrade.none : Upgrade where
  wants _ := false
  State := Unit
  start _ _ _ := ()
  step _ _ _ := ((), [])
  wantsInput _ := false
  room _ := 0
  wakeAt _ := Option.none
  unsent _ := false
  closed _ := true

end Lanes.Http
