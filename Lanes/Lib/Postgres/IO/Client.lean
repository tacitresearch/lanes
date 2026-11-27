/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std.Async
public import Lanes.Runtime.IO.Shell
public import Lanes.Lib.Postgres.Table

/-!
The IO of a connection to PostgreSQL. It opens a TCP socket, tells the connection (`Postgres.Conn.step`)
what happened, and does what it answers: send bytes, report a reply. It decides nothing (rule
3.9): which bytes to send, what the server's bytes mean, which reply answers which request and
what a reply to `COMMIT` means are `Conn.step`'s, proved in `Lanes/Lib/Postgres/ConnSound.lean`.
It draws the SCRAM nonce from libsodium, reads no more than `Conn.room` bytes at a time, and
tells the connection the socket broke when a send or a read fails or a request's deadline passes.

`Session` is a connection used by one task at a time. `Store.handler` runs the transactional
store of `Lanes/Outside/Store/Basic.lean` on a table (`Lanes/Lib/Postgres/Table.lean`) as an
adapter: each transaction on a connection of its own, each request on a task of its own, its
answer handed back as an input. Plain TCP to an IPv4 address; no TLS.
-/

public section

namespace Lanes.Postgres

open Std Std.Async

structure Client.Config where
  /-- An IPv4 address. Names are not resolved. -/
  host : String
  port : UInt16 := 5432
  conn : Conn.Config
  /-- How long connecting and authenticating, and each request, may take (rule 3.4). -/
  timeout_ms : Nat := 10000

structure Session where
  socket : TCP.Socket.Client
  cfg : Conn.Config
  conn : IO.Ref Conn
  next : IO.Ref Nat
  timeout_ms : Nat

namespace Session

/-- Tell the connection `e` and do what it answers; what it answers is returned. A send that
fails is told as a broken socket. -/
partial def tell (s : Session) (e : Conn.Event) : Async (List Conn.Action) := do
  let (c, actions) := (← s.conn.get).step s.cfg e
  s.conn.set c
  let mut failed := false
  for a in actions do
    match a with
    | .send bytes | .query _ bytes =>
      if !failed then
        try s.socket.send bytes catch _ => failed := true
    | .close _ => s.socket.close
    | _ => pure ()
  if failed then return actions ++ (← s.tell .broken) else return actions

/-- Read and tell until `found` picks something out of what the connection answers, or it
closes. -/
partial def await {α : Type} (s : Session) (found : List Conn.Action → Option α)
    (seen : List Conn.Action) : Async (Option α) := do
  if let some a := found seen then return some a
  if seen.any (fun | .close _ => true | _ => false) then return none
  let room := (← s.conn.get).room s.cfg
  let bytes ← try s.socket.recv? (min room 65536).toUInt64 catch _ => pure (some .empty)
  let actions ← match bytes with
    | some b => if b.isEmpty then s.tell .broken else s.tell (.received b)
    | none => s.tell .ended
  s.await found actions

def within {α : Type} (timeout_ms : Nat) (work : Async (Option α)) : Async (Option α) :=
  Async.race work ((fun _ => none) <$> Async.sleep (.ofNat timeout_ms))

/-- Send `r` and wait for its reply. A deadline that passes breaks the connection, and the reply
is then `unknown`. -/
def exec (s : Session) (r : Request) : Async Reply := do
  let id ← s.next.modifyGet fun n => (n, n + 1)
  let pick := fun (actions : List Conn.Action) => actions.findSome? fun
    | .reply i reply => if i == id then some reply else none
    | _ => none
  let first ← s.tell (.submit id r)
  match ← within s.timeout_ms (s.await pick first) with
  | some reply => return reply
  | none =>
    let late ← s.tell .broken
    return (pick late).getD .unknown

/-- Tell the server the session is over, and close. -/
def close (s : Session) : Async Unit := do
  discard <| s.tell .stop
  s.socket.close

end Session

/-- Connect and authenticate: a session open for requests, or why it closed. -/
def connect (cfg : Client.Config) : Async (Except (Option Closing) Session) := do
  let some addr := Std.Net.IPv4Addr.ofString cfg.host | return .error none
  let nonce := Base64.encode .std (← randomBytes 18)
  let conn := { cfg.conn with nonce }
  let socket ← TCP.Socket.Client.mk
  let s : Session := { socket, cfg := conn, conn := ← IO.mkRef {}, next := ← IO.mkRef 0,
                       timeout_ms := cfg.timeout_ms }
  let opened := fun (actions : List Conn.Action) => actions.findSome? fun
    | .opened => some (Except.ok ())
    | .close why => some (.error why)
    | _ => none
  let attempt : Async (Option (Except Closing Unit)) := do
    socket.connect (.v4 ⟨addr, cfg.port⟩)
    let (c, actions) := Conn.start conn
    s.conn.set c
    for a in actions do
      if let .send bytes := a then socket.send bytes
    s.await opened actions
  match ← (try Session.within cfg.timeout_ms attempt catch _ => pure none) with
  | some (.ok ()) => return .ok s
  | some (.error why) => socket.close; return .error (some why)
  | none => socket.close; return .error none

namespace Store

/-- The sessions of the transactions open. -/
abbrev Sessions := IO.Ref (List (Nat × Session))

/-- Perform one request on its transaction's session, opening one for `begin`, and closing it
once the transaction is over or its session failed. -/
def perform (cfg : Client.Config) (table : Table) (isolation : Lanes.Store.Isolation)
    (sessions : Sessions) (r : Lanes.Store.Request Nat String) : Async (Lanes.Store.Answer Nat String) := do
  let request := table.request isolation r.op
  let session ← match r.op with
    | .begin =>
      match ← connect cfg with
      | .ok s =>
        sessions.modify ((r.txn, s) :: ·)
        pure (some s)
      | .error _ => pure none
    | _ => pure ((← sessions.get).lookup r.txn)
  let some s := session | return .failed
  let reply ← try s.exec request catch _ => pure .unknown
  let answer := Table.answer r.op reply
  if Table.over r.op answer then
    sessions.modify (·.filter (·.1 != r.txn))
    try s.close catch _ => pure ()
  return answer

/-- The store as an adapter: each request on a task of its own, its answer handed back as an
input. An answer that finds the inbox full is dropped, which the model allows as a lost one. -/
def handler {σ : Signature} {sys : System σ} [Hashable σ.Id] (port : Lanes.Store.Port σ Nat String)
    (cfg : Client.Config) (table : Table) (isolation : Lanes.Store.Isolation) (sessions : Sessions)
    (rt : Runtime sys) (out : σ.Out) : Async Unit := do
  if let some r := port.request out then
    background do
      let answer ← try perform cfg table isolation sessions r catch _ => pure .unknown
      discard <| rt.tryInput (port.reply { id := r.id, answer })

end Store

end Lanes.Postgres
