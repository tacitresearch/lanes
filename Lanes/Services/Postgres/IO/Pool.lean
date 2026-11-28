/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Lib.Postgres.IO.Client
public import Lanes.Lib.Postgres.Pool

/-!
The IO of a pool of connections to PostgreSQL. Which connection a client gets, when one is opened
or closed, and who waits or is refused, are `Pool.step`'s (`Lanes/Lib/Postgres/Pool.lean`,
proved); whether a connection handed back may be handed out again is `Conn.reusable`, pure. This
file opens and closes the connections, keeps the clients waiting on promises, numbers
connections and clients from one counter, so that no number is used twice (the premise of
`Pool.never_again`), and tells the policy when a client's deadline passed.
-/

public section

namespace Lanes.Postgres

open Std Std.Async

structure Pool where
  cfg : Client.Config
  policy : Pool.Config
  state : IO.Ref Pool.State
  sessions : IO.Ref (Std.HashMap Nat Session)
  clients : IO.Ref (Std.HashMap Nat (IO.Promise (Except Pool.Refusal Nat)))
  next : IO.Ref Nat

namespace Pool

def new (cfg : Client.Config) (policy : Pool.Config := {}) : BaseIO Pool := do
  return { cfg, policy, state := ← IO.mkRef {}, sessions := ← IO.mkRef {}, clients := ← IO.mkRef {},
           next := ← IO.mkRef 0 }

def fresh (p : Pool) : BaseIO Nat := p.next.modifyGet fun n => (n, n + 1)

def answer (p : Pool) (client : Nat) (a : Except Pool.Refusal Nat) : BaseIO Unit := do
  if let some promise ← p.clients.modifyGet fun m => (m[client]?, m.erase client) then
    promise.resolve a

/-- Tell the policy `e` and do what it answers. -/
partial def tell (p : Pool) (e : Pool.Event) : Async Unit := do
  let actions ← p.state.modifyGet fun st =>
    let (st, actions) := Pool.step p.policy st e
    (actions, st)
  for a in actions do
    match a with
    | .connect =>
      background do
        match ← (try connect p.cfg catch _ => pure (.error none)) with
        | .ok s =>
          let id ← p.fresh
          p.sessions.modify (·.insert id s)
          p.tell (.opened id)
        | .error _ => p.tell .failed
    | .give client conn => p.answer client (.ok conn)
    | .refuse client why => p.answer client (.error why)
    | .close conn =>
      if let some s ← p.sessions.modifyGet fun m => (m[conn]?, m.erase conn) then
        background (try s.close catch _ => pure ())

/-- A connection, its number and its session, or why there is none by the deadline. -/
def checkout (p : Pool) (deadline_ms : Nat) : Async (Except Pool.Refusal (Nat × Session)) := do
  let client ← p.fresh
  let promise ← IO.Promise.new
  p.clients.modify (·.insert client promise)
  p.tell (.checkout client)
  let waited ← Session.within deadline_ms (await promise.result?)
  if waited.isNone then p.tell (.expire client)
  match ← await promise.result? with
  | some (.ok conn) =>
    match (← p.sessions.get)[conn]? with
    | some s => return .ok (conn, s)
    | none => return .error .unavailable
  | some (.error why) => return .error why
  | none => return .error .unavailable

/-- Hand a connection back; the policy closes it unless `Conn.reusable` says it may be used
again. -/
def checkin (p : Pool) (conn : Nat) (s : Session) : Async Unit := do
  p.tell (.checkin conn (← s.conn.get).reusable)

/-- Run `work` on a connection of the pool, and hand it back, also when `work` throws. -/
def withSession {α : Type} (p : Pool) (deadline_ms : Nat) (work : Session → Async α) :
    Async (Except Pool.Refusal α) := do
  match ← p.checkout deadline_ms with
  | .error why => return .error why
  | .ok (conn, s) =>
    try return .ok (← work s)
    finally p.checkin conn s

end Pool

end Lanes.Postgres
