/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Services.Postgres.Pool
import Lanes.Check.Search

/-!
The pool's policy (`Lanes/Services/Postgres/Pool.lean`) against an IO that does what it may: clients
ask for connections whenever they like, a connection asked for opens or fails, a client hands
its connection back reusable or broken, and a client's deadline passes, in every order. The
search checks the bounds and that a connection handed back broken is never handed out again
(rule 5.1), beside the proofs (`Pool.run_size`, `Pool.run_waiting`, `Pool.never_again`), and
that every client is answered once.
-/

namespace Tests.PostgresPool

open Lanes Lanes.Check Lanes.Postgres

def cfg : Pool.Config := { max := 2, waiting_max := 2 }

structure World where
  pool : Pool.State := {}
  /-- Clients that have asked, and connections the IO has opened: their next numbers. -/
  clients : Nat := 0
  conns : Nat := 0
  /-- Connections asked for and not yet opened or failed. -/
  pending : Nat := 0
  holding : List Nat := []
  broken : List Nat := []
  answered : List Nat := []
  /-- A broken connection handed out, or a client answered twice. -/
  violation : Bool := false
  full : Bool := false
  timedOut : Bool := false
  replaced : Bool := false
  deriving DecidableEq, Hashable

def perform (w : World) : Pool.Action → World
  | .connect => { w with pending := w.pending + 1 }
  | .give client conn =>
    { w with holding := conn :: w.holding, answered := client :: w.answered,
             violation := w.violation || w.answered.contains client || w.broken.contains conn,
             replaced := w.replaced || !w.broken.isEmpty }
  | .refuse client why =>
    { w with answered := client :: w.answered, violation := w.violation || w.answered.contains client,
             full := w.full || why == .full, timedOut := w.timedOut || why == .timeout }
  | .close _ => w

def tell (w : World) (e : Pool.Event) : World :=
  let (pool, actions) := Pool.step cfg w.pool e
  actions.foldl perform { w with pool }

def next (w : World) : List (String × World) :=
  let asks := if w.clients < 4 then
      [("a client asks", tell { w with clients := w.clients + 1 } (.checkout w.clients))] else []
  let opens := if 0 < w.pending && w.conns < 4 then
      [("a connection opens",
          tell { w with pending := w.pending - 1, conns := w.conns + 1 } (.opened w.conns)),
        ("a connection fails", tell { w with pending := w.pending - 1 } .failed)] else []
  let back := w.holding.flatMap fun c =>
    let w' := { w with holding := w.holding.erase c }
    [("handed back", tell w' (.checkin c true)),
      ("handed back broken", tell { w' with broken := c :: w.broken } (.checkin c false))]
  let expires := (List.range w.clients).filterMap fun client =>
    if w.answered.contains client then none
    else some ("a deadline passes", tell w (.expire client))
  asks ++ opens ++ back ++ expires

def model : Model World String where
  init := [{}]
  next := next

def properties : List (Property World) :=
  [ .always "at most max connections are open or being opened" fun w => w.pool.size ≤ cfg.max,
    .always "at most waiting_max clients wait" fun w => w.pool.waiting.length ≤ cfg.waiting_max,
    .always "a broken connection is never handed out again, and no client is answered twice"
      fun w => !w.violation,
    .always "the connections being opened are those asked for" fun w => w.pool.opening == w.pending,
    .always "a client waits only while there is no idle connection" fun w =>
      w.pool.waiting.isEmpty || w.pool.idle.isEmpty,
    .sometimes "every connection is out and a client waits" fun w =>
      w.pool.size == cfg.max && !w.pool.waiting.isEmpty,
    .sometimes "a client is refused because too many wait" (·.full),
    .sometimes "a client's deadline passes" (·.timedOut),
    .sometimes "a connection is handed out after another was handed back broken" (·.replaced) ]

@[never_extract] def report := search model properties {} id

def checks : IO (List (String × Bool)) := do
  let r := report
  return [("postgres pool: the bounds hold and a broken connection is never handed out again",
    r.ok)]

end Tests.PostgresPool
