/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import TodoDb

/-!
The to-do list on a real PostgreSQL, through the typed store's driver
(`Postgres.Typed.handler`), connected as libpq's variables say (`Postgres.Client.fromEnv`). For
a server set up by `scripts/postgres-test-server` on port 5433:

```bash
PGHOST=localhost PGPORT=5433 PGUSER=lanes_scram PGPASSWORD=scram-pw PGDATABASE=lanes_test \
  lake exe todoLive
```

It drops and creates the table `todos` from the schema, adds three to-dos, one of them twice,
completes one and lists the user's. Without `PGHOST` it says so and exits.
-/

open Lanes TodoDb Std.Async

def main : IO UInt32 := do
  if (← IO.getEnv "PGHOST").isNone then
    IO.println "PGHOST is not set: no server to run against"; return 0
  let cfg ← Postgres.Client.fromEnv
  let .ok s ← (Postgres.connect cfg).block | throw (IO.userError "cannot connect")
  discard <| (s.exec (.statement { sql := "DROP TABLE IF EXISTS todos" })).block
  let errors ← (Postgres.Typed.create s schema).block
  (s.close).block
  unless errors.isEmpty do IO.println s!"{errors}"; return 1
  let store : Postgres.Typed.Store Request Answer := { pool := ← Postgres.Pool.new cfg, handler := handler true }
  let outs ← IO.mkRef ([] : List Out)
  let requests := [Request.add 7 "milk", .add 7 "eggs", .add 7 "milk", .add 8 "milk", .complete 7 1, .list 7]
  let run : Async Unit := do
    let rt ← Runtime.startWith (system {}) {} fun rt _ out => do
      outs.modify (· ++ [out])
      Postgres.Typed.handler port store rt out
    for (r, n) in requests.zip (List.range requests.length) do
      rt.input (.request n r)
      -- One at a time, so that the answers are in order.
      for _ in List.range 100 do
        let done := (← outs.get).countP fun | .answered .. | .gaveUp _ => true | _ => false
        if done > n then break
        Std.Async.sleep (.ofNat 20)
    rt.stop
  run.block
  let answers := (← outs.get).filterMap fun
    | .answered n a => some (n, a)
    | _ => none
  for (n, a) in answers do IO.println s!"{n}: {repr a}"
  let expected : List (Nat × Answer) :=
    [(0, .added 0), (1, .added 1), (2, .existing 0), (3, .added 2), (4, .done),
     (5, .list [{ id := 1, owner := 7, title := "eggs", done := true }, { id := 0, owner := 7, title := "milk" }])]
  return if answers == expected then 0 else 1
