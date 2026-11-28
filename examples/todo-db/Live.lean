/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import TodoDb

/-!
The fixed to-do list on a real PostgreSQL, through the client's store adapter
(`Postgres.Store.handler`), connected as libpq's variables say (`Postgres.Client.fromEnv`). For
a server set up by `scripts/postgres-test-server` on port 5433:

```bash
PGHOST=localhost PGPORT=5433 PGUSER=lanes_scram PGPASSWORD=scram-pw PGDATABASE=lanes_test \
  lake exe todoLive
```

The to-dos go in the table `todo_db`. It adds three to-dos, one of them twice under the same
key, and prints the rows. Without `PGHOST` it says so and exits.
-/

open Lanes TodoDb Std.Async

def table : Postgres.Table := { name := "todo_db" }

def main : IO UInt32 := do
  if (← IO.getEnv "PGHOST").isNone then
    IO.println "PGHOST is not set: no server to run against"; return 0
  let cfg ← Postgres.Client.fromEnv
  let setup ← (do
    let .ok s ← Postgres.connect cfg | throw (IO.userError "cannot connect")
    discard <| s.exec (.statement table.create)
    discard <| s.exec (.statement { sql := s!"DELETE FROM {table.name}" })
    s.close : Async Unit).block
  discard <| pure setup
  let sessions ← IO.mkRef []
  let outs ← IO.mkRef ([] : List Out)
  let run : Async (List (Nat × String)) := do
    let rt ← Runtime.startWith (system { keyed := true }) {} fun rt _ out => do
      outs.modify (· ++ [out])
      Postgres.Store.handler port cfg table .serializable sessions rt out
    for (key, title) in [(1, "milk"), (2, "eggs"), (1, "milk"), (3, "bread")] do
      rt.input (.add key title)
    for _ in List.range 100 do
      let done := (← outs.get).countP fun | .added _ | .gaveUp _ => true | _ => false
      if done ≥ 4 then break
      Std.Async.sleep (.ofNat 50)
    rt.stop
    let .ok s ← Postgres.connect cfg | throw (IO.userError "cannot connect")
    let rows ← s.exec (.statement { sql := s!"SELECT key, value FROM {table.name} ORDER BY key" })
    s.close
    match rows with
    | .rows r => return r.rows.filterMap fun
        | [some k, some v] => k.toNat?.map (·, v)
        | _ => none
    | _ => return []
  let rows ← run.block
  for (k, v) in rows do IO.println s!"{k} {v}"
  let outcomes := (← outs.get).filterMap fun
    | .added k => some s!"added {k}"
    | .gaveUp k => some s!"gave up {k}"
    | _ => none
  IO.println s!"{", ".intercalate outcomes}"
  return if rows == [(1, "milk"), (2, "eggs"), (3, "bread")] then 0 else 1
