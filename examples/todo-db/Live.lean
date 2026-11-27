/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import TodoDb

/-!
The fixed to-do list on a real PostgreSQL, through the client's store adapter
(`Postgres.Store.handler`): `LANES_POSTGRES=host:port` names a server set up by
`scripts/postgres-test-server`, and the to-dos go in the table `todo_db` of `lanes_test`, as
`lanes_scram`. It adds three to-dos, one of them twice under the same key, and prints the rows.
Without `LANES_POSTGRES` it says so and exits.
-/

open Lanes TodoDb Std.Async

def table : Postgres.Table := { name := "todo_db" }

def main : IO UInt32 := do
  let some spec ← IO.getEnv "LANES_POSTGRES"
    | IO.println "LANES_POSTGRES is not set: no server to run against"; return 0
  let [host, portText] := spec.splitOn ":" | IO.println "LANES_POSTGRES is host:port"; return 2
  let cfg : Postgres.Client.Config :=
    { host, port := portText.toNat!.toUInt16, sslmode := .disable
      conn := { user := "lanes_scram", database := "lanes_test", password := some "scram-pw" } }
  let setup ← (do
    let .ok s ← Postgres.connect cfg | throw (IO.userError "cannot connect")
    discard <| s.exec (.statement table.create)
    discard <| s.exec (.statement { sql := s!"DELETE FROM {table.name}" })
    s.close : Async Unit).block
  discard <| pure setup
  let sessions ← IO.mkRef []
  let outs ← IO.mkRef ([] : List Out)
  let run : Async (List (Nat × String)) := do
    let rt ← Runtime.startWith (system { keyed := true }) {} fun rt out => do
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
