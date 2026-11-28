/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Services.Postgres.IO.Pool
public import Lanes.Services.Postgres.Sql
public import Lanes.Db.Model

/-!
The IO of the typed store on PostgreSQL: a call runs its handler's transaction in attempts, each
`BEGIN ISOLATION LEVEL SERIALIZABLE`, one statement per operation, `COMMIT`, on a connection of
the pool. It decides nothing (rule 3.9): the SQL of an operation and what its reply means are
`Lanes/Services/Postgres/Sql.lean`'s, whether an operation may be sent is `Op.valid`, and whether to
try again is `Retry.next`'s (`Lanes/Db/Retry.lean`). An attempt that did not commit on a
connection still open is rolled back before the connection goes back to the pool.

`Db.handler` runs calls for a system, as the adapter of `Lanes/Db/Model.lean`'s port: each call
on a task of its own, its result handed back as an input.
-/

public section

namespace Lanes.Postgres.Typed

open Std Std.Async Lanes.Db

structure Store (Q A : Type) where
  pool : Pool
  handler : Handler Q A
  /-- Attempts of one call, the first included (rule 2.6). -/
  attempts_max : Nat := 5
  /-- How long a call waits for a connection of the pool. -/
  checkout_ms : Nat := 10000

/-- Run the transaction's operations on the session, inside its open transaction. -/
def operations {α : Type} (s : Session) : Txn α → Async (Except (Attempt α) α)
  | .pure a => pure (.ok a)
  | .abort why => pure (.error (.aborted why))
  | .op o k => do
    if !o.valid then return .error (.aborted s!"an operation on {o.table.name} that the schema does not admit")
    match Sql.classify (← s.exec (.statement (Sql.statement o))) with
    | .rows rows =>
      match Sql.answer o rows with
      | some r => operations s (k r)
      | none => return .error (.error "")
    | .conflict => return .error .conflict
    | .dropped => return .error .dropped
    | .error code => return .error (.error code)

/-- One attempt on the session. -/
def attempt {α : Type} (s : Session) (t : Txn α) : Async (Attempt α) := do
  match Sql.classify (← s.exec (.begin .serializable)) with
  | .rows _ =>
    match ← operations s t with
    | .ok a => return Sql.committed a (← s.exec .commit)
    | .error stop =>
      unless stop matches .dropped do discard <| s.exec .rollback
      return stop
  | .conflict => return .conflict
  | .dropped => return .dropped
  | .error code => return .error code

def Store.attemptOnPool {Q A : Type} (st : Store Q A) (q : Q) : Async (Attempt A) := do
  match ← st.pool.withSession st.checkout_ms (fun s => attempt s (st.handler q)) with
  | .ok a => return a
  | .error _ => return .dropped

/-- Run a call to its result, trying again as `Retry.next` says. -/
def Store.call {Q A : Type} (st : Store Q A) (q : Q) : Async (Result A) := do
  for n in [0:st.attempts_max] do
    let a ← try st.attemptOnPool q catch _ => pure .dropped
    if let some r := Retry.next st.attempts_max n a then return r
  return .failed .unavailable

/-- Create the schema's tables and indexes, each statement on its own; the errors, if any. -/
def create (s : Session) (schema : Schema) : Async (List String) := do
  let mut errors := []
  for t in schema do
    for stmt in Sql.create t do
      match ← s.exec (.statement stmt) with
      | .rows _ => pure ()
      | other => errors := errors ++ [s!"{stmt.sql}: {repr other}"]
  return errors

/-- Run migrations, each the text of a file, in order, statement by statement
(`Postgres.Sql.statements`); the errors, stopping at the first. -/
def migrate (s : Session) (files : List String) : Async (List String) := do
  for file in files do
    for sql in Sql.statements file do
      match ← s.exec (.statement { sql }) with
      | .rows _ => pure ()
      | other => return [s!"{sql}: {repr other}"]
  return []

/-- The key of the advisory lock `migrateOnce` takes: any number, the same in every instance. -/
def migrationsLock : Nat := 7406223

/-- Run the migrations that `lanes_migrations` does not record, each a file's name and text, in
the order of their names, and record them. It is one transaction under an advisory lock, so that
instances started at once run each migration once, and a migration that fails leaves nothing of
the run. The errors, if any. -/
def migrateOnce (s : Session) (files : List (String × String)) : Async (List String) := do
  let exec := fun (sql : String) (params : List (Option String)) => s.exec (.statement { sql, params })
  let fail := fun (what : String) (r : Reply) => do
    discard <| s.exec .rollback
    return [s!"{what}: {repr r}"]
  match ← s.exec (.begin .readCommitted) with
  | .rows _ => pure ()
  | r => return [s!"BEGIN: {repr r}"]
  for sql in [s!"SELECT pg_advisory_xact_lock({migrationsLock})", Sql.migrationsCreate] do
    match ← exec sql [] with
    | .rows _ => pure ()
    | r => return (← fail sql r)
  let applied ← match ← exec s!"SELECT name FROM {Sql.migrationsTable}" [] with
    | .rows r => pure (r.rows.filterMap fun row => row.head?.join)
    | r => return (← fail "the migrations run" r)
  for (name, text) in Sql.pending applied files do
    for sql in Sql.statements text do
      match ← exec sql [] with
      | .rows _ => pure ()
      | r => return (← fail s!"{name}: {sql}" r)
    match ← exec s!"INSERT INTO {Sql.migrationsTable} (name) VALUES ($1)" [some name] with
    | .rows _ => pure ()
    | r => return (← fail name r)
  match ← s.exec .commit with
  | .committed => return []
  | r => return [s!"COMMIT: {repr r}"]

/-- The migrations of a directory: each `.sql` file's name and text. -/
def readMigrations (dir : System.FilePath) : IO (List (String × String)) := do
  let files := (← dir.readDir).toList.filter (·.fileName.endsWith ".sql")
  files.mapM fun e => return (e.fileName, ← IO.FS.readFile e.path)

/-- How the tables of the session's current schema differ from `schema`
(`Postgres.Sql.catalogDiff`); empty when they agree. -/
def checkSchema (s : Session) (schema : Schema) : Async (List String) := do
  match ← s.exec (.statement Sql.columnsQuery), ← s.exec (.statement Sql.keysQuery) with
  | .rows columns, .rows keys => return Sql.catalogDiff schema columns.rows keys.rows
  | a, b => return [s!"the catalog: {repr a}, {repr b}"]

/-- How the tables `schema` names differ from the database's (`Postgres.Sql.tablesDiff`). -/
def checkTables (s : Session) (schema : Schema) : Async (List String) := do
  match ← s.exec (.statement Sql.columnsQuery), ← s.exec (.statement Sql.keysQuery) with
  | .rows columns, .rows keys => return Sql.tablesDiff schema columns.rows keys.rows
  | a, b => return [s!"the catalog: {repr a}, {repr b}"]

/-- What an application does before it serves: run the migrations not yet run
(`migrateOnce`), then compare the tables `schema` declares with the database's
(`checkTables`). The problems, if any. An application refuses to start on any, rather than run
its transactions on tables they were not written for. -/
def prepare (cfg : Client.Config) (schema : Schema) (files : List (String × String)) :
    Async (List String) := do
  match ← connect cfg with
  | .error _ => return [s!"cannot connect to PostgreSQL at {cfg.host}:{cfg.port}"]
  | .ok s =>
    let errors ← migrateOnce s files
    let diff ← if errors.isEmpty then checkTables s schema else pure []
    s.close
    return errors ++ diff

/-- For tests: drop the schema's tables and forget the migrations named, so that `prepare` runs
them again on tables that hold nothing. -/
def reset (cfg : Client.Config) (schema : Schema) (names : List String) : Async (List String) := do
  match ← connect cfg with
  | .error _ => return [s!"cannot connect to PostgreSQL at {cfg.host}:{cfg.port}"]
  | .ok s =>
    let drops := schema.map fun t => (s!"DROP TABLE IF EXISTS {Sql.quote t.name} CASCADE", [])
    let forget := names.map fun n => (s!"DELETE FROM {Sql.migrationsTable} WHERE name = $1", [some n])
    let mut errors := []
    for (sql, params) in drops ++ [(Sql.migrationsCreate, [])] ++ forget do
      match ← s.exec (.statement { sql, params }) with
      | .rows _ => pure ()
      | r => errors := errors ++ [s!"{sql}: {repr r}"]
    s.close
    return errors

/-- The store as an adapter: each call on a task of its own, its result handed back as an input.
A result that finds the inbox full is dropped, which the model allows as a lost answer. -/
def handler {σ : Signature} {sys : System σ} [Hashable σ.Id] {Q A : Type}
    (port : Db.Port σ Q A) (st : Store Q A) (rt : Runtime sys) (out : σ.Out) : Async Unit := do
  if let some c := port.call out then
    background do
      let result ← try st.call c.request catch _ => pure .unknown
      discard <| rt.tryInput (port.reply { id := c.id, result })

end Lanes.Postgres.Typed
