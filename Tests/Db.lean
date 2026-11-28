/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Lanes.Services.Postgres

/-!
The typed store without a server: what the operations mean on small tables (`Op.apply`), the SQL
they are sent as (`Postgres.Sql.statement`, `Postgres.Sql.create`), what a reply means
(`Postgres.Sql.classify`, `Postgres.Sql.committed`), when the driver tries again
(`Retry.next`), and the runs the model allows and refuses (`Db.State.run`): a lost `COMMIT`
that took effect or not, or takes effect later; a failed call that never does; an answer that
no order of the calls gives. `Tests/Oracle/Service/Db.lean` compares the same with PostgreSQL.
-/

namespace Tests.Db

open Lanes.Db
open Lanes (Signature)

def kv : Table :=
  { name := "kv", key := 1,
    columns := [{ name := "k", ty := .int }, { name := "v", ty := .text }, { name := "n", ty := .int, nullable := true }],
    indexes := [{ name := "by_v", columns := [1], unique := true }] }

def row (k : Int64) (v : String) (n : Option Int64 := none) : Row :=
  [.int k, .text v, (n.map Value.int).getD .null]

/-- Apply operations in order, from the empty table; the answers, rendered. -/
def answers (ops : List Op) : List String :=
  let step := fun (acc : List String × Db) (o : Op) =>
    match o.apply acc.2 with
    | .ok (r, db) =>
      let shown := match o, r with
        | .get .., (r : Option Row) => s!"{repr r}"
        | .scan _, (rs : List Row) => s!"{repr rs}"
        | .insert .., (b : Bool) | .update .., (b : Bool) | .upsert .., (b : Bool) | .delete .., (b : Bool) => s!"{b}"
      (acc.1 ++ [shown], db)
    | .error _ => (acc.1 ++ ["error"], acc.2)
  (ops.foldl step ([], Db.empty [kv])).1

def scanAll (order : Order := .asc) (limit : Nat := 10) : Op := .scan { table := kv, order, limit }

def meaningTests : List (String × Bool) :=
  let writes := [Op.insert kv (row 2 "b"), .insert kv (row 1 "a" (some 5)), .insert kv (row 2 "c"),
    .insert kv (row 3 "a"), .update kv (row 4 "d"), .update kv (row 2 "a"), .upsert kv (row 3 "c"),
    .upsert kv (row 2 "bb"), scanAll, scanAll .desc 2, .delete kv [.int 9], .delete kv [.int 1],
    .get kv [.int 1], .get kv [.int 2]]
  let got := answers writes
  [ ("typed store: an insert of a key taken, or of a unique value taken, does nothing",
      got.take 4 == ["true", "true", "false", "false"]),
    ("typed store: an update of a missing key, or onto a unique value taken, does nothing",
      (got.drop 4).take 2 == ["false", "false"]),
    ("typed store: an upsert inserts or replaces",
      (got.drop 6).take 2 == ["true", "true"]),
    ("typed store: a scan is in key order, and in reverse with a limit",
      (got.drop 8).take 2 == [s!"{repr [row 1 "a" (some 5), row 2 "bb", row 3 "c"]}", s!"{repr [row 3 "c", row 2 "bb"]}"]),
    ("typed store: a delete says whether there was a row, and a get finds it or not",
      got.drop 10 == ["false", "true", "none", s!"{repr (some (row 2 "bb"))}"]),
    ("typed store: a value of the wrong type, a NULL key, NUL in text and a limit too large are errors",
      answers [.insert kv [.text "x", .text "a", .null], .insert kv [.null, .text "a", .null],
        .insert kv (row 1 "a\x00"), scanAll (limit := Scan.limit_max + 1)] == ["error", "error", "error", "error"]),
    ("typed store: a scan by an index, with equality and a range",
      (answers [.insert kv (row 1 "b"), .insert kv (row 2 "a"), .insert kv (row 3 "c"),
        .scan { table := kv, index := kv.indexes[0]?, lower := some { value := .text "a", inclusive := false }, limit := 5 }]).getLast?
        == some s!"{repr [row 1 "b", row 3 "c"]}") ]

def sqlTests : List (String × Bool) :=
  let ins := Lanes.Postgres.Sql.statement (.insert kv (row 1 "a" (some (-5))))
  let upd := Lanes.Postgres.Sql.statement (.update kv (row 1 "a"))
  let scan := Lanes.Postgres.Sql.statement (.scan { table := kv, eq := [.int 1], order := .desc, limit := 3 })
  [ ("typed store sql: an insert", ins.sql ==
      "INSERT INTO \"kv\" (\"k\", \"v\", \"n\") VALUES ($1::bigint, $2::text, $3::bigint) ON CONFLICT DO NOTHING RETURNING 1"
      && ins.params == [some "1", some "a", some "-5"]),
    ("typed store sql: an update checks the unique index", upd.sql ==
      "UPDATE \"kv\" SET \"v\" = $1::text, \"n\" = $2::bigint WHERE \"k\" = $3::bigint AND NOT EXISTS (SELECT 1 FROM \"kv\" AS o WHERE NOT (o.\"k\" = $4::bigint) AND ((o.\"v\" = $5::text))) RETURNING 1"
      && upd.params == [some "a", none, some "1", some "1", some "a"]),
    ("typed store sql: a scan", scan.sql ==
      "SELECT \"k\", \"v\", \"n\" FROM \"kv\" WHERE \"k\" = $1::bigint ORDER BY \"k\" DESC, \"k\" DESC LIMIT 3"),
    ("typed store sql: the table and its index", (Lanes.Postgres.Sql.create kv).map (·.sql) ==
      ["CREATE TABLE \"kv\" (\"k\" bigint NOT NULL, \"v\" text COLLATE \"C\" NOT NULL, \"n\" bigint, PRIMARY KEY (\"k\"))",
       "CREATE UNIQUE INDEX \"kv_by_v\" ON \"kv\" (\"v\")"]),
    ("typed store sql: bytes and booleans in text, and back",
      Lanes.Postgres.Sql.param (.bytes ⟨#[0, 255]⟩) == some "\\x00ff"
        && Lanes.Postgres.Sql.decode { name := "b", ty := .bytes } (some "\\x00ff") == some (.bytes ⟨#[0, 255]⟩)
        && Lanes.Postgres.Sql.decode { name := "f", ty := .bool } (some "t") == some (.bool true)
        && Lanes.Postgres.Sql.decode { name := "i", ty := .int } (some "9223372036854775808") == none),
    ("typed store migrations: a file's statements end at a line ending with a semicolon",
      Lanes.Postgres.Sql.statements "-- kv\nCREATE TABLE kv (\n  k bigint\n);\n\nCREATE INDEX i ON kv (k);\n"
        == ["CREATE TABLE kv (\nk bigint\n);", "CREATE INDEX i ON kv (k);"]),
    ("typed store migrations: the catalog the schema expects agrees with it, and a column missing is named",
      Lanes.Postgres.Sql.catalogDiff [kv] (Lanes.Postgres.Sql.expectedColumns [kv]) (Lanes.Postgres.Sql.expectedKeys [kv]) == []
        && Lanes.Postgres.Sql.catalogDiff [kv] ((Lanes.Postgres.Sql.expectedColumns [kv]).take 2) (Lanes.Postgres.Sql.expectedKeys [kv])
          == ["column missing: kv, n, bigint, YES, NULL"]) ]

def retryTests : List (String × Bool) :=
  let fields (code : String) : List Lanes.Postgres.Field := [{ code := 'C'.toNat.toUInt8, value := code }]
  [ ("typed store retry: serialization failures and deadlocks are conflicts, other errors are not",
      Lanes.Postgres.Sql.classify (.error (fields "40001")) == .conflict
        && Lanes.Postgres.Sql.classify (.error (fields "40P01")) == .conflict
        && Lanes.Postgres.Sql.classify (.error (fields "22012")) == .error "22012"),
    ("typed store retry: a COMMIT whose reply is lost is unknown",
      Lanes.Postgres.Sql.committed () .unknown == .unknown
        && Lanes.Postgres.Sql.committed () (.error (fields "40001")) == .conflict),
    ("typed store retry: a conflict is tried again until the last attempt, a lost COMMIT never",
      Retry.next (A := Unit) 3 0 .conflict == none && Retry.next (A := Unit) 3 2 .conflict == some (.failed .conflict)
        && Retry.next (A := Unit) 3 0 .unknown == some .unknown && Retry.next (A := Unit) 3 1 .dropped == none) ]

/-! ## The model -/

/-- A counter: each call adds one to row 0, and answers the value it read. -/
def counter : Table := { name := "counter", key := 1, columns := [{ name := "k", ty := .int }, { name := "n", ty := .int }] }

def bump : Handler Unit Int64 := fun _ => do
  let n ← match ← Txn.get counter [.int 0] with
    | some [_, .int n] => pure n
    | _ => pure 0
  discard <| Txn.upsert counter [.int 0, .int (n + 1)]
  pure n

abbrev Event := Call Unit ⊕ Reply Int64

def call (id : Nat) : Event := .inl { id, request := () }
def reply (id : Nat) (r : Result Int64) : Event := .inr { id, result := r }

def allows (events : List Event) : Bool :=
  (({ worlds := [{ db := Db.empty [counter] }] } : State Unit Int64).run {} bump events).isSome

def modelTests : List (String × Bool) :=
  [ ("typed store model: calls one after another read what the earlier wrote",
      allows [call 0, reply 0 (.committed 0), call 1, reply 1 (.committed 1)]
        && !allows [call 0, reply 0 (.committed 0), call 1, reply 1 (.committed 0)]),
    ("typed store model: a lost COMMIT may have taken effect or not",
      allows [call 0, reply 0 .unknown, call 1, reply 1 (.committed 1)]
        && allows [call 0, reply 0 .unknown, call 1, reply 1 (.committed 0)]),
    ("typed store model: and may take effect later",
      allows [call 0, reply 0 .unknown, call 1, reply 1 (.committed 0), call 2, reply 2 (.committed 2)]),
    ("typed store model: a failed call never took effect",
      !allows [call 0, reply 0 (.failed .conflict), call 1, reply 1 (.committed 1)]),
    ("typed store model: calls at once take effect in either order, but each once",
      allows [call 0, call 1, reply 1 (.committed 0), reply 0 (.committed 1)]
        && !allows [call 0, call 1, reply 0 (.committed 0), reply 1 (.committed 0)]) ]

def tests : List (String × Bool) := meaningTests ++ sqlTests ++ retryTests ++ modelTests

end Tests.Db
