/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Oracle.Service.Basic
import Tests.PostgresLive
import Lanes.Lib.Postgres.IO.Db

/-!
The typed store against a real PostgreSQL (`oracles/postgres`): transactions generated at random
over two tables that use every column type, nullable columns, a composite primary key, and a
unique and a non-unique index, run through the driver (`Lanes/Lib/Postgres/IO/Db.lean`).

- **One call at a time**, every answer is compared with the Lean meaning (`Txn.run`) on the
  database the earlier calls left, and a last call reads every row of both tables, so the two
  databases are compared too.
- **Three calls at once**, on the same few keys, so that PostgreSQL meets serialization failures
  and the driver retries; the run is checked against the model (`State.run`, what
  `Db.outside` allows).

Each run is kept in `oracles/postgres/db.jsonl`, one run a line, and `lake test` checks the
record against the model again.

A call is a list of steps (`Step`), each an operation of the query subset or `bump`, which reads
a row and writes what depends on what it read.
-/

namespace Tests.Oracle.Service.Typed

open Lanes.Db
open Lanes (Json)

/-! ## The schema and the calls -/

def items : Table :=
  { name := "lanes_items", key := 1,
    columns := [{ name := "id", ty := .int }, { name := "tag", ty := .text },
      { name := "owner", ty := .int }, { name := "data", ty := .bytes, nullable := true },
      { name := "flag", ty := .bool, nullable := true }, { name := "note", ty := .text, nullable := true }],
    indexes := [{ name := "by_owner", columns := [2, 1] }, { name := "by_tag", columns := [1], unique := true }] }

def pairs : Table :=
  { name := "lanes_pairs", key := 2,
    columns := [{ name := "a", ty := .int }, { name := "b", ty := .text }, { name := "v", ty := .int, nullable := true }] }

def schema : Schema := [items, pairs]

def table (n : Nat) : Table := if n == 0 then items else pairs

inductive Step where
  | get (tbl : Nat) (key : Row)
  | scan (tbl : Nat) (index : Option Nat) (eq : Row) (lower upper : Option Bound) (desc : Bool) (limit : Nat)
  | insert (tbl : Nat) (row : Row)
  | update (tbl : Nat) (row : Row)
  | upsert (tbl : Nat) (row : Row)
  | delete (tbl : Nat) (key : Row)
  /-- Read the item `id`: flip its flag if it is there, insert it if not. -/
  | bump (id : Int64)
  deriving DecidableEq, Repr

def Step.scanOf (tbl : Nat) (index : Option Nat) (eq : Row) (lower upper : Option Bound) (desc : Bool)
    (limit : Nat) : Scan :=
  { table := table tbl, index := index.bind fun n => (table tbl).indexes[n]?, eq, lower, upper,
    order := if desc then .desc else .asc, limit }

inductive Out where
  | row (r : Option Row)
  | rows (rs : List Row)
  | flag (b : Bool)
  deriving DecidableEq, Repr

def Step.run : Step → Txn Out
  | .get t k => .row <$> Txn.get (table t) k
  | .scan t i eq lo hi desc limit => .rows <$> Txn.scan (Step.scanOf t i eq lo hi desc limit)
  | .insert t r => .flag <$> Txn.insert (table t) r
  | .update t r => .flag <$> Txn.update (table t) r
  | .upsert t r => .flag <$> Txn.upsert (table t) r
  | .delete t k => .flag <$> Txn.delete (table t) k
  | .bump id => do
    match ← Txn.get items [.int id] with
    | some r =>
      let flag := match r[4]? with
        | some (Value.bool b) => !b
        | _ => true
      .flag <$> Txn.update items (r.set 4 (.bool flag))
    | none => .flag <$> Txn.insert items [.int id, .text s!"b{id}", .int 0, .null, .null, .null]

def handler : Handler (List Step) (List Out) := fun steps => steps.mapM Step.run

/-! ## Calls at random -/

structure Gen where
  gen : IO.Ref StdGen

def Gen.below (g : Gen) (n : Nat) : IO Nat := g.gen.modifyGet fun s => let (x, s) := randNat s 0 (n - 1); (x, s)

def Gen.pick {α : Type} [Inhabited α] (g : Gen) (xs : List α) : IO α := do return xs[← g.below xs.length]!

def ints : List Int64 := [0, 1, 2, 3, -1, 9223372036854775807, -9223372036854775808]
def texts : List String := ["a", "b", "ab", "", "é", "Z", "a b"]
def blobs : List ByteArray := [.empty, ⟨#[0]⟩, ⟨#[255, 1]⟩, ⟨#[0, 0]⟩]

def Gen.key (g : Gen) : IO Int64 := do return Int64.ofNat (← g.below 4)
def Gen.int (g : Gen) : IO Value := do return .int (← g.pick ints)
def Gen.text (g : Gen) : IO Value := do return .text (← g.pick texts)
def Gen.small (g : Gen) : IO Value := do return .int (Int64.ofNat (← g.below 3))
def Gen.maybe (g : Gen) (v : IO Value) : IO Value := do if (← g.below 3) == 0 then return .null else v

def Gen.item (g : Gen) : IO Row := do
  return [.int (← g.key), ← g.text, ← g.small, ← g.maybe (do return .bytes (← g.pick blobs)),
    ← g.maybe (do return .bool ((← g.below 2) == 0)), ← g.maybe g.text]

def Gen.pair (g : Gen) : IO Row := do return [← g.small, ← g.pick [Value.text "a", .text "b", .text "c"], ← g.maybe g.int]

def Gen.row (g : Gen) (tbl : Nat) : IO Row := if tbl == 0 then g.item else g.pair

def Gen.bound (g : Gen) (v : IO Value) : IO (Option Bound) := do
  if (← g.below 2) == 0 then return none
  return some { value := ← v, inclusive := (← g.below 2) == 0 }

def Gen.step (g : Gen) : IO Step := do
  let tbl ← g.below 2
  let row ← g.row tbl
  let key := row.take (table tbl).key
  match ← g.below 9 with
  | 0 => return .get tbl key
  | 1 | 2 =>
    let index ← if tbl == 0 then g.pick [none, some 0, some 1] else pure none
    let cols := (Step.scanOf tbl index [] none none false 0).columns
    let n ← g.below (cols.length + 1)
    let eq := (cols.take n).map (row.getD · .null)
    let next := cols[n]?.map (row.getD · .null)
    let near : IO Value := match next with
      | some (.int _) => do if (← g.below 2) == 0 then g.small else g.int
      | some (.text _) => g.text
      | _ => g.small
    return .scan tbl index eq (← g.bound near) (← g.bound near) ((← g.below 2) == 0) (← g.below 5)
  | 3 => return .insert tbl row
  | 4 => return .update tbl row
  | 5 => return .upsert tbl row
  | 6 => return .delete tbl key
  | 7 => return .bump (← g.key)
  | _ =>
    -- Now and then a step the schema does not admit, which aborts the call.
    if (← g.below 4) == 0 then return .insert 0 (row.set 1 .null) else return .bump (← g.key)

def Gen.call (g : Gen) : IO (List Step) := do
  let n := (← g.below 4) + 1
  (List.range n).mapM fun _ => g.step

/-! ## A run, as JSON -/

def valueJson : Value → Json
  | .null => .null
  | .int i => Json.mkObj [("i", toString i.toInt)]
  | .bytes b => Json.mkObj [("b", Lanes.Bytes.hex b)]
  | .text s => Json.mkObj [("t", s)]
  | .bool b => .bool b

def readValue (j : Json) : Option Value :=
  match j with
  | .null => some .null
  | .bool b => some (.bool b)
  | _ =>
    match str? j "i", str? j "b", str? j "t" with
    | some i, _, _ => (Lanes.Postgres.Sql.decodeInt i).map .int
    | none, some b, _ => (Lanes.Bytes.unhex? b).map .bytes
    | none, none, some t => some (.text t)
    | _, _, _ => none

def rowJson (r : Row) : Json := .arr (r.map valueJson).toArray

def readRow (j : Json) : Option Row := do (← j.getArr?.toOption).toList.mapM readValue

def boundJson : Option Bound → Json
  | none => .null
  | some b => Json.mkObj [("v", valueJson b.value), ("inclusive", b.inclusive)]

def readBound (j : Json) : Option (Option Bound) :=
  match j with
  | .null => some none
  | _ => do
    let v ← readValue (← (j.getObjVal? "v").toOption)
    return some { value := v, inclusive := ← (j.getObjVal? "inclusive" >>= Json.getBool?).toOption }

def stepJson : Step → Json
  | .get t k => Json.mkObj [("op", "get"), ("table", t), ("key", rowJson k)]
  | .scan t i eq lo hi desc limit => Json.mkObj [("op", "scan"), ("table", t),
      ("index", (i.map fun n => Json.num n).getD .null), ("eq", rowJson eq), ("lower", boundJson lo),
      ("upper", boundJson hi), ("desc", desc), ("limit", limit)]
  | .insert t r => Json.mkObj [("op", "insert"), ("table", t), ("row", rowJson r)]
  | .update t r => Json.mkObj [("op", "update"), ("table", t), ("row", rowJson r)]
  | .upsert t r => Json.mkObj [("op", "upsert"), ("table", t), ("row", rowJson r)]
  | .delete t k => Json.mkObj [("op", "delete"), ("table", t), ("key", rowJson k)]
  | .bump id => Json.mkObj [("op", "bump"), ("id", toString id.toInt)]

def readStep (j : Json) : Option Step := do
  let row (name : String) : Option Row := (j.getObjVal? name).toOption >>= readRow
  let t := (nat? j "table").getD 0
  match ← str? j "op" with
  | "get" => return .get t (← row "key")
  | "scan" =>
    let index ← match j.getObjVal? "index" with
      | .ok .null => some none
      | .ok n => (n.getNat?.toOption).map some
      | .error _ => none
    return .scan t index (← row "eq") (← (j.getObjVal? "lower").toOption >>= readBound)
      (← (j.getObjVal? "upper").toOption >>= readBound) (← (j.getObjVal? "desc" >>= Json.getBool?).toOption)
      (← nat? j "limit")
  | "insert" => return .insert t (← row "row")
  | "update" => return .update t (← row "row")
  | "upsert" => return .upsert t (← row "row")
  | "delete" => return .delete t (← row "key")
  | "bump" => return .bump (← Lanes.Postgres.Sql.decodeInt (← str? j "id"))
  | _ => none

def outJson : Out → Json
  | .row r => Json.mkObj [("row", (r.map rowJson).getD .null)]
  | .rows rs => Json.mkObj [("rows", .arr (rs.map rowJson).toArray)]
  | .flag b => Json.mkObj [("flag", b)]

def readOut (j : Json) : Option Out :=
  match j.getObjVal? "row", j.getObjVal? "rows", j.getObjVal? "flag" with
  | .ok .null, _, _ => some (.row none)
  | .ok r, _, _ => (readRow r).map (.row ∘ some)
  | _, .ok rs, _ => do return .rows (← (← rs.getArr?.toOption).toList.mapM readRow)
  | _, _, .ok (.bool b) => some (.flag b)
  | _, _, _ => none

abbrev Event := Call (List Step) ⊕ Reply (List Out)

def resultJson : Result (List Out) → Json
  | .committed outs => Json.mkObj [("committed", .arr (outs.map outJson).toArray)]
  | .failed why => Json.mkObj [("failed", toString (repr why))]
  | .unknown => Json.mkObj [("unknown", true)]

def readResult (j : Json) : Option (Result (List Out)) :=
  match j.getObjVal? "committed", j.getObjVal? "failed", j.getObjVal? "unknown" with
  | .ok outs, _, _ => do return .committed (← (← outs.getArr?.toOption).toList.mapM readOut)
  | _, .ok _, _ => some (.failed .unavailable)
  | _, _, .ok _ => some .unknown
  | _, _, _ => none

def eventJson : Event → Json
  | .inl c => Json.mkObj [("call", c.id), ("steps", .arr (c.request.map stepJson).toArray)]
  | .inr r => Json.mkObj [("reply", r.id), ("result", resultJson r.result)]

def readEvent (j : Json) : Option Event :=
  match nat? j "call", nat? j "reply" with
  | some id, _ => do return .inl { id, request := ← (← (j.getObjVal? "steps" >>= Json.getArr?).toOption).toList.mapM readStep }
  | none, some id => do return .inr { id, result := ← readResult (← (j.getObjVal? "result").toOption) }
  | none, none => none

def runJson (name : String) (events : List Event) : Json :=
  Json.mkObj [("run", name), ("events", .arr (events.map eventJson).toArray)]

def model : Config := { calls_max := 4 }

/-- Whether the model allows the run, from the empty tables. -/
def allows (events : List Event) : Bool :=
  (({ worlds := [{ db := Db.empty schema }] } : State (List Step) (List Out)).run model handler events).isSome

/-! ## Against PostgreSQL -/

def reset (cfg : Lanes.Postgres.Client.Config) : IO (List String) := do
  let .ok s ← (Lanes.Postgres.connect cfg).block | throw (IO.userError "no connection")
  for t in schema do
    discard <| (s.exec (.statement { sql := s!"DROP TABLE IF EXISTS {Lanes.Postgres.Sql.quote t.name}" })).block
  let errors ← (Lanes.Postgres.Typed.create s schema).block
  (s.close).block
  return errors

/-- One call at a time, each answer compared with the meaning; the run, and the calls whose
answers differ. -/
def sequential (st : Lanes.Postgres.Typed.Store (List Step) (List Out)) (seed calls : Nat) :
    IO (List Event × List String) := do
  let g : Gen := { gen := ← IO.mkRef (mkStdGen seed) }
  let mut db := Db.empty schema
  let mut events : List Event := []
  let mut wrong : List String := []
  let everything := [Step.scan 0 none [] none none false 100, .scan 1 none [] none none false 100]
  for id in [0:calls + 1] do
    let steps ← if id == calls then pure everything else g.call
    let result ← (st.call steps).block
    events := events ++ [.inl { id, request := steps }, .inr { id, result }]
    match (handler steps).run db, result with
    | .ok (outs, db'), .committed outs' =>
      if outs == outs' then db := db' else wrong := wrong ++ [s!"{repr steps}: {repr outs'}, not {repr outs}"]
    | .error _, .failed (.aborted _) => pure ()
    | expected, _ => wrong := wrong ++ [s!"{repr steps}: {repr result}, not {repr (expected.map (·.1))}"]
  return (events, wrong)

/-- Rounds of three calls at once on the same few keys. -/
def concurrent (st : Lanes.Postgres.Typed.Store (List Step) (List Out)) (seed rounds : Nat) : IO (List Event) := do
  let g : Gen := { gen := ← IO.mkRef (mkStdGen seed) }
  let events ← IO.mkRef ([] : List Event)
  for round in [0:rounds] do
    let tasks ← (List.range 3).mapM fun k => do
      let id := round * 3 + k
      let steps ← g.call
      events.modify (· ++ [.inl { id, request := steps }])
      IO.asTask do
        let result ← (st.call steps).block
        events.modify (· ++ [.inr { id, result }])
    for t in tasks do discard <| IO.wait t
  events.get

def run (host : String) (tcpPort : UInt16) : IO (List (String × Bool) × List Json) := do
  let cfg := Tests.PostgresLive.config host tcpPort "lanes_trust" none
  let errors ← reset cfg
  unless errors.isEmpty do
    return ([(s!"typed store on postgres: the schema is created: {errors}", false)], [])
  let st : Lanes.Postgres.Typed.Store (List Step) (List Out) := { pool := ← Lanes.Postgres.Pool.new cfg, handler, attempts_max := 20 }
  let mut checks := []
  let mut lines := []
  for seed in [0:20] do
    discard <| reset cfg
    let (events, wrong) ← sequential st seed 25
    for w in wrong do IO.println s!"  differs: {w}"
    checks := checks ++ [(s!"typed store on postgres, one call at a time, seed {seed}: every answer is the meaning's", wrong.isEmpty),
      (s!"typed store on postgres, one call at a time, seed {seed}: the model allows the run", allows events)]
    lines := lines ++ [runJson s!"one at a time, seed {seed}" events]
  for seed in [0:10] do
    discard <| reset cfg
    let events ← concurrent st seed 8
    let ok := allows events
    unless ok do IO.println s!"  not allowed: {(runJson "" events).compress}"
    let committed := events.countP fun | .inr { result := .committed _, .. } => true | _ => false
    checks := checks ++ [(s!"typed store on postgres, three at once, seed {seed}: {committed} committed, and the model allows the run", ok)]
    lines := lines ++ [runJson s!"three at once, seed {seed}" events]
  return (checks, lines)

def readRun (j : Json) : Option (String × List Event) := do
  let lines ← (j.getObjVal? "events" >>= Json.getArr?).toOption
  return (← str? j "run", ← lines.toList.mapM readEvent)

def replay (lines : List Json) : List (String × Bool) :=
  let read := lines.filterMap readRun
  [ (s!"typed store on postgres, recorded: {read.length} runs read", read.length == lines.length && !lines.isEmpty),
    ("typed store on postgres, recorded: every run is one the model allows", read.all fun (_, events) => allows events) ]

def oracle : Oracle where
  name := "db"
  reference := "postgres"
  envVar := "LANES_POSTGRES"
  live := run
  replay := replay

end Tests.Oracle.Service.Typed
