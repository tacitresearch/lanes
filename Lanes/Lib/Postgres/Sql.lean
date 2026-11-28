/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Lib.Postgres.Conn
public import Lanes.Lib.Crypto.Hmac
public import Lanes.Db.Retry

/-!
# The typed store in SQL

The query subset of `Lanes/Db/Query.lean` as PostgreSQL statements with parameters, and what
their replies mean, pure, so that the driver (`Lanes/Lib/Postgres/IO/Db.lean`) decides nothing
(rule 3.9).

- **Tables.** `create` gives a table's `CREATE TABLE` and `CREATE INDEX` statements: `bigint`,
  `bytea`, `text COLLATE "C"` (so that text compares byte by byte, as `Value.compare` does) and
  `boolean`, `NOT NULL` unless the column is nullable, the primary key, and each index.
- **Values.** Parameters and results are in text: integers in decimal, bytes as `\x` and
  lowercase hex, booleans as `t` and `f`. A value reads back from its parameter
  (`decode_param`), so the format the driver sends is the one it reads.
- **Writes never fail.** An insert is `ON CONFLICT DO NOTHING`; an update or an upsert first
  checks, in the same statement, that no row of another key has its values in a unique index.
  Each answers a row when it wrote, so that its answer is whether it did. Under `SERIALIZABLE`,
  a conflict with a transaction the statement could not see is a serialization failure, which
  the driver retries.
- **Replies.** `classify` says what a reply means for an attempt: rows, a serialization failure
  or deadlock (`40001`, `40P01`), a unique violation (`23505`), a connection lost, or another error, by its SQLSTATE.
-/

@[expose] public section

namespace Lanes.Postgres.Sql

open Lanes.Db

def quote (name : String) : String := "\"" ++ name ++ "\""

def tySql : Ty → String
  | .int => "bigint"
  | .bytes => "bytea"
  | .text => "text COLLATE \"C\""
  | .bool => "boolean"

def tyCast : Ty → String
  | .int => "bigint"
  | .bytes => "bytea"
  | .text => "text"
  | .bool => "boolean"

/-! ## Values -/

def param : Value → Option String
  | .null => none
  | .int i => some i.toInt.repr
  | .bytes b => some ("\\x" ++ Bytes.hex b)
  | .text s => some s
  | .bool b => some (if b then "t" else "f")

def decodeInt (s : String) : Option Int64 := do
  let n ← s.toInt?
  if h : Int64.minValue.toInt ≤ n ∧ n ≤ Int64.maxValue.toInt then some (Int64.ofIntLE n h.1 h.2)
  else none

def decodeBytes (s : String) : Option ByteArray :=
  match s.toList with
  | '\\' :: 'x' :: rest => Bytes.unhex? (String.ofList rest)
  | _ => none

/-- A value of a column, from its text; `none` if it is not one. -/
def decode (c : Db.Column) : Option String → Option Value
  | none => if c.nullable then some .null else none
  | some s =>
    match c.ty with
    | .int => (decodeInt s).map .int
    | .bytes => (decodeBytes s).map .bytes
    | .text => if s.toList.contains '\x00' then none else some (.text s)
    | .bool => if s == "t" then some (.bool true) else if s == "f" then some (.bool false) else none

def decodeRow (t : Table) (r : List (Option String)) : Option Row :=
  if r.length = t.columns.length then (t.columns.zip r).mapM fun (c, v) => decode c v else none

/-! ## Statements -/

/-- A statement being written: its parameters so far. -/
abbrev Build := StateM (List (Option String))

def arg (ty : Ty) (v : Value) : Build String := do
  modify (· ++ [param v])
  return s!"${(← get).length}::{tyCast ty}"

def colName (t : Table) (n : Nat) : String := quote ((t.columns[n]?.map (·.name)).getD "")

def colTy (t : Table) (n : Nat) : Ty := (t.columns[n]?.map (·.ty)).getD .int

def columnList (t : Table) : String := ", ".intercalate (t.columns.map (quote ·.name))

/-- `"c" = $n AND …` for the columns `cols` and the values `vals`, prefixed by `pre`. -/
def eqs (t : Table) (pre : String) (cols : List Nat) (vals : Row) : Build String := do
  let parts ← (cols.zip vals).mapM fun (n, v) => do
    return s!"{pre}{colName t n} = {← arg (colTy t n) v}"
  return " AND ".intercalate parts

def keyCols (t : Table) : List Nat := List.range t.key

def condSql (t : Table) : Nat × Cond → Build String
  | (n, c) => do
    let op := match c with
      | .eq _ => "=" | .gt _ => ">" | .ge _ => ">=" | .lt _ => "<" | .le _ => "<="
    return s!"{colName t n} {op} {← arg (colTy t n) c.value}"

def whereClause (parts : List String) : String :=
  if parts.isEmpty then "" else " WHERE " ++ " AND ".intercalate parts

/-- `NOT EXISTS` a row of another key with the values of `row` in a unique index of `t`; none if
`t` has no unique index. -/
def noClash (t : Table) (row : Row) : Build (Option String) := do
  let unique := t.indexes.filter (·.unique)
  if unique.isEmpty then return none
  let sameKey ← eqs t "o." (keyCols t) (t.keyOf row)
  let clauses ← unique.mapM fun i => do return s!"({← eqs t "o." i.columns (i.project row)})"
  return some s!"NOT EXISTS (SELECT 1 FROM {quote t.name} AS o WHERE NOT ({sameKey}) AND ({" OR ".intercalate clauses}))"

def selectSql (t : Table) (conds : List String) (suffix : String) : String :=
  s!"SELECT {columnList t} FROM {quote t.name}{whereClause conds}{suffix}"

def scanSql (s : Scan) : Build String := do
  let conds ← s.conds.mapM (condSql s.table)
  let dir := match s.order with | .asc => "ASC" | .desc => "DESC"
  let order := (s.columns ++ keyCols s.table).map fun n => s!"{colName s.table n} {dir}"
  return selectSql s.table conds s!" ORDER BY {", ".intercalate order} LIMIT {s.limit}"

def values (t : Table) (row : Row) : Build (List String) :=
  (t.columns.zip row).mapM fun (c, v) => arg c.ty v

def opSql : Op → Build String
  | .get t k => do return selectSql t [← eqs t "" (keyCols t) k] ""
  | .scan s => scanSql s
  | .insert t r => do
    return s!"INSERT INTO {quote t.name} ({columnList t}) VALUES ({", ".intercalate (← values t r)}) ON CONFLICT DO NOTHING RETURNING 1"
  | .update t r => do
    let cols := (List.range t.columns.length).drop t.key
    let sets ← if cols.isEmpty then pure [s!"{colName t 0} = {colName t 0}"]
      else cols.mapM fun n => do return s!"{colName t n} = {← arg (colTy t n) (r.getD n .null)}"
    let key ← eqs t "" (keyCols t) (t.keyOf r)
    let guard ← noClash t r
    return s!"UPDATE {quote t.name} SET {", ".intercalate sets}{whereClause ([key] ++ guard.toList)} RETURNING 1"
  | .upsert t r => do
    let vals ← values t r
    let guard ← noClash t r
    let sets := t.columns.map fun c => s!"{quote c.name} = EXCLUDED.{quote c.name}"
    let keys := ", ".intercalate ((keyCols t).map (colName t))
    return s!"INSERT INTO {quote t.name} ({columnList t}) SELECT {", ".intercalate vals}{whereClause guard.toList} ON CONFLICT ({keys}) DO UPDATE SET {", ".intercalate sets} RETURNING 1"
  | .delete t k => do return s!"DELETE FROM {quote t.name}{whereClause [← eqs t "" (keyCols t) k]} RETURNING 1"

/-- The statement a valid operation is sent as. -/
def statement (o : Op) : Statement :=
  let (sql, params) := (opSql o).run []
  { sql, params }

/-- A table's `CREATE TABLE`, then a `CREATE INDEX` for each of its indexes. -/
def create (t : Table) : List Statement :=
  let cols := t.columns.map fun c => s!"{quote c.name} {tySql c.ty}{if c.nullable then "" else " NOT NULL"}"
  let key := s!"PRIMARY KEY ({", ".intercalate ((keyCols t).map (colName t))})"
  { sql := s!"CREATE TABLE {quote t.name} ({", ".intercalate (cols ++ [key])})" } ::
    t.indexes.map fun i =>
      { sql := s!"CREATE {if i.unique then "UNIQUE " else ""}INDEX {quote (t.name ++ "_" ++ i.name)} ON {quote t.name} ({", ".intercalate (i.columns.map (colName t))})" }

/-! ## Replies -/

/-- What a reply to an operation's statement means; `none` if it is not one that statement
gives. -/
def answer : (o : Op) → Rows → Option o.Ret
  | .get t _, r =>
    match r.rows with
    | [] => some none
    | [row] => (decodeRow t row).map some
    | _ => none
  | .scan s, r => if r.rows.length ≤ s.limit then r.rows.mapM (decodeRow s.table) else none
  | .insert .., r | .update .., r | .upsert .., r | .delete .., r =>
    match r.rows with
    | [] => some false
    | [_] => some true
    | _ => none

def sqlstate (fields : List Field) : String :=
  ((fields.find? (·.code == 'C'.toNat.toUInt8)).map (·.value)).getD ""

/-- What a reply to a statement of an attempt means. -/
inductive Verdict where
  | rows (rows : Rows)
  /-- A serialization failure or a deadlock: the attempt is rolled back, and may be tried again. -/
  | conflict
  /-- Not sent, or the connection was lost: the attempt did not commit. -/
  | dropped
  | error (sqlstate : String)
  deriving DecidableEq, Repr

/-- A serialization failure, a deadlock, or a unique violation. A write checks its unique indexes
in the statement's snapshot, so a unique violation means a transaction it could not see took
the values first, which PostgreSQL does not always report as a serialization failure. Trying a
pure transaction again is safe in every case; these are the ones a new attempt can change. -/
def retryable (code : String) : Bool := code == "40001" || code == "40P01" || code == "23505"

/-- A reply to `BEGIN` or to a statement. -/
def classify : Reply → Verdict
  | .rows r => .rows r
  | .error fields => if retryable (sqlstate fields) then .conflict else .error (sqlstate fields)
  | .unknown | .refused _ => .dropped
  | .tooManyRows => .error "54000"
  | .committed | .rolledBack => .error ""

/-- How an attempt whose transaction answered `a` ended, by the reply to its `COMMIT`. -/
def committed {A : Type} (a : A) : Reply → Attempt A
  | .committed => .committed a
  | .error fields => if retryable (sqlstate fields) then .conflict else .error (sqlstate fields)
  | .refused _ => .dropped
  | .unknown => .unknown
  | .rows _ | .rolledBack | .tooManyRows => .error ""


/-! ## A value reads back from its parameter -/

theorem decodeInt_repr (i : Int64) : decodeInt i.toInt.repr = some i := by
  simp only [decodeInt, Int.toInt?_repr, Option.bind_eq_bind, Option.bind_some]
  have := i.le_toInt
  simp [Int64.toInt_le]
  omega

theorem decodeBytes_param (b : ByteArray) : decodeBytes ("\\x" ++ Bytes.hex b) = some b := by
  simp [decodeBytes, String.toList_append, Bytes.unhex?_hex]

theorem decode_param (c : Db.Column) (v : Value) (h : c.admits v = true) : decode c (param v) = some v := by
  cases v with
  | null => simpa [param, decode, Db.Column.admits] using h
  | int i => cases hc : c.ty <;> simp_all [param, decode, Db.Column.admits, Value.hasTy, decodeInt_repr]
  | bytes b => cases hc : c.ty <;> simp_all [param, decode, Db.Column.admits, Value.hasTy, decodeBytes_param]
  | text s => cases hc : c.ty <;> simp_all [param, decode, Db.Column.admits, Value.hasTy]
  | bool b => cases hc : c.ty <;> cases b <;> simp_all [param, decode, Db.Column.admits, Value.hasTy] <;> decide
theorem mapM_decode (cs : List Db.Column) (r : Row) (hlen : r.length = cs.length)
    (h : (cs.zip r).all (fun (c, v) => c.admits v) = true) :
    (cs.zip (r.map param)).mapM (fun (c, v) => decode c v) = some r := by
  induction cs generalizing r with
  | nil => cases r <;> simp_all
  | cons c cs ih =>
    cases r with
    | nil => simp at hlen
    | cons v r =>
      simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at h
      simp [List.map_cons, List.zip_cons_cons, List.mapM_cons, decode_param c v h.1,
        ih r (by simpa using hlen) h.2]

theorem decodeRow_param (t : Table) (r : Row) (h : t.admits r = true) :
    decodeRow t (r.map param) = some r := by
  simp only [Table.admits, Bool.and_eq_true, beq_iff_eq] at h
  simp [decodeRow, h.1, mapM_decode t.columns r h.1 h.2]

end Lanes.Postgres.Sql
