/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Db.Basic

/-!
# The query subset, and what each operation means

The operations a transaction may ask (`Op`): a row by primary key; a scan on the primary key or
a secondary index, with equality on its first columns and a range on the next, ordered either
way, with a limit (a lookup by an index is a scan with equality on all its columns); and an
insert, update, upsert or delete of one row by primary key. Each means a pure function of the
database (`Op.apply`), which `Lanes/Services/Postgres/Db.lean` compiles to SQL and
`Tests/Oracle/Service/Db.lean` compares with PostgreSQL.

A write that would give two rows the same values of a unique index does nothing and answers
`false`, as an insert that finds the key taken does: no write fails, so that a transaction never
fails for a reason it could have read first. An operation whose values do not have its columns'
types, on a table that is not valid, or a scan whose limit passes `Scan.limit_max`, is an error,
which ends the transaction before anything is sent.
-/

@[expose] public section

namespace Lanes.Db

/-- A condition on one column. -/
inductive Cond where
  | eq (v : Value)
  | gt (v : Value)
  | ge (v : Value)
  | lt (v : Value)
  | le (v : Value)
  deriving DecidableEq, Repr, Hashable

def Cond.value : Cond → Value
  | .eq v | .gt v | .ge v | .lt v | .le v => v

def Cond.holds (c : Cond) (x : Value) : Bool :=
  match c with
  | .eq v => x.compare v == .eq
  | .gt v => x.compare v == .gt
  | .ge v => x.compare v != .lt
  | .lt v => x.compare v == .lt
  | .le v => x.compare v != .gt

structure Bound where
  value : Value
  inclusive : Bool := true
  deriving DecidableEq, Repr, Hashable

inductive Order where
  | asc
  | desc
  deriving DecidableEq, Repr, Hashable

structure Scan where
  table : Table
  /-- `none` for the primary key. -/
  index : Option Index := none
  /-- Equal to the first columns of the index, one value each. -/
  eq : List Value := []
  /-- On the column after those. -/
  lower : Option Bound := none
  upper : Option Bound := none
  order : Order := .asc
  limit : Nat
  deriving DecidableEq, Repr, Hashable

namespace Scan

/-- The most rows one scan returns (rule 2.6). -/
def limit_max : Nat := 10000

variable (s : Scan)

/-- The columns of the index scanned, in order. -/
def columns : List Nat :=
  match s.index with
  | none => List.range s.table.key
  | some i => i.columns

/-- The conditions of the scan, each on one column. A bound on a column the index does not
have, or more values than its columns, is ignored, in the SQL too. -/
def conds : List (Nat × Cond) :=
  let eqs := (s.columns.zip s.eq).map fun (n, v) => (n, Cond.eq v)
  let range := match s.columns[s.eq.length]? with
    | none => []
    | some n =>
      (s.lower.toList.map fun b => (n, if b.inclusive then Cond.ge b.value else .gt b.value))
        ++ (s.upper.toList.map fun b => (n, if b.inclusive then Cond.le b.value else .lt b.value))
  eqs ++ range

def «matches» (r : Row) : Bool := s.conds.all fun (n, c) => c.holds (r.getD n .null)

/-- What a scan sorts by: the index's columns, then the primary key, which makes the order
total on rows with distinct keys. -/
def sortKey (r : Row) : Row := s.columns.map (r.getD · .null) ++ s.table.keyOf r

def before (a b : Row) : Bool :=
  match s.order with
  | .asc => compareRows (s.sortKey a) (s.sortKey b) != .gt
  | .desc => compareRows (s.sortKey a) (s.sortKey b) != .lt

def run (rows : List Row) : List Row :=
  ((rows.filter s.matches).mergeSort s.before).take s.limit

def valid : Bool :=
  s.table.valid && s.limit ≤ limit_max
    && s.conds.all fun (n, c) => c.value != .null && s.table.columns[n]?.any (·.admits c.value)

end Scan

inductive Op where
  | get (table : Table) (key : Row)
  | scan (s : Scan)
  /-- Insert a row whose key is free; `false`, and nothing, if it is taken. -/
  | insert (table : Table) (row : Row)
  /-- Replace the row of the row's key; `false`, and nothing, if there is none. -/
  | update (table : Table) (row : Row)
  /-- Insert or replace the row of the row's key. -/
  | upsert (table : Table) (row : Row)
  /-- Delete the row of a key; whether there was one. -/
  | delete (table : Table) (key : Row)
  deriving DecidableEq, Repr, Hashable

def Op.Ret : Op → Type
  | .get .. => Option Row
  | .scan _ => List Row
  | .insert .. | .update .. | .upsert .. | .delete .. => Bool

def Op.table : Op → Table
  | .get t _ | .insert t _ | .update t _ | .upsert t _ | .delete t _ => t
  | .scan s => s.table

def Op.valid : Op → Bool
  | .get t k | .delete t k => t.valid && t.admitsKey k
  | .scan s => s.valid
  | .insert t r | .update t r | .upsert t r => t.valid && t.admits r

def Op.writes : Op → Bool
  | .get .. | .scan _ => false
  | _ => true

namespace Table

variable (t : Table)

def hasKey (key : Row) (r : Row) : Bool := t.keyOf r == key

/-- Whether a row of another key has the values of `row` in a unique index. -/
def clashes (rows : List Row) (row : Row) : Bool :=
  t.indexes.any fun i => i.unique &&
    rows.any fun r => t.keyOf r != t.keyOf row && i.project r == i.project row

/-- Insert by key into rows sorted by key. -/
def insertSorted (row : Row) : List Row → List Row
  | [] => [row]
  | r :: rest =>
    if compareRows (t.keyOf row) (t.keyOf r) == .lt then row :: r :: rest
    else r :: insertSorted row rest

def without (key : Row) (rows : List Row) : List Row := rows.filter (!t.hasKey key ·)

end Table

/-- What a valid operation answers on a table's rows, and the rows after it. -/
def Op.onRows : (o : Op) → List Row → o.Ret × List Row
  | .get t k, rows => (rows.find? (t.hasKey k), rows)
  | .scan s, rows => (s.run rows, rows)
  | .insert t r, rows =>
    if rows.any (t.hasKey (t.keyOf r)) || t.clashes rows r then (false, rows)
    else (true, t.insertSorted r rows)
  | .update t r, rows =>
    if !rows.any (t.hasKey (t.keyOf r)) || t.clashes rows r then (false, rows)
    else (true, rows.map fun x => if t.hasKey (t.keyOf r) x then r else x)
  | .upsert t r, rows =>
    if t.clashes rows r then (false, rows)
    else (true, t.insertSorted r (t.without (t.keyOf r) rows))
  | .delete t k, rows => (rows.any (t.hasKey k), t.without k rows)

/-- What an operation means: its answer and the database after it, or why it is an error. -/
def Op.apply (o : Op) (db : Db) : Except String (o.Ret × Db) :=
  if o.valid then
    let (ret, rows) := o.onRows (db.rows o.table.name)
    .ok (ret, if o.writes then db.setRows o.table.name rows else db)
  else .error s!"an operation on {o.table.name} that the schema does not admit"

end Lanes.Db
