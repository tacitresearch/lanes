/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std.Data.String

/-!
# Typed tables, as values

The data of the typed store (`docs/decisions/new-typed-store.md`): a table has typed columns,
of 64-bit integers, bytes, text and booleans, each nullable or not; its primary key is its first
`key` columns; it declares secondary indexes, unique or not. A row is a list of values, and a
database (`Db`) the rows of each table, sorted by primary key.

The order of values is the one PostgreSQL gives the column types the driver creates
(`Lanes/Lib/Postgres/Db.lean`): integers by value, bytes and text byte by byte (text is created
`COLLATE "C"`), `false` before `true`. Key and index columns are never `NULL` (`Table.valid`),
so that `NULL`'s place in an order and its equality never matter. PostgreSQL's text cannot hold
the character `NUL`, so a text value that does is not admitted.
-/

@[expose] public section

namespace Lanes.Db

inductive Ty where
  | int
  | bytes
  | text
  | bool
  deriving DecidableEq, Repr, Hashable

inductive Value where
  | null
  | int (i : Int64)
  | bytes (b : ByteArray)
  | text (s : String)
  | bool (b : Bool)
  deriving DecidableEq, Hashable

instance : Inhabited Value := ⟨.null⟩

instance : Repr Value where
  reprPrec
    | .null, _ => "null"
    | .int i, _ => s!"int {i}"
    | .bytes b, _ => s!"bytes {b.data.toList}"
    | .text s, _ => s!"text {s.quote}"
    | .bool b, _ => s!"bool {b}"

abbrev Row := List Value

structure Column where
  name : String
  ty : Ty
  nullable : Bool := false
  deriving DecidableEq, Repr, Hashable

/-- A secondary index, by the positions of its columns in a row. -/
structure Index where
  name : String
  columns : List Nat
  unique : Bool := false
  deriving DecidableEq, Repr, Hashable

structure Table where
  name : String
  columns : List Column
  /-- The primary key is the first `key` columns. -/
  key : Nat
  indexes : List Index := []
  deriving DecidableEq, Repr, Hashable

/-- The tables of a database. -/
abbrev Schema := List Table

namespace Value

def hasTy : Value → Ty → Bool
  | .int _, .int | .bytes _, .bytes | .bool _, .bool => true
  | .text s, .text => !s.toList.contains '\x00'
  | _, _ => false

/-- The order of kinds, for values of different types, which no valid query compares. -/
def rank : Value → Nat
  | .null => 0
  | .int _ => 1
  | .bytes _ => 2
  | .text _ => 3
  | .bool _ => 4

def lex : List UInt8 → List UInt8 → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs => (compare a b).then (lex as bs)

def compare : Value → Value → Ordering
  | .int a, .int b => Ord.compare a.toInt b.toInt
  | .bytes a, .bytes b => lex a.data.toList b.data.toList
  | .text a, .text b => lex a.toUTF8.data.toList b.toUTF8.data.toList
  | .bool a, .bool b => Ord.compare a b
  | a, b => Ord.compare a.rank b.rank

end Value

/-- Rows, or keys, compared column by column. -/
def compareRows : Row → Row → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs => (Value.compare a b).then (compareRows as bs)

def Column.admits (c : Column) : Value → Bool
  | .null => c.nullable
  | v => v.hasTy c.ty

/-- A name PostgreSQL takes as it is: lowercase letters, digits and `_`, not starting with a
digit, at most 63 bytes. -/
def identifier (s : String) : Bool :=
  !s.isEmpty && s.length ≤ 63 && (s.toList.all fun c => c.isLower || c.isDigit || c == '_')
    && s.toList.head?.any (fun c => !c.isDigit)

namespace Table

variable (t : Table)

def keyOf (r : Row) : Row := r.take t.key

def admits (r : Row) : Bool :=
  r.length == t.columns.length && (t.columns.zip r).all fun (c, v) => c.admits v

/-- Whether the column at position `n` is there and never `NULL`. -/
def required (n : Nat) : Bool := t.columns[n]?.any (!·.nullable)

def valid : Bool :=
  identifier t.name && t.columns.all (identifier ·.name)
    && (t.columns.map (·.name)).eraseDups.length == t.columns.length
    && 0 < t.key && t.key ≤ t.columns.length && (List.range t.key).all t.required
    && t.indexes.all (fun i => identifier i.name && !i.columns.isEmpty && i.columns.all t.required)
    && (t.indexes.map (·.name)).eraseDups.length == t.indexes.length

/-- Whether key values have the key columns' types. -/
def admitsKey (key : Row) : Bool :=
  key.length == t.key && ((t.columns.take t.key).zip key).all fun (c, v) => c.admits v

end Table

def Index.project (i : Index) (r : Row) : Row := i.columns.map fun n => r.getD n .null

/-- A database: the rows of each table, by its name, sorted by primary key, one per key. -/
structure Db where
  tables : List (String × List Row) := []
  deriving DecidableEq, Hashable

namespace Db

def empty (schema : Schema) : Db := { tables := schema.map (·.name, []) }

def rows (db : Db) (name : String) : List Row := (db.tables.lookup name).getD []

def setRows (db : Db) (name : String) (rows : List Row) : Db :=
  if db.tables.any (·.1 == name) then
    { tables := db.tables.map fun (n, rs) => if n == name then (n, rows) else (n, rs) }
  else { tables := db.tables ++ [(name, rows)] }

end Db

end Lanes.Db
