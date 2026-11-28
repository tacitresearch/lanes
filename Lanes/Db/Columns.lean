/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Db.Txn

/-!
# A Lean type as columns

What `lanes_data … table …` (`Lanes/Data/Declare.lean`) derives a `TableOf` with. A field's type
is stored in one column (`ColumnOf`): `Int64`, `ByteArray`, `String` and `Bool`, never `NULL`,
or `Option` of one, nullable, with `none` as `NULL`. A structure is its fields' columns, one
after another (`Columns`), and each piece carries both laws, so a derived table has both by
construction: a value reads back from its row (`TableOf.ofRow_toRow`), and a row that reads
back is the row of what it read (`Columns.toRow_of_ofRow`), which a proof about what a scan
found uses.

`Int` and `Nat` have no column: a column holds 64 bits, and a value that does not fit would not
read back.
-/

@[expose] public section

namespace Lanes.Db

/-- A type stored in one column that is never `NULL`. -/
class Scalar (α : Type) where
  ty : Ty
  toValue : α → Value
  ofValue : Value → Option α
  ofValue_toValue : ∀ a, ofValue (toValue a) = some a
  toValue_ofValue : ∀ {v a}, ofValue v = some a → toValue a = v
  ofValue_null : ofValue .null = none

namespace Scalar

variable {α : Type} [Scalar α]

theorem toValue_ne_null (a : α) : toValue a ≠ .null := fun h => by
  have := ofValue_toValue a
  rw [h, ofValue_null] at this
  cases this

instance : Scalar Int64 where
  ty := .int
  toValue := .int
  ofValue | .int i => some i | _ => none
  ofValue_toValue _ := rfl
  toValue_ofValue {v _} h := by cases v <;> simp_all
  ofValue_null := rfl

instance : Scalar ByteArray where
  ty := .bytes
  toValue := .bytes
  ofValue | .bytes b => some b | _ => none
  ofValue_toValue _ := rfl
  toValue_ofValue {v _} h := by cases v <;> simp_all
  ofValue_null := rfl

instance : Scalar String where
  ty := .text
  toValue := .text
  ofValue | .text s => some s | _ => none
  ofValue_toValue _ := rfl
  toValue_ofValue {v _} h := by cases v <;> simp_all
  ofValue_null := rfl

instance : Scalar Bool where
  ty := .bool
  toValue := .bool
  ofValue | .bool b => some b | _ => none
  ofValue_toValue _ := rfl
  toValue_ofValue {v _} h := by cases v <;> simp_all
  ofValue_null := rfl

@[simp] theorem toValue_int64 (i : Int64) : toValue i = .int i := rfl
@[simp] theorem toValue_bytes (b : ByteArray) : toValue b = .bytes b := rfl
@[simp] theorem toValue_string (s : String) : toValue s = .text s := rfl
@[simp] theorem toValue_bool (b : Bool) : toValue b = .bool b := rfl

end Scalar

/-- A type stored in one column: a `Scalar`, or `Option` of one, which is nullable. -/
class ColumnOf (α : Type) where
  ty : Ty
  nullable : Bool
  toValue : α → Value
  ofValue : Value → Option α
  ofValue_toValue : ∀ a, ofValue (toValue a) = some a
  toValue_ofValue : ∀ {v a}, ofValue v = some a → toValue a = v

namespace ColumnOf

variable {α : Type} [Scalar α]

instance : ColumnOf α where
  ty := Scalar.ty α
  nullable := false
  toValue := Scalar.toValue
  ofValue := Scalar.ofValue
  ofValue_toValue := Scalar.ofValue_toValue
  toValue_ofValue := Scalar.toValue_ofValue

instance : ColumnOf (Option α) where
  ty := Scalar.ty α
  nullable := true
  toValue
    | none => .null
    | some a => Scalar.toValue a
  ofValue
    | .null => some none
    | v => (Scalar.ofValue v).map some
  ofValue_toValue
    | none => rfl
    | some a => by
      have := Scalar.toValue_ne_null a
      split
      · contradiction
      · simp [Scalar.ofValue_toValue]
  toValue_ofValue {v a} h := by
    cases v with
    | null => simp at h; subst h; rfl
    | _ =>
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨b, hb, rfl⟩ := h
      exact Scalar.toValue_ofValue hb

@[simp] theorem toValue_scalar (a : α) : ColumnOf.toValue a = Scalar.toValue a := rfl
@[simp] theorem toValue_none : ColumnOf.toValue (none : Option α) = .null := rfl
@[simp] theorem toValue_some (a : α) : ColumnOf.toValue (some a) = Scalar.toValue a := rfl

end ColumnOf

/-- Columns of a table, and a type written as their values, in order: a row, or its start. -/
structure Columns (α : Type) where
  columns : List Column
  write : α → Row
  read : Row → Option (α × Row)
  read_write : ∀ a rest, read (write a ++ rest) = some (a, rest)
  write_read : ∀ {r a rest}, read r = some (a, rest) → write a ++ rest = r

namespace Columns

variable {α β : Type}

def column (name : String) {β : Type} [ColumnOf β] : Columns β where
  columns := [{ name, ty := ColumnOf.ty β, nullable := ColumnOf.nullable β }]
  write b := [ColumnOf.toValue b]
  read
    | v :: rest => (ColumnOf.ofValue v).map (·, rest)
    | [] => none
  read_write b rest := by simp [ColumnOf.ofValue_toValue]
  write_read {r b rest} h := by
    cases r with
    | nil => cases h
    | cons v r =>
      simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨b', hb, rfl, rfl⟩ := h
      simp [ColumnOf.toValue_ofValue hb]

def unit : Columns Unit where
  columns := []
  write _ := []
  read r := some ((), r)
  read_write _ _ := rfl
  write_read h := by cases h; rfl

def pair (a : Columns α) (b : Columns β) : Columns (α × β) where
  columns := a.columns ++ b.columns
  write x := a.write x.1 ++ b.write x.2
  read r := do
    let (x, rest) ← a.read r
    let (y, rest) ← b.read rest
    return ((x, y), rest)
  read_write x rest := by simp [List.append_assoc, a.read_write, b.read_write]
  write_read {r x rest} h := by
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨⟨x₁, r₁⟩, h₁, ⟨y, r₂⟩, h₂, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    rw [List.append_assoc, b.write_read h₂, a.write_read h₁]

/-- A type written as another that holds the same values. -/
def map (c : Columns β) (to : α → β) (back : β → α) (h : ∀ a, back (to a) = a)
    (h' : ∀ b, to (back b) = b) : Columns α where
  columns := c.columns
  write a := c.write (to a)
  read r := (c.read r).map fun (b, rest) => (back b, rest)
  read_write a rest := by simp [c.read_write, h]
  write_read {r a rest} hr := by
    simp only [Option.map_eq_some_iff, Prod.mk.injEq, Prod.exists] at hr
    obtain ⟨b, rest', hb, rfl, rfl⟩ := hr
    rw [h']
    exact c.write_read hb

/-- The table: these columns, the first `key` of them its primary key. -/
def table (c : Columns α) (name : String) (key : Nat) (indexes : List Index := []) : TableOf α where
  table := { name, columns := c.columns, key, indexes }
  toRow := c.write
  ofRow r :=
    match c.read r with
    | some (a, []) => some a
    | _ => none
  ofRow_toRow a := by
    have := c.read_write a []
    simp only [List.append_nil] at this
    simp [this]

/-! What a derived table writes, for `simp`. -/

@[simp] theorem column_write (name : String) [ColumnOf β] (b : β) :
    (column name).write b = [ColumnOf.toValue b] := rfl
@[simp] theorem unit_write (u : Unit) : unit.write u = [] := rfl
@[simp] theorem pair_write (a : Columns α) (b : Columns β) (x : α × β) :
    (a.pair b).write x = a.write x.1 ++ b.write x.2 := rfl
@[simp] theorem map_write (c : Columns β) (to : α → β) (back : β → α) (h h') (a : α) :
    (c.map to back h h').write a = c.write (to a) := rfl
@[simp] theorem table_toRow (c : Columns α) (name : String) (key : Nat) (indexes : List Index) :
    (c.table name key indexes).toRow = c.write := rfl
@[simp] theorem table_table (c : Columns α) (name : String) (key : Nat) (indexes : List Index) :
    (c.table name key indexes).table = { name, columns := c.columns, key, indexes } := rfl

/-- A row that reads back is the row of what it read. -/
theorem toRow_of_ofRow (c : Columns α) {name : String} {key : Nat} {indexes : List Index}
    {r : Row} {a : α} (h : (c.table name key indexes).ofRow r = some a) :
    r = (c.table name key indexes).toRow a := by
  simp only [table] at h ⊢
  split at h
  · rename_i a' hr
    cases h
    simpa using (c.write_read hr).symm
  · cases h

end Columns

end Lanes.Db
