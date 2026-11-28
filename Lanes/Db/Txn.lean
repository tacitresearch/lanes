/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Db.Query

/-!
# A transaction, and a request handler

A transaction (`Txn`) is a program over the operations of `Lanes/Db/Query.lean`: a free monad,
so that an operation may depend on what earlier ones answered, and a value, so that it does no
IO. A request handler (`Handler`) is a pure function from a request to one transaction: its type
leaves no room for a second transaction, or for IO between two. The driver runs the transaction
at `SERIALIZABLE` and runs it again from the start after a serialization failure
(`Lanes/Db/Retry.lean`), which is safe because nothing outside saw the failed attempt.

What a transaction means is `Txn.run`: its operations applied one after another to one
database, which is what serializable promises it saw. A transaction may also `abort`, which
rolls it back.

`TableOf α` puts a Lean type on a table: rows encoded and decoded, with the law that a value
decodes from its row. A row that does not decode aborts the transaction that read it.
-/

@[expose] public section

namespace Lanes.Db

inductive Txn (α : Type) : Type where
  | pure (a : α)
  /-- Roll back, with a reason. -/
  | abort (why : String)
  | op (o : Op) (k : o.Ret → Txn α)

namespace Txn

def bind {α β : Type} : Txn α → (α → Txn β) → Txn β
  | .pure a, f => f a
  | .abort why, _ => .abort why
  | .op o k, f => .op o fun r => (k r).bind f

instance : Monad Txn where
  pure := .pure
  bind := Txn.bind

theorem bind_pure {α : Type} (t : Txn α) : t.bind Txn.pure = t := by
  induction t with
  | pure a => rfl
  | abort why => rfl
  | op o k ih => simp only [bind, ih]

theorem bind_assoc {α β γ : Type} (t : Txn α) (f : α → Txn β) (g : β → Txn γ) :
    (t.bind f).bind g = t.bind fun a => (f a).bind g := by
  induction t with
  | pure a => rfl
  | abort why => rfl
  | op o k ih => simp only [bind, ih]

instance : LawfulMonad Txn := LawfulMonad.mk'
  (id_map := fun t => bind_pure t)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := bind_assoc)

/-- The transaction's answer and the database after it, from `db`, or why it aborted. -/
def run {α : Type} : Txn α → Db → Except String (α × Db)
  | .pure a, db => .ok (a, db)
  | .abort why, _ => .error why
  | .op o k, db =>
    match o.apply db with
    | .ok (r, db') => (k r).run db'
    | .error e => .error e

/-- The transaction in a monad that answers each operation, as the driver runs it. -/
def interp {α : Type} {m : Type → Type} [Monad m] [MonadExceptOf String m]
    (answer : (o : Op) → m o.Ret) : Txn α → m α
  | .pure a => Pure.pure a
  | .abort why => throw why
  | .op o k => do interp answer (k (← answer o))

def get (t : Table) (key : Row) : Txn (Option Row) := .op (.get t key) .pure

def scan (s : Scan) : Txn (List Row) := .op (.scan s) .pure

def insert (t : Table) (row : Row) : Txn Bool := .op (.insert t row) .pure

def update (t : Table) (row : Row) : Txn Bool := .op (.update t row) .pure

def upsert (t : Table) (row : Row) : Txn Bool := .op (.upsert t row) .pure

def delete (t : Table) (key : Row) : Txn Bool := .op (.delete t key) .pure

/-- The rows whose index `i` has the values `vals`, at most `limit`, by primary key. -/
def lookup (t : Table) (i : Index) (vals : Row) (limit : Nat) : Txn (List Row) :=
  scan { table := t, index := some i, eq := vals, limit }

end Txn

/-- A request handler: one transaction per request, and nothing else. -/
abbrev Handler (Q A : Type) := Q → Txn A

/-- A Lean type stored in a table. -/
structure TableOf (α : Type) where
  table : Table
  toRow : α → Row
  ofRow : Row → Option α
  ofRow_toRow : ∀ a, ofRow (toRow a) = some a

namespace TableOf

variable {α : Type} (t : TableOf α)

def decode (r : Row) : Txn α :=
  match t.ofRow r with
  | some a => .pure a
  | none => .abort s!"a row of {t.table.name} does not decode"

def get (key : Row) : Txn (Option α) := do
  match ← Txn.get t.table key with
  | some r => some <$> t.decode r
  | none => Pure.pure none

def scan (s : Scan) : Txn (List α) := do
  (← Txn.scan { s with table := t.table }).mapM t.decode

def lookup (i : Index) (vals : Row) (limit : Nat) : Txn (List α) := do
  (← Txn.lookup t.table i vals limit).mapM t.decode

def insert (a : α) : Txn Bool := Txn.insert t.table (t.toRow a)

def update (a : α) : Txn Bool := Txn.update t.table (t.toRow a)

def upsert (a : α) : Txn Bool := Txn.upsert t.table (t.toRow a)

def delete (key : Row) : Txn Bool := Txn.delete t.table key

end TableOf

end Lanes.Db
