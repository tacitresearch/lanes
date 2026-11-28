module

import Lanes
meta import Spike.Lanes

/-! Lanes' derivations through `deriving`, on plain declarations. -/

open Lanes

namespace App

structure Point where
  x : Int
  y : Int
  /-- A docstring on a field, and a default value. -/
  label : Option String := none
  deriving DecidableEq, Repr, ToJson, FromJson

inductive Shape where
  | dot
  | circle (centre : Point) (radius : Nat)
  | path (points : List Point) (closed : Bool)
  deriving DecidableEq, Repr, ToJson, FromJson

inductive Slot (A : Type) where
  | empty
  | held (owner : A) (count : Fin 2)
  deriving DecidableEq, Repr, Enum, ToJson, FromJson

/-- `extends`, which `lanes_data` refuses. -/
structure Labelled extends Point where
  colour : String
  deriving DecidableEq, Repr, ToJson, FromJson

structure Todo where
  id : Int64
  owner : Int64
  title : String
  /-- When it was done, if it was. -/
  doneAt : Option Int64 := none
  deriving DecidableEq, Repr, ToJson, FromJson

lanes_table todos : Todo key id
  index byOwner on owner, title
  unique index byTitle "todo_titles" on title

example (t : Todo) : todos.ofRow (todos.toRow t) = some t := todos.ofRow_toRow t

/-- The laws hold for every value, as with `lanes_data`. -/
example (s : Shape) : fromJson? (toJson s) = .ok s := fromJson?_toJson s
example : NonNullJson (Slot Bool) := inferInstance

def roundTrips (s : Shape) : Bool :=
  match (Json.parse (toJson s).compress).toOption.map (fromJson? (α := Shape)) with
  | some (.ok b) => decide (b = s)
  | _ => false

def shapes : List Shape :=
  [.dot, .circle ⟨-3, 4, some "a/b é"⟩ 7, .path [⟨0, 0, none⟩] false]

end App

open App in
public def main : IO Unit := do
  for s in shapes do
    let j := (toJson s).compress
    IO.println s!"{j} reads back: {roundTrips s}"
  IO.println (toJson ({ x := 1, y := 2, colour := "red" } : Labelled)).compress
  IO.println s!"{(Enum.all : List (Slot Bool)).length} slots"
  IO.println s!"{todos.table.name} {todos.byOwner.name} {todos.byTitle.name} {todos.byOwner.columns}"
