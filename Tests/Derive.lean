/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-! What `lanes_data` derives. JSON: what is written reads back, in the documented shape, and
what Lean's own derived encoders write reads too. Rows: the schema a `table` line declares, and
rows that read back. The laws are proved; these run the compiled code and pin the wire format.
Then `Enum`, and `LawfulBEq` for a structure holding a function; and what the command accepts:
constructors named by keywords, arguments named like their constructor, default values and
subtypes, with the errors it gives. -/

namespace Tests.Derive

open Lanes

lanes_data structure Point where
  x : Int
  y : Int
  label : Option String
  deriving DecidableEq, ToJson, FromJson

lanes_data inductive Shape where
  | dot
  | circle (centre : Point) (radius : Nat)
  | path (points : List Point) (closed : Bool)
  deriving DecidableEq, ToJson, FromJson

lanes_data inductive Slot (A : Type) where
  | empty
  | held (owner : A) (count : Fin 2)
  deriving DecidableEq, Repr, Enum, ToJson, FromJson

lanes_data structure Pair (A : Type) where
  first : A
  second : Bool
  deriving DecidableEq, Enum

lanes_data structure Table (V : Type) where
  rows : Fin 2 → Nat
  version : Nat
  default : V
  deriving LawfulBEq

lanes_data inductive Door where
  | open (wide : Bool)
  | close
  | «end»
  deriving DecidableEq, Repr, Enum, ToJson, FromJson

lanes_data inductive Ask where
  | ask (ask : Shape)
  | both (both : Bool) (ask : Door)
  deriving DecidableEq, ToJson, FromJson

lanes_data structure Tally where
  hits : Nat := 0
  doors : List Door := [.close]
  owner : String
  deriving DecidableEq, ToJson, FromJson

def Handle.valid (s : String) : Bool :=
  0 < s.length && s.toList.all Char.isLower

abbrev Handle := {s : String // Handle.valid s}

lanes_data structure Member where
  handle : Handle
  rank : {k : Fin 4 // k ≠ 0}
  deriving DecidableEq, Repr, Hashable, ToJson, FromJson, LawfulBEq

/-- A parameter inside `Option` needs `NonNullJson`, which `Option`'s own law asks. -/
lanes_data structure Maybe (A : Type) where
  value : Option A
  deriving DecidableEq, ToJson, FromJson

/--
error: lanes_data: this type names `text`, and `ToJson`, `FromJson` takes each field by its type
alone. Put the property in the type of `text` instead, as a subtype `{x : α // p x}`, or both in
a sigma type.
-/
#guard_msgs (whitespace := lax) in
lanes_data structure Checked where
  text : String
  valid : Handle.valid text = true
  deriving ToJson, FromJson

/--
error: lanes_data: `ToJson` and `FromJson` are derived together, with the law that one reads back
what the other writes
-/
#guard_msgs (whitespace := lax) in
lanes_data structure Half where
  n : Nat
  deriving ToJson

/-! ### A table -/

/-- The key is not the first field: the columns are the key's, then the rest. -/
lanes_data structure Account where
  email : String
  id : Int64
  avatar : Option ByteArray := none
  admin : Bool := false
  createdAt : Int64
  deriving DecidableEq
  table accounts key id
    unique index byEmail on email
    index recent "accounts_new" on createdAt, id

/-- error: lanes_data: the structure has no field `name` -/
#guard_msgs in
lanes_data structure Named where
  id : Int64
  table nameds key id
    index byName on name

/--
error: lanes_data: a table is declared by a line after `deriving`: `table todos key id`, then
`index byOwner on owner` lines
-/
#guard_msgs (whitespace := lax) in
lanes_data structure Wrong where
  id : Int64
  deriving TableOf

/-- The law, for any value. -/
example (a : Account) : accounts.ofRow (accounts.toRow a) = some a := accounts.ofRow_toRow a
example (s : Shape) : fromJson? (toJson s) = .ok s := fromJson?_toJson s
example (m : Maybe (Slot Nat)) : fromJson? (toJson m) = .ok m := fromJson?_toJson m

def shapes : List Shape :=
  [ .dot, .circle ⟨-3, 4, some "a/b é"⟩ 7, .path [] true,
    .path [⟨0, 0, none⟩, ⟨1, -1, some ""⟩, ⟨-2000000, 5, some "x"⟩] false ]

def roundTrips {α : Type} [ToJson α] [FromJson α] [DecidableEq α] (a : α) : Bool :=
  match (Json.parse (toJson a).compress).toOption.map fromJson? with
  | some (.ok b) => decide (b = a)
  | _ => false

def reads {α : Type} [FromJson α] [DecidableEq α] (text : String) (a : α) : Bool :=
  match (Json.parse text).toOption.map fromJson? with
  | some (.ok b) => decide (b = a)
  | _ => false

def refuses (α : Type) [FromJson α] (text : String) : Bool :=
  match (Json.parse text).toOption.map (fromJson? (α := α)) with
  | some (.ok _) => false
  | _ => true

def alice : Account :=
  { email := "alice@example.com", id := 7, createdAt := -1, avatar := some "x".toUTF8 }

def tests : List (String × Bool) :=
  [ ("json: a structure and an inductive type read back from their text",
      shapes.all roundTrips && roundTrips (Slot.held (3 : Nat) 1) && roundTrips (Slot.empty : Slot Nat)),
    ("json: a structure is an object of its fields, and a field that is null is left out",
      (toJson (Point.mk 1 (-2) none)).compress == "{\"x\":1,\"y\":-2}"
        && (toJson (Point.mk 1 2 (some "a"))).compress == "{\"label\":\"a\",\"x\":1,\"y\":2}"),
    ("json: a constructor is its name, or an object of its name holding its arguments",
      (toJson Shape.dot).compress == "\"dot\""
        && (toJson (Shape.path [] true)).compress == "{\"path\":{\"closed\":true,\"points\":[]}}"
        && (toJson (Door.open false)).compress == "{\"open\":{\"wide\":false}}"
        && (toJson Door.end).compress == "\"end\""),
    ("json: what Lean's derived encoders write reads back: nulls, and arguments as an object",
      reads "{\"x\":1,\"y\":2,\"label\":null}" (Point.mk 1 2 none)
        && reads "{\"dot\":{}}" Shape.dot
        && reads "{\"circle\":{\"centre\":{\"x\":0,\"y\":0},\"radius\":3}}"
          (Shape.circle ⟨0, 0, none⟩ 3)),
    ("json: a missing field, a field of the wrong type, another name or another shape is refused",
      refuses Point "{\"x\":1}" && refuses Point "{\"x\":1,\"y\":\"2\"}" && refuses Point "[1,2]"
        && refuses Shape "\"square\"" && refuses Shape "{\"dot\":{},\"path\":{}}"
        && refuses Shape "\"circle\"" && refuses Shape "3"),
    ("json: a parameter's instance is the one used",
      (toJson (Slot.held "ab" 1)).compress == "{\"held\":{\"count\":1,\"owner\":\"ab\"}}"
        && roundTrips (Maybe.mk (some (Slot.empty : Slot Nat)))
        && (toJson (Maybe.mk (none : Option Nat))).compress == "{}"),
    ("enum: lanes_data lists every value of an inductive type and of a structure, once each",
      Enum.all (α := Slot Bool)
          == [.empty, .held false 0, .held false 1, .held true 0, .held true 1]
        && (Enum.all (α := Pair (Slot Bool))).length == 10
        && (Enum.all (α := Pair (Slot Bool))).eraseDups.length == 10),
    ("beq: a structure holding a function is compared at every argument",
      let table : Table (Option Nat) := { rows := fun k => k.val, version := 1, default := none }
      table == { table with rows := fun k => k.val + 0 }
        && !(table == { table with rows := fun k => if k = 1 then 2 else k.val })
        && !(table == { table with version := 2 })),
    ("lanes_data: a constructor may be named by a keyword, as in `inductive`",
      Enum.all (α := Door) == [.open false, .open true, .close, .end]
        && Enum.all.all fun (door : Door) => roundTrips door),
    ("lanes_data: an argument may be named like its constructor",
      [Ask.ask (.circle ⟨1, 2, none⟩ 3), .both true .end].all roundTrips),
    ("lanes_data: fields with defaults are left out of a structure instance, and written",
      let tally : Tally := { owner := "o" }
      tally.hits == 0 && tally.doors == [.close] && roundTrips tally
        && (toJson tally).compress == "{\"doors\":[\"close\"],\"hits\":0,\"owner\":\"o\"}"),
    ("subtype: a value is written as its value, and read back only with its property",
      let member : Member := ⟨⟨"ada", rfl⟩, ⟨2, by decide⟩⟩
      roundTrips member
        && (toJson member).compress == "{\"handle\":\"ada\",\"rank\":2}"
        && refuses Member "{\"handle\":\"Ada\",\"rank\":2}"
        && refuses Member "{\"handle\":\"ada\",\"rank\":0}"
        && member == { member with handle := ⟨"ada", rfl⟩ }
        && (Enum.all (α := {k : Fin 4 // k ≠ 0})).map (·.val) == [1, 2, 3]),
    ("table: the key's columns come first, names are snake_case, an index's starts with its table's",
      accounts.table == {
        name := "accounts", key := 1,
        columns := [{ name := "id", ty := .int }, { name := "email", ty := .text },
          { name := "avatar", ty := .bytes, nullable := true }, { name := "admin", ty := .bool },
          { name := "created_at", ty := .int }],
        indexes := [{ name := "accounts_by_email", columns := [1], unique := true },
          { name := "accounts_new", columns := [4, 0] }] }
        && accounts.table.valid && accounts.byEmail.unique && !accounts.recent.unique),
    ("table: a row is the values in the columns' order, `none` as NULL, and reads back",
      accounts.toRow alice
          == [.int 7, .text "alice@example.com", .bytes "x".toUTF8, .bool false, .int (-1)]
        && (accounts.toRow { alice with avatar := none }).contains .null
        && accounts.ofRow (accounts.toRow alice) == some alice
        && accounts.ofRow (accounts.toRow { alice with avatar := none })
          == some { alice with avatar := none }),
    ("table: a row of other types, or of another length, does not read",
      accounts.ofRow [.int 7, .text "a", .null, .bool false] == none
        && accounts.ofRow (accounts.toRow alice ++ [.null]) == none
        && accounts.ofRow [.text "7", .text "a", .null, .bool false, .int 0] == none
        && accounts.ofRow [.int 7, .null, .null, .bool false, .int 0] == none) ]

end Tests.Derive
