/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Tests.Codec

/-! The schemas and values that codecs carry: what `lanes_data` derives, with its former names
(`(was …)`) and defaults; what the combinators and the macros give; the text of a schema; and
values that do not fit their schema, which are refused. The law `ofValue (toValue a) = some a`
is a field of every codec; these run the compiled code. -/

namespace Tests.Schema

open Lanes

lanes_data structure Point where
  x : Int
  height (was y) : Int := 0
  label : Option String := some "here"
  deriving DecidableEq, Codable

lanes_data inductive Shape (A : Type) where
  | dot
  | circle (centre : Point) (radius : Nat := 1)
  | path (was line polyline) (points : List Point) (closed (was shut) : Bool)
  | tagged (tag : A) (counts : List (A × Nat))
  | «open»
  deriving DecidableEq, Codable

/-- `was` is a word only after a name: elsewhere it is an identifier. -/
lanes_data structure Was where
  was : Nat
  deriving DecidableEq, Codable

lanes_data inductive Named where
  | was (was : Nat)
  deriving DecidableEq, Codable

/--
error: lanes_data: this default names `x`, and the schema `Codable` derives holds a default as a
value. Give one that names no field.
-/
#guard_msgs (whitespace := lax) in
lanes_data structure Derived where
  x : Nat
  y : Nat := x + 1
  deriving Codable

def shapeText : String := "Tests.Schema.Shape String

inductive Tests.Schema.Shape String where
  | dot
  | circle (centre : Tests.Schema.Point) (radius : Nat := 1)
  | path (was line polyline) (points : List Tests.Schema.Point) (closed (was shut) : Bool)
  | tagged (tag : String) (counts : List (Prod String Nat))
  | open

structure Tests.Schema.Point where
  x : Int
  height (was y) : Int := 0
  label : Option String := .some \"here\"

inductive Option String where
  | none
  | some (val : String)

inductive Bool where
  | false
  | true

structure Prod String Nat where
  fst : String
  snd : Nat
"

/-- A tree, which refers to itself: no codec derives one yet, and its schema is written so. -/
def tree : Schema :=
  ⟨[("Tree", .sum "Tree" [⟨"leaf", [], []⟩, ⟨"node", [], [⟨"left", [], .ref "Tree", none⟩,
      ⟨"value", [], .nat, none⟩, ⟨"right", [], .ref "Tree", none⟩]⟩])], .ref "Tree"⟩

def treeText : String := "Tree

inductive Tree where
  | leaf
  | node (left : Tree) (value : Nat) (right : Tree)
"

/-- `node (node leaf 1 leaf) 2 leaf`. -/
def treeValue : Value := .ctor 1 [.ctor 1 [.ctor 0 [], .nat 1, .ctor 0 []], .nat 2, .ctor 0 []]

def pairOfPoints : Schema := (Codec.of (Point × Point)).schema

def shapes : List (Shape String) :=
  [ .dot, .circle { x := 0 } 2, .path [⟨-3, 4, none⟩, {x := 5}] true, .tagged "t" [("a", 1), ("", 0)],
    .open ]

def roundTrip {α : Type} [BEq α] (c : Codec α) (a : α) : Bool :=
  c.ofValue (c.toValue a) == some a

def tests : List (String × Bool) :=
  [ ("schema: lanes_data's schema names the type, its fields and constructors, their former \
      names and their defaults",
      (Codec.of (Shape String)).schema.text == shapeText),
    ("schema: a default is recorded as the value it is, and a field without one has none",
      match (Codec.of Point).schema.types.lookup "Tests.Schema.Point" with
      | some (.record "Tests.Schema.Point" [x, h, l]) =>
        x.default == none && h.default == some (.int 0) && h.aliases == ["y"]
          && l.default == some (.ctor 1 [.string "here"])
      | _ => false),
    ("schema: a value is the constructor's index and its fields, with no names",
      (Codec.of (Shape String)).toValue (.circle { x := 0 } 2)
          == .ctor 1 [.ctor 0 [.int 0, .int 0, .ctor 1 [.string "here"]], .nat 2]
        && (Codec.of (Shape String)).toValue .open == .ctor 4 []),
    ("schema: each value of a declared type reads back from its value",
      shapes.all (roundTrip (Codec.of (Shape String)))
        && Tests.Codec.shapes.all (roundTrip (Codec.of Tests.Codec.Shape))
        && roundTrip (Codec.of Was) ⟨3⟩ && roundTrip (Codec.of Named) (.was 4)),
    ("schema: a value that does not fit its schema is refused",
      let c := Codec.of (Shape String)
      (c.ofValue (.ctor 5 [])).isNone && (c.ofValue (.ctor 1 [.nat 2])).isNone
        && (c.ofValue (.ctor 3 [.string "t", .list [.ctor 0 [.string "a"]]])).isNone
        && (c.ofValue (.nat 0)).isNone
        && ((Codec.of Tests.Codec.Member).ofValue (.ctor 0 [.string "Ada", .nat 2])).isNone),
    ("schema: Lean's own types are named as Lean names them",
      (Codec.of Bool).toValue true == .ctor 1 [] && (Codec.of (Option Nat)).toValue none == .ctor 0 []
        && (Codec.of (Nat × String)).toValue (1, "a") == .ctor 0 [.nat 1, .string "a"]
        && (Codec.of (Nat ⊕ Unit)).toValue (.inr ()) == .ctor 1 [.ctor 0 []]
        && (Codec.of Int).toValue (-3) == .int (-3)
        && (Codec.of (Fin 3)).schema == ⟨[], .nat⟩
        && (Codec.of (Option Nat)).schema.name == "Option Nat"
        && (Codec.of (Std.ExtTreeMap String Nat)).schema == ⟨[], .map .string .nat⟩
        && (Codec.of (Std.ExtTreeMap String Nat)).toValue (.ofList [("b", 2), ("a", 1)])
          == .list [.ctor 0 [.string "a", .nat 1], .ctor 0 [.string "b", .nat 2]]),
    ("schema: Codec.struct% and Codec.sum% name what lanes_data names",
      Tests.Codec.Point.byHand.schema == (Codec.of Tests.Codec.Point).schema
        && Tests.Codec.Shape.byHand.schema == (Codec.of Tests.Codec.Shape).schema
        && Tests.Codec.shapes.all fun s =>
          Tests.Codec.Shape.byHand.toValue s == (Codec.of Tests.Codec.Shape).toValue s),
    ("schema: a value is written with its schema as Lean writes it",
      let c := Codec.of (Shape String)
      c.schema.display (c.toValue (.tagged "a b" [("c", 2)]))
          == ".tagged \"a b\" [{ fst := \"c\", snd := 2 }]"
        && c.schema.display (c.toValue (.circle ⟨-1, 2, none⟩ 3))
          == ".circle { x := -1, height := 2, label := .none } 3"
        && c.schema.display (.nat 3) == "?"),
    ("schema: a named type is declared once, in the table, and each use refers to it by name",
      pairOfPoints.types.map (·.1)
          == ["Prod Tests.Schema.Point Tests.Schema.Point", "Tests.Schema.Point", "Option String"]
        && pairOfPoints.root == .ref "Prod Tests.Schema.Point Tests.Schema.Point"
        && pairOfPoints.type? == some "Prod"
        && ((pairOfPoints.types.lookup pairOfPoints.name).map (·.refs))
          == some ["Tests.Schema.Point", "Tests.Schema.Point"]
        && (Codec.of (Std.ExtTreeMap String Point)).schema
          == Schema.map (Codec.of String).schema (Codec.of Point).schema
        && (Codec.of (Shape String)).schema.types.length == 5),
    ("schema: a type that refers to itself is written, shown and read back as a value",
      tree.text == treeText
        && tree.display treeValue == ".node (.node .leaf 1 .leaf) 2 .leaf"
        && Schema.ofValue? tree.toValue == some tree) ]

end Tests.Schema
