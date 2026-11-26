/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Examples.Bank

/-! Codecs built by the combinators, by the two macros and by `lanes_data`: what is written is
read back, with what followed it left over. The law is proved; these run the compiled code. Then
what else `lanes_data` derives: `Enum`, and `LawfulBEq` for a structure holding a function. -/

namespace Tests.Codec

open Lanes

lanes_data structure Point where
  x : Int
  y : Int
  label : Option String
  deriving DecidableEq, Codable

lanes_data inductive Shape where
  | dot
  | circle (centre : Point) (radius : Nat)
  | path (points : List Point) (closed : Bool)
  deriving DecidableEq, Codable

/-- The codecs `lanes_data` writes, by hand: the records must be the same. -/
def Point.byHand : Codec Point :=
  Codec.struct% Point { x := Codec.int, y := Codec.int, label := Codec.option Codec.string }

def Shape.byHand : Codec Shape :=
  Codec.sum% Shape { dot, circle (centre := Point.byHand) (radius := Codec.nat),
    path (points := Codec.list Point.byHand) (closed := Codec.bool) }

lanes_data inductive Slot (A : Type) where
  | empty
  | held (owner : A) (count : Fin 2)
  deriving DecidableEq, Repr, Enum, Codable

lanes_data structure Pair (A : Type) where
  first : A
  second : Bool
  deriving DecidableEq, Enum

lanes_data structure Table (V : Type) where
  rows : Fin 2 → Nat
  version : Nat
  default : V
  deriving LawfulBEq

def shapes : List Shape :=
  [ .dot, .circle ⟨-3, 4, some "a/b é"⟩ 7, .path [] true,
    .path [⟨0, 0, none⟩, ⟨1, -1, some ""⟩, ⟨-2000000, 5, some "x"⟩] false ]

def trailing : List ByteArray := ["next".toUTF8]

abbrev Index := Std.ExtTreeMap String (List Nat)

def Index.codec : Codec Index := Codec.extTreeMap Codec.string (Codec.list Codec.nat)

def index (keys : List String) : Index :=
  keys.foldl (fun m key => m.insert key [key.length, m.size]) ∅

def fruit : List String := ["pear", "apple", "fig", "quince", "apple", "é"]

def tests : List (String × Bool) :=
  [ ("codec: a structure and an inductive type read back as written, leaving what follows",
      shapes.all fun shape =>
        Shape.codec.read (Shape.codec.write shape ++ trailing) == some (shape, trailing)),
    ("codec: a list of them reads back in order",
      (Codec.list Shape.codec).read ((Codec.list Shape.codec).write shapes) == some (shapes, [])),
    ("codec: records cut short, or of another type, are refused",
      (shapes.drop 1).all (fun shape =>
        (Shape.codec.read ((Shape.codec.write shape).dropLast)).isNone)
        && (Shape.codec.read (Codec.string.write "circle")).isNone),
    ("codec: a map reads back as the map written, and an empty one as empty",
      Index.codec.read (Index.codec.write (index fruit) ++ trailing)
          == some (index fruit, trailing)
        && Index.codec.read (Index.codec.write ∅) == some (∅, [])
        && ((Index.codec.read (Index.codec.write (index fruit))).map
              fun (m, _) => (m["fig"]?, m["plum"]?, m.size))
            == some (some [3, 2], none, 5)),
    ("codec: maps that hold the same are written the same, however they were built",
      let other := (index (fruit.reverse ++ ["plum"])).erase "plum"
      let same := fruit.foldl (fun m key => m.insert key (index fruit)[key]!) other
      Index.codec.write same == Index.codec.write (index fruit)
        && Index.codec.write other != Index.codec.write (index fruit)),
    ("codec: the bank's requests and an HTTP request read back as written",
      let request : Examples.Bank.Request (Fin 3) := .transfer ⟨7, 0, 2, 40⟩
      let codec := Examples.Bank.Request.codec (Codec.fin (n := 3))
      let http : Http.Request := { method := .post, path := ["a", "b c"], query := [("q", "1")]
                                   headers := [("x", "y")], body := "body".toUTF8 }
      codec.read (codec.write request) == some (request, [])
        && Http.Request.codec.read (Http.Request.codec.write http) == some (http, [])),
    ("codec: lanes_data writes what the macros given each codec by hand write",
      shapes.all fun shape => (Codec.of Shape).write shape == Shape.byHand.write shape),
    ("codec: a parameter's codec is the one given, or its instance",
      let slot : Slot (Fin 3) := .held 2 1
      (Slot.codec Codec.fin).write slot == (Codec.of (Slot (Fin 3))).write slot
        && (Codec.of (Slot (Fin 3))).read ((Codec.of (Slot (Fin 3))).write slot ++ trailing)
          == some (slot, trailing)),
    ("enum: lanes_data lists every value of an inductive type and of a structure, once each",
      Enum.all (α := Slot Bool)
          == [.empty, .held false 0, .held false 1, .held true 0, .held true 1]
        && (Enum.all (α := Pair (Slot Bool))).length == 10
        && (Enum.all (α := Pair (Slot Bool))).eraseDups.length == 10),
    ("beq: a structure holding a function is compared at every argument",
      let table : Table (Option Nat) := { rows := fun k => k.val, version := 1, default := none }
      table == { table with rows := fun k => k.val + 0 }
        && !(table == { table with rows := fun k => if k = 1 then 2 else k.val })
        && !(table == { table with version := 2 })) ]

end Tests.Codec
