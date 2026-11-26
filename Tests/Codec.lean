/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Examples.Bank

/-! Codecs built by the combinators and the two macros: what is written is read back, with what
followed it left over. The law is proved; these run the compiled code. -/

namespace Tests.Codec

open Lanes

structure Point where
  x : Int
  y : Int
  label : Option String
  deriving DecidableEq

inductive Shape where
  | dot
  | circle (centre : Point) (radius : Nat)
  | path (points : List Point) (closed : Bool)
  deriving DecidableEq

def Point.codec : Codec Point :=
  Codec.struct% Point { x := Codec.int, y := Codec.int, label := Codec.option Codec.string }

def Shape.codec : Codec Shape :=
  Codec.sum% Shape { dot, circle (centre := Point.codec) (radius := Codec.nat),
    path (points := Codec.list Point.codec) (closed := Codec.bool) }

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
        && Http.Request.codec.read (Http.Request.codec.write http) == some (http, [])) ]

end Tests.Codec
