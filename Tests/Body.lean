/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Tests.Schema

/-! The body of a value, written and read with its schema (`Lanes/Data/Body.lean`): the bytes of
each kind of value, values of declared types read back, each limit refused by the reader and by
the writer with its name, a count larger than the bytes left, errors that name the
type, the constructor and the field, and, over every short byte string, that whatever reads is
what the writer writes. The laws are `Body.read_write` and `Body.write_read`; these run the
compiled code. -/

namespace Tests.Body

open Lanes

def limits : Codec.Limits := {}

def bytesOf (s : Schema) (v : Value) (l : Codec.Limits := limits) : Option (List UInt8) :=
  match Body.write l s v with
  | .ok b => some b.toList
  | .error _ => none

/-- The error of reading `bytes`, or `none` if they read. -/
def refusal (s : Schema) (bytes : List UInt8) (l : Codec.Limits := limits) :
    Option Codec.Error :=
  match Body.read l s bytes.toByteArray with
  | .ok _ => none
  | .error e => some e

/-- The error of writing `v`, or `none` if it is written. -/
def writeRefusal (s : Schema) (v : Value) (l : Codec.Limits := limits) : Option Codec.Error :=
  match Body.write l s v with
  | .ok _ => none
  | .error e => some e

/-- Written with the type's codec, then read back to the same value and the same `α`. -/
def roundTrip {α : Type} [BEq α] (c : Codec α) (a : α) : Bool :=
  match Body.write limits c.schema (c.toValue a) with
  | .ok bytes =>
    match Body.read limits c.schema bytes with
    | .ok v => v == c.toValue a && c.ofValue v == some a
    | .error _ => false
  | .error _ => false

/-- Every byte string up to `n` bytes long. -/
def strings : Nat → List (List UInt8)
  | 0 => [[]]
  | n + 1 => [] :: (strings n).flatMap fun s => (List.range 256).map fun b => b.toUInt8 :: s

/-- Whatever reads is written back as the same bytes. -/
def canonical (s : Schema) (n : Nat) (l : Codec.Limits := limits) : Bool :=
  (strings n).all fun bytes =>
    match Body.read l s bytes.toByteArray with
    | .ok v => bytesOf s v l == some bytes
    | .error _ => true

def Part : Bool → Type
  | true => Nat
  | false => String

def partCodec : (i : Bool) → Codec (Part i)
  | true => Codec.nat
  | false => Codec.string

def sigma : Codec ((i : Bool) × Part i) := Codec.sigma Codec.bool partCodec

/-- A pair of `sigma` read back as itself. -/
def sigmaRoundTrip (x : (i : Bool) × Part i) : Bool :=
  match Body.write limits sigma.schema (sigma.toValue x) with
  | .ok bytes =>
    match Body.read limits sigma.schema bytes with
    | .ok v => v == sigma.toValue x && (sigma.ofValue v).isSome
    | .error _ => false
  | .error _ => false

/-- Where a circle whose centre is cut short ends. -/
def cutCentre : Codec.Error :=
  { offset := 3, problem := .ended,
    path := [.type "Tests.Schema.Shape", .ctor "circle", .field "centre",
      .type "Tests.Schema.Point", .field "label"] }

def point : Schema := (Codec.of Tests.Schema.Point).schema
def shape : Schema := (Codec.of (Tests.Schema.Shape String)).schema

def tests : List (String × Bool) :=
  [ ("body: a number is LEB128, an integer its zigzag, a string its length and bytes",
      bytesOf .nat (.nat 0) == some [0] && bytesOf .nat (.nat 127) == some [127]
        && bytesOf .nat (.nat 300) == some [0xac, 0x02]
        && bytesOf .int (.int 0) == some [0] && bytesOf .int (.int (-1)) == some [1]
        && bytesOf .int (.int 1) == some [2] && bytesOf .int (.int (-65)) == some [0x81, 0x01]
        && bytesOf .string (.string "ab") == some [2, 97, 98]
        && bytesOf .bytes (.bytes ⟨#[7]⟩) == some [1, 7] && bytesOf .unit (.ctor 0 []) == some []),
    ("body: a record is its fields in order, a sum its index then its fields, with no names",
      bytesOf point ((Codec.of Tests.Schema.Point).toValue ⟨-1, 2, none⟩) == some [1, 4, 0]
        && bytesOf shape ((Codec.of (Tests.Schema.Shape String)).toValue (.circle ⟨0, 0, none⟩ 5))
          == some [1, 0, 0, 0, 5]
        && bytesOf (.list .nat) (.list [.nat 1, .nat 2]) == some [2, 1, 2]
        && bytesOf (.map .string .nat) (.list [.ctor 0 [.string "a", .nat 1]])
          == some [1, 1, 97, 1]),
    ("body: the second part of a dependent pair is written with tags",
      bytesOf sigma.schema (sigma.toValue ⟨true, (3 : Nat)⟩) == some [1, 0, 3]
        && bytesOf sigma.schema (sigma.toValue ⟨false, "x"⟩) == some [0, 2, 1, 120]
        && bytesOf (.dependent .unit) (.ctor 0 [.ctor 0 [], .ctor 2 [.list [.int (-1)]]])
          == some [5, 2, 1, 4, 1, 1, 1]
        && sigmaRoundTrip ⟨true, (3 : Nat)⟩ && sigmaRoundTrip ⟨false, "x"⟩),
    ("body: values of declared types read back as themselves",
      Tests.Schema.shapes.all (roundTrip (Codec.of (Tests.Schema.Shape String)))
        && Tests.Codec.shapes.all (roundTrip (Codec.of Tests.Codec.Shape))
        && roundTrip (Codec.of (Std.ExtTreeMap String Nat)) (.ofList [("b", 2), ("a", 1)])
        && roundTrip (Codec.of (Option (List (Int × Bool)))) (some [(-5, true), (7, false)])
        && roundTrip (Codec.of (Nat ⊕ Unit)) (.inr ())
        && roundTrip (Codec.of Nat) (2 ^ 200)),
    ("body: whatever reads is written back as the same bytes",
      canonical .nat 2 && canonical .int 2 && canonical (.list .unit) 2
        && canonical (.list .nat) 2 && canonical .string 2 && canonical point 2
        && canonical (.dependent .nat) 2
        && canonical shape 2 { maxItems := 2, maxNumberBytes := 1, maxDepth := 2 }),
    ("body: a number with a needless last byte is refused, and bytes after the value",
      refusal .nat [0x80, 0x00] == some { offset := 0, problem := .padded }
        && refusal .nat [0x81, 0x00] == some { offset := 0, problem := .padded }
        && refusal .nat [0x01, 0x00] == some { offset := 1, problem := .trailing 1 }
        && refusal .nat [0x80] == some { offset := 1, problem := .ended }),
    ("body: a count larger than the bytes left is refused before any item is read",
      refusal (.list .nat) [5, 1] == some { offset := 1, problem := .overrun 5 1 }
        && refusal .string [3, 97] == some { offset := 1, problem := .overrun 3 1 }
        && refusal (.list .unit) [3] == none),
    ("body: a list of a type written as no bytes is bounded by maxItems, at once",
      refusal (.list .unit) [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x0f]
          == some { offset := 0, problem := .limit "maxItems" limits.maxItems }
        && refusal (.list .unit) [3] { maxItems := 2 }
          == some { offset := 0, problem := .limit "maxItems" 2 }
        && writeRefusal (.list .unit) (.list [.ctor 0 [], .ctor 0 [], .ctor 0 []]) { maxItems := 2 }
          == some { offset := 0, problem := .limit "maxItems" 2 }),
    ("body: each limit is refused by the reader and by the writer, named",
      refusal .string [3, 97, 98, 99] { maxLength := 2 }
          == some { offset := 0, problem := .limit "maxLength" 2 }
        && writeRefusal .string (.string "abc") { maxLength := 2 }
          == some { offset := 0, problem := .limit "maxLength" 2 }
        && refusal .nat [0x80, 0x01] { maxNumberBytes := 1 }
          == some { offset := 0, problem := .limit "maxNumberBytes" 1 }
        && writeRefusal .nat (.nat 128) { maxNumberBytes := 1 }
          == some { offset := 0, problem := .limit "maxNumberBytes" 1 }
        && refusal (.list (.list .nat)) [1, 0] { maxDepth := 1 }
          == some { offset := 1, path := [.item 0], problem := .limit "maxDepth" 1 }
        && writeRefusal (.list (.list .nat)) (.list [.list []]) { maxDepth := 1 }
          == some { offset := 1, path := [.item 0], problem := .limit "maxDepth" 1 }
        && refusal .bytes [3, 0, 0, 0] { maxBytes := 3 }
          == some { offset := 0, problem := .limit "maxBytes" 3 }
        && writeRefusal .bytes (.bytes ⟨#[0, 0, 0]⟩) { maxBytes := 3 }
          == some { offset := 0, problem := .limit "maxBytes" 3 }
        && refusal (.dependent .nat) [0, 4, 1, 4, 0] { maxDepth := 2 }
          == some { offset := 3, path := [.item 1, .item 0], problem := .limit "maxDepth" 2 }),
    ("body: an error names the type, the constructor, the field and the byte",
      refusal shape [1, 0, 0] == some cutCentre
        && refusal shape [9]
          == some { offset := 0, path := [.type "Tests.Schema.Shape"], problem := .index 9 5 }
        && refusal .string [1, 0xff] == some { offset := 0, problem := .utf8 }
        && refusal (.dependent .nat) [0, 9]
          == some { offset := 1, path := [.item 1], problem := .tag 9 }
        && (refusal shape [1, 0, 0]).map toString
          == some "byte 3, Tests.Schema.Shape.circle.centre / Tests.Schema.Point.label: the bytes \
            end inside a value"),
    ("body: a value that does not fit its schema is not written",
      writeRefusal .nat (.int 0) == some { offset := 0, problem := .misfit }
        && writeRefusal point (.ctor 0 [.int 0])
          == some { offset := 1, path := [.type "Tests.Schema.Point"], problem := .misfit }
        && writeRefusal shape (.ctor 7 []) == some { offset := 0, problem := .misfit }) ]

end Tests.Body
