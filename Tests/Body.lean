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
what the writer writes; then a type's values through `Body.encode` and `Body.decode`. The laws are `Body.read_write` and `Body.write_read`; these run the
compiled code. -/

namespace Tests.Body

open Lanes

def limits : Codec.Limits := {}

/-- The schema of a type with no named type in it. -/
def ty (t : Schema.Ty) : Schema := ⟨[], t⟩

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

/-- Encoded with `Body.encode`, then decoded as itself. -/
def decoded {α : Type} [BEq α] (c : Codec α) (a : α) : Bool :=
  match Body.encode limits c.toOf a with
  | .ok bytes =>
    match Body.decode limits c.toOf bytes with
    | .ok b => b == a
    | .error _ => false
  | .error _ => false

/-- The error of decoding `bytes` as an `α`, or `none` if they decode. -/
def decodeRefusal {α : Type} (c : Codec α) (bytes : List UInt8) : Option Codec.Error :=
  match Body.decode limits c.toOf bytes.toByteArray with
  | .ok _ => none
  | .error e => some e

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
      bytesOf (ty .nat) (.nat 0) == some [0] && bytesOf (ty .nat) (.nat 127) == some [127]
        && bytesOf (ty .nat) (.nat 300) == some [0xac, 0x02]
        && bytesOf (ty .int) (.int 0) == some [0] && bytesOf (ty .int) (.int (-1)) == some [1]
        && bytesOf (ty .int) (.int 1) == some [2] && bytesOf (ty .int) (.int (-65)) == some [0x81, 0x01]
        && bytesOf (ty .string) (.string "ab") == some [2, 97, 98]
        && bytesOf (ty .bytes) (.bytes ⟨#[7]⟩) == some [1, 7] && bytesOf (ty .unit) (.ctor 0 []) == some []),
    ("body: a record is its fields in order, a sum its index then its fields, with no names",
      bytesOf point ((Codec.of Tests.Schema.Point).toValue ⟨-1, 2, none⟩) == some [1, 4, 0]
        && bytesOf shape ((Codec.of (Tests.Schema.Shape String)).toValue (.circle ⟨0, 0, none⟩ 5))
          == some [1, 0, 0, 0, 5]
        && bytesOf (ty (.list .nat)) (.list [.nat 1, .nat 2]) == some [2, 1, 2]
        && bytesOf (ty (.map .string .nat)) (.list [.ctor 0 [.string "a", .nat 1]])
          == some [1, 1, 97, 1]),
    ("body: the second part of a dependent pair is written with tags",
      bytesOf sigma.schema (sigma.toValue ⟨true, (3 : Nat)⟩) == some [1, 0, 3]
        && bytesOf sigma.schema (sigma.toValue ⟨false, "x"⟩) == some [0, 2, 1, 120]
        && bytesOf (ty (.dependent .unit)) (.ctor 0 [.ctor 0 [], .ctor 2 [.list [.int (-1)]]])
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
      canonical (ty .nat) 2 && canonical (ty .int) 2 && canonical (ty (.list .unit)) 2
        && canonical (ty (.list .nat)) 2 && canonical (ty .string) 2 && canonical point 2
        && canonical (ty (.dependent .nat)) 2
        && canonical shape 2 { maxItems := 2, maxNumberBytes := 1, maxDepth := 2 }),
    ("body: a number with a needless last byte is refused, and bytes after the value",
      refusal (ty .nat) [0x80, 0x00] == some { offset := 0, problem := .padded }
        && refusal (ty .nat) [0x81, 0x00] == some { offset := 0, problem := .padded }
        && refusal (ty .nat) [0x01, 0x00] == some { offset := 1, problem := .trailing 1 }
        && refusal (ty .nat) [0x80] == some { offset := 1, problem := .ended }),
    ("body: a count larger than the bytes left is refused before any item is read",
      refusal (ty (.list .nat)) [5, 1] == some { offset := 1, problem := .overrun 5 1 }
        && refusal (ty .string) [3, 97] == some { offset := 1, problem := .overrun 3 1 }
        && refusal (ty (.list .unit)) [3] == none),
    ("body: a list of a type written as no bytes is bounded by maxItems, at once",
      refusal (ty (.list .unit)) [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x0f]
          == some { offset := 0, problem := .limit "maxItems" limits.maxItems }
        && refusal (ty (.list .unit)) [3] { maxItems := 2 }
          == some { offset := 0, problem := .limit "maxItems" 2 }
        && writeRefusal (ty (.list .unit)) (.list [.ctor 0 [], .ctor 0 [], .ctor 0 []]) { maxItems := 2 }
          == some { offset := 0, problem := .limit "maxItems" 2 }),
    ("body: each limit is refused by the reader and by the writer, named",
      refusal (ty .string) [3, 97, 98, 99] { maxLength := 2 }
          == some { offset := 0, problem := .limit "maxLength" 2 }
        && writeRefusal (ty .string) (.string "abc") { maxLength := 2 }
          == some { offset := 0, problem := .limit "maxLength" 2 }
        && refusal (ty .nat) [0x80, 0x01] { maxNumberBytes := 1 }
          == some { offset := 0, problem := .limit "maxNumberBytes" 1 }
        && writeRefusal (ty .nat) (.nat 128) { maxNumberBytes := 1 }
          == some { offset := 0, problem := .limit "maxNumberBytes" 1 }
        && refusal (ty (.list (.list .nat))) [1, 0] { maxDepth := 1 }
          == some { offset := 1, path := [.item 0], problem := .limit "maxDepth" 1 }
        && writeRefusal (ty (.list (.list .nat))) (.list [.list []]) { maxDepth := 1 }
          == some { offset := 1, path := [.item 0], problem := .limit "maxDepth" 1 }
        && refusal (ty .bytes) [3, 0, 0, 0] { maxBytes := 3 }
          == some { offset := 0, problem := .limit "maxBytes" 3 }
        && writeRefusal (ty .bytes) (.bytes ⟨#[0, 0, 0]⟩) { maxBytes := 3 }
          == some { offset := 0, problem := .limit "maxBytes" 3 }
        && refusal (ty (.dependent .nat)) [0, 4, 1, 4, 0] { maxDepth := 2 }
          == some { offset := 3, path := [.item 1, .item 0], problem := .limit "maxDepth" 2 }),
    ("body: an error names the type, the constructor, the field and the byte",
      refusal shape [1, 0, 0] == some cutCentre
        && refusal shape [9]
          == some { offset := 0, path := [.type "Tests.Schema.Shape"], problem := .index 9 5 }
        && refusal (ty .string) [1, 0xff] == some { offset := 0, problem := .utf8 }
        && refusal (ty (.dependent .nat)) [0, 9]
          == some { offset := 1, path := [.item 1], problem := .tag 9 }
        && (refusal shape [1, 0, 0]).map toString
          == some "byte 3, Tests.Schema.Shape.circle.centre / Tests.Schema.Point.label: the bytes \
            end inside a value"),
    ("body: a value that does not fit its schema is not written",
      writeRefusal (ty .nat) (.int 0) == some { offset := 0, problem := .misfit }
        && writeRefusal point (.ctor 0 [.int 0])
          == some { offset := 1, path := [.type "Tests.Schema.Point"], problem := .misfit }
        && writeRefusal shape (.ctor 7 []) == some { offset := 0, problem := .misfit }),
    ("body: a type that refers to itself is written and read back, bounded by maxDepth",
      bytesOf Tests.Schema.tree Tests.Schema.treeValue == some [1, 1, 0, 1, 0, 2, 0]
        && (Body.write limits Tests.Schema.tree Tests.Schema.treeValue).toOption.bind
            (fun b => (Body.read limits Tests.Schema.tree b).toOption)
          == some Tests.Schema.treeValue
        && refusal Tests.Schema.tree [1, 1, 0, 1, 0, 2, 0] { maxDepth := 2 }
          == some { offset := 2, path := [.type "Tree", .ctor "node", .field "left", .type "Tree",
            .ctor "node", .field "left"], problem := .limit "maxDepth" 2 }),
    ("body: a type the schema does not declare is refused, named",
      refusal ⟨[], .ref "Gone"⟩ [0] == some { offset := 0, problem := .undeclared "Gone" }
        && writeRefusal ⟨[], .ref "Gone"⟩ (.ctor 0 [])
          == some { offset := 0, problem := .undeclared "Gone" }),
    ("body: a type's value is encoded and decoded, and a value its type does not take is refused",
      decoded (Codec.of (Tests.Schema.Shape String)) (.circle ⟨1, -2, none⟩ 3)
        && decoded (Codec.of (Fin 3)) 2
        && decodeRefusal (Codec.of (Fin 3)) [5] == some { offset := 0, problem := .refused }
        && decodeRefusal (Codec.of (Fin 3)) [2] == none
        && decodeRefusal (Codec.of (Fin 3)) [2, 0]
          == some { offset := 1, problem := .trailing 1 }) ]

end Tests.Body
