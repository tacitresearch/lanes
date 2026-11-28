/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-! Matching by name (`Lanes/Data/Match.lean`): values written with one version of a type read
as values of the next, by each rule of the data-format decision (section 3.2), and each refusal,
named. The laws are in `Lanes/Data/MatchSound.lean`; these run the compiled code. -/

namespace Tests.Match

open Lanes

namespace V1

lanes_data structure Point where
  x : Int
  y : Int
  colour : String
  deriving DecidableEq, Repr, Codable

lanes_data inductive Shape where
  | dot
  | circle (centre : Point) (radius : Nat)
  | line (points : List Point) (shut : Bool)
  | blob (size : Nat)
  deriving DecidableEq, Repr, Codable

end V1

-- The next version: a field added with a default, a field renamed, a field removed, fields
-- and constructors reordered, a constructor and an argument renamed, a constructor added and one
-- removed.
namespace V2

lanes_data structure Point where
  label : String := "here"
  height (was y) : Int := 0
  x : Int
  deriving DecidableEq, Repr, Codable

lanes_data inductive Shape where
  | square (side : Nat)
  | path (was line) (points : List Point) (closed (was shut) : Bool)
  | circle (centre : Point) (radius : Nat)
  | dot
  deriving DecidableEq, Repr, Codable

end V2

/-- A field added without a default. -/
lanes_data structure Plain where
  x : Int
  y : Int
  colour : String
  z : Int
  deriving DecidableEq, Repr, Codable

lanes_data inductive PlainShape where
  | dot
  | line (points : List Plain) (shut : Bool)
  deriving DecidableEq, Repr, Codable

/-- A field renamed without its former name, once with a default and once without. -/
lanes_data structure Renamed where
  x : Int
  height : Int := 7
  colour : String
  deriving DecidableEq, Repr, Codable

lanes_data structure RenamedBare where
  x : Int
  height : Int
  colour : String
  deriving DecidableEq, Repr, Codable

/-- A field whose type changed, once with a migration from `V1.Point`. -/
lanes_data structure Changed where
  x : String
  y : Int
  colour : String
  deriving DecidableEq, Repr, Codable

lanes_data structure Migrated where
  x : String
  y : Int
  deriving DecidableEq, Repr, Codable
  from V1.Point := fun p => { x := toString p.x, y := p.y }

lanes_data inductive MigratedShape where
  | dot
  | circle (centre : Migrated) (radius : Nat)
  deriving DecidableEq, Repr, Codable

/-- Two fields that take the data's `x`, one by its name and one by a former name. -/
lanes_data structure Twice where
  x : Int
  again (was x) : Int
  deriving DecidableEq, Repr, Codable

lanes_data inductive TwiceShape where
  | dot (was blob)
  | spot (was dot)
  | circle (centre : V1.Point) (radius : Nat)
  deriving DecidableEq, Repr, Codable

def limits : Codec.Limits := {}

def migrations : List Schema.Migration :=
  [.of (Codec.of V1.Point).toOf (Codec.of Migrated).toOf Migrated.migrate]

/-- The plan from `α`'s schema to `β`'s. -/
def plan (α β : Type) [Codable α] [Codable β] (ms : List Schema.Migration := []) :
    Except Codec.Error Schema.Plan :=
  Schema.Plan.of ms (Codec.of α).schema (Codec.of β).schema

/-- The refusal of the plan from `α`'s schema to `β`'s, or `none`. -/
def refusal (α β : Type) [Codable α] [Codable β] : Option Codec.Error :=
  match plan α β with
  | .ok _ => none
  | .error e => some e

/-- `a`, written as an `α`, read as a `β`. -/
def readAs {α : Type} (β : Type) [Codable α] [Codable β] (a : α)
    (ms : List Schema.Migration := []) : Except Codec.Error β :=
  match plan α β ms, Body.encode limits (Codec.of α).toOf a with
  | .ok p, .ok bytes => Body.decodeWith limits (Codec.of α).schema p (Codec.of β).toOf bytes
  | .error e, _ | _, .error e => .error e

def isOk {α : Type} [DecidableEq α] (r : Except Codec.Error α) (a : α) : Bool :=
  match r with
  | .ok b => b = a
  | .error _ => false

def isError {α : Type} (r : Except Codec.Error α) (e : Codec.Error) : Bool :=
  match r with
  | .ok _ => false
  | .error e' => e' = e

/-- A refusal found when matching, which is at no byte. -/
def err (path : List Codec.Error.Step) (problem : Codec.Error.Problem) : Codec.Error :=
  { offset := 0, path, problem }

def isSame : Except Codec.Error Schema.Plan → Bool
  | .ok .same => true
  | _ => false

def v1Shapes : List V1.Shape :=
  [.dot, .circle ⟨1, -2, "red"⟩ 3, .line [⟨0, 5, ""⟩, ⟨-7, 8, "blue"⟩] true, .line [] false]

def v2Shapes : List V2.Shape :=
  [.dot, .circle { x := 1, height := -2 } 3, .path [{ x := 0, height := 5 }, { x := -7, height := 8 }] true,
    .path [] false]

def point : Schema := (Codec.of V2.Point).schema

def tests : List (String × Bool) :=
  [ ("match: the same schema needs no plan, and reads every value as itself",
      isSame (plan V2.Shape V2.Shape) && isSame (plan Nat Nat)
        && v2Shapes.all fun s => isOk (readAs V2.Shape s) s),
    ("match: a field added with a default takes it, and a renamed field reads through its \
        former name",
      isOk (readAs V2.Point (V1.Point.mk 3 4 "red")) { label := "here", height := 4, x := 3 }),
    ("match: a removed field is skipped, and reordered fields and constructors are matched by name",
      (v1Shapes.zip v2Shapes).all fun (a, b) => isOk (readAs V2.Shape a) b),
    ("match: a renamed constructor reads through its former name, with a renamed argument",
      isOk (readAs V2.Shape (V1.Shape.line [⟨1, 2, "x"⟩] true))
        (.path [{ x := 1, height := 2 }] true)),
    ("match: an added constructor is accepted, and a removed one absent from the data",
      isOk (readAs V2.Shape V1.Shape.dot) .dot && (plan V1.Shape V2.Shape).toBool),
    ("match: a constructor of the data that the reader's type lacks is refused when met, named",
      isError (readAs V2.Shape (V1.Shape.blob 3))
        (err [.type "Tests.Match.V2.Shape", .ctor "blob"] .absent)),
    ("match: values inside lists, options, pairs and maps are matched",
      isOk (readAs (List (Option V2.Point)) [some (V1.Point.mk 1 2 ""), none])
          [some { x := 1, height := 2 }, none]
        && isOk (readAs (Std.ExtTreeMap String V2.Point)
            (Std.ExtTreeMap.ofList [("a", V1.Point.mk 1 2 "")] : Std.ExtTreeMap String V1.Point))
          (.ofList [("a", ({ x := 1, height := 2 } : V2.Point))])
        && isOk (readAs (V2.Point × Nat) (V1.Point.mk 1 2 "", 5)) ({ x := 1, height := 2 }, 5)),
    ("match: a field added without a default is refused at open, named",
      refusal V1.Point Plain
          == some (err [.type "Tests.Match.Plain", .field "z"] .noDefault)
        && refusal V1.Shape PlainShape
          == some (err [.type "Tests.Match.PlainShape", .ctor "line",
            .field "points", .type "Tests.Match.Plain", .field "z"] .noDefault)),
    ("match: a rename without a former name is a removal and an addition",
      isOk (readAs Renamed (V1.Point.mk 3 4 "red")) { x := 3, height := 7, colour := "red" }
        && refusal V1.Point RenamedBare
          == some (err [.type "Tests.Match.RenamedBare", .field "height"] .noDefault)),
    ("match: a field whose type changed is refused at open, naming both types",
      refusal V1.Point Changed
          == some (err [.type "Tests.Match.Changed", .field "x"] (.changed "Int" "String"))
        && refusal Nat String == some (err [] (.changed "Nat" "String"))
        && (Schema.Plan.of [] (.dependent .nat) (.dependent .int)).toOption.isNone),
    ("match: a type with a declared migration is read through it",
      isOk (readAs Migrated (V1.Point.mk (-3) 4 "red") migrations) { x := "-3", y := 4 }
        && isOk (readAs MigratedShape (V1.Shape.circle ⟨1, 2, ""⟩ 5) migrations)
          (.circle { x := "1", y := 2 } 5)
        && refusal V1.Point Migrated
          == some (err [.type "Tests.Match.Migrated", .field "x"] (.changed "Int" "String"))),
    ("match: two of the reader's names that take one of the data's are refused at open",
      refusal V1.Point Twice
          == some (err [.type "Tests.Match.Twice", .field "again"] (.ambiguous "x"))
        && refusal V1.Shape TwiceShape
          == some (err [.type "Tests.Match.TwiceShape", .ctor "spot"] (.ambiguous "dot"))),
    ("match: a value that does not fit the writer's schema is refused",
      isError ((Schema.Plan.record "T" [.take "x" 0 .same]).apply (.nat 1))
          (err [] .misfit)
        && isError ((Schema.Plan.record "T" [.take "x" 1 .same]).apply (.ctor 0 [.nat 1]))
          (err [.type "T"] .misfit)),
    ("match: a refusal found by matching names no byte",
      (refusal V1.Point Plain).map toString
          == some "Tests.Match.Plain.z: a field the data does not have, with no default"
        && (refusal Nat String).map toString
          == some "the data's type is Nat, the reader's String") ]

end Tests.Match
