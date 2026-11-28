/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Data.Body

/-!
Matching by name: reading a value written under one schema, the writer's, which a file holds,
as a value of another, the reader's, which the binary holds. `Schema.Plan.of` compares the two
once, when a file is opened, and refuses there what no value could get past. `Plan.apply` then
turns each value read with the writer's schema into one of the reader's, by index.

A reader's field takes the writer's field of its name, or else of the first of its former names
the writer has; a field the writer lacks takes its default. A writer's field no reader's field
takes is dropped. Constructors are matched the same way; one of the data's that the reader's type
lacks is refused when it is met. Equal schemas need no plan (`Plan.same`). The names of types are
not compared: a type is reached through its place, so a renamed type needs no former name. A
declared migration is used where the writer's schema is its old one and the reader's its new one.
-/

@[expose] public section

namespace Lanes

namespace Schema

open Codec (Error)
open Body (fail within)

/-- How a value of a type's previous version becomes one of this, as values: `from Old := f`
over the two types' schemas. -/
structure Migration where
  old : Schema
  new : Schema
  run : Value → Option Value

/-- A reader's field: the writer's field at `index`, through a plan, or a default. -/
inductive Plan.Field (π : Type) where
  | take (name : String) (index : Nat) (plan : π)
  | fill (value : Value)

/-- What becomes of a writer's constructor: refused, or the reader's constructor at `index`,
with its fields as they are (`none`) or through a plan of each. -/
inductive Plan.Ctor (π : Type) where
  | absent (name : String)
  | to (name : String) (index : Nat) (fields : Option (List (Plan.Field π)))

/-- How a value of the writer's schema becomes one of the reader's. A record's fields are the
reader's, in its order; a sum's constructors are the writer's, in its order. -/
inductive Plan where
  | same
  | list (item : Plan)
  | map (key value : Plan)
  | record (type : String) (fields : List (Plan.Field Plan))
  | sum (type : String) (ctors : List (Plan.Ctor Plan))
  | convert (type : String) (run : Value → Option Value)

namespace Plan

/-- The writer's index that a reader's name takes: its own name first, then its former names in
order. -/
def claim (names : List String) (name : String) (aliases : List String) : Option Nat :=
  match names.idxOf? name with
  | some k => some k
  | none => aliases.findSome? names.idxOf?

/-- The first of the reader's names, with the writer's index it takes, that takes an index an
earlier one took. -/
def clash : List (String × Option Nat) → List Nat → Option (String × Nat)
  | [], _ => none
  | (_, none) :: cs, seen => clash cs seen
  | (name, some k) :: cs, seen => if k ∈ seen then some (name, k) else clash cs (k :: seen)

/-- Refused if two of the reader's names take one of the writer's. -/
def unambiguous (step : String → Error.Step) (names : List String)
    (claims : List (String × Option Nat)) : Except Error Unit :=
  match clash claims [] with
  | none => .ok ()
  | some (name, k) => within (step name) (fail 0 (.ambiguous (names[k]?.getD "")))

/-- The plan of the writer's constructor `k`, from what the reader's constructors take. -/
def pick : List (Option (Nat × Ctor Plan)) → Nat → String → Ctor Plan
  | [], _, name => .absent name
  | none :: found, k, name => pick found k name
  | some (k', c) :: found, k, name => if k' = k then c else pick found k name

variable (ms : List Migration)

mutual

/-- The plan from `w`, the writer's schema, to `r`, the reader's; refused, naming what changed,
if a value could not be read. -/
def of (w r : Schema) : Except Error Plan :=
  if w == r then .ok .same else
  match ms.find? (fun m => m.old == w && m.new == r) with
  | some m => .ok (.convert r.name m.run)
  | none =>
    match w, r with
    | .list wi, .list ri =>
      match of wi ri with
      | .ok p => .ok (.list p)
      | .error e => .error e
    | .map wk wv, .map rk rv =>
      match within (.field "key") (of wk rk) with
      | .error e => .error e
      | .ok pk =>
        match within (.field "value") (of wv rv) with
        | .ok pv => .ok (.map pk pv)
        | .error e => .error e
    | .record _ _ wfs, .record type _ rfs =>
      let names := wfs.map (·.name)
      match within (.type type) (unambiguous .field names
          (rfs.map fun f => (f.name, claim names f.name f.aliases))) with
      | .error e => .error e
      | .ok () =>
        match within (.type type) (ofFields wfs rfs) with
        | .ok ps => .ok (.record type ps)
        | .error e => .error e
    | .sum _ _ wcs, .sum type _ rcs =>
      let names := wcs.map (·.name)
      match within (.type type) (unambiguous .ctor names
          (rcs.map fun c => (c.name, claim names c.name c.aliases))) with
      | .error e => .error e
      | .ok () =>
        match within (.type type) (ofCtors wcs rcs 0) with
        | .ok found => .ok (.sum type (wcs.mapIdx fun k c => pick found k c.name))
        | .error e => .error e
    | w, r => fail 0 (.changed w.name r.name)

/-- The plan of each of the reader's fields `rfs` from the writer's `wfs`. -/
def ofFields (wfs : List (Schema.Field Schema)) :
    List (Schema.Field Schema) → Except Error (List (Plan.Field Plan))
  | [] => .ok []
  | ⟨name, aliases, s, default⟩ :: rfs =>
    let head : Except Error (Plan.Field Plan) :=
      match claim (wfs.map (·.name)) name aliases with
      | some k =>
        match wfs[k]? with
        | some g =>
          match within (.field name) (of g.schema s) with
          | .ok p => .ok (.take name k p)
          | .error e => .error e
        | none => fail 0 .misfit
      | none =>
        match default with
        | some v => .ok (.fill v)
        | none => within (.field name) (fail 0 .noDefault)
    match head with
    | .error e => .error e
    | .ok p =>
      match ofFields wfs rfs with
      | .ok ps => .ok (p :: ps)
      | .error e => .error e

/-- For each of the reader's constructors `rcs`, from the `index`th: the writer's constructor
it takes, if any, and that constructor's plan. -/
def ofCtors (wcs : List (Schema.Ctor Schema)) :
    List (Schema.Ctor Schema) → Nat → Except Error (List (Option (Nat × Ctor Plan)))
  | [], _ => .ok []
  | ⟨name, aliases, fields⟩ :: rcs, index =>
    let head : Except Error (Option (Nat × Ctor Plan)) :=
      match claim (wcs.map (·.name)) name aliases with
      | none => .ok none
      | some k =>
        match wcs[k]? with
        | none => fail 0 .misfit
        | some c =>
          if Schema.beqFields c.fields fields then .ok (some (k, .to name index none))
          else
            match within (.ctor name) (ofFields c.fields fields) with
            | .ok ps => .ok (some (k, .to name index (some ps)))
            | .error e => .error e
    match head with
    | .error e => .error e
    | .ok x =>
      match ofCtors wcs rcs (index + 1) with
      | .ok xs => .ok (x :: xs)
      | .error e => .error e

end

mutual

/-- The reader's value of `v`, a value of the writer's schema. -/
def apply : Plan → Value → Except Error Value
  | .same, v => .ok v
  | .list item, .list vs =>
    match applyItems item vs 0 with
    | .ok us => .ok (.list us)
    | .error e => .error e
  | .map key value, .list es =>
    match applyEntries key value es 0 with
    | .ok us => .ok (.list us)
    | .error e => .error e
  | .record type fields, .ctor 0 vs =>
    match within (.type type) (applyFields fields vs) with
    | .ok us => .ok (.ctor 0 us)
    | .error e => .error e
  | .sum type ctors, .ctor k vs => within (.type type) (applyCtor ctors k vs)
  | .convert type run, v =>
    match run v with
    | some u => .ok u
    | none => within (.type type) (fail 0 .refused)
  | _, _ => fail 0 .misfit
termination_by p => (2 * sizeOf p, 0)

def applyItems (item : Plan) (vs : List Value) (index : Nat) : Except Error (List Value) :=
  match vs with
  | [] => .ok []
  | v :: vs =>
    match within (.item index) (apply item v) with
    | .error e => .error e
    | .ok u =>
      match applyItems item vs (index + 1) with
      | .ok us => .ok (u :: us)
      | .error e => .error e
termination_by (2 * sizeOf item + 1, vs.length)

def applyEntries (key value : Plan) (es : List Value) (index : Nat) :
    Except Error (List Value) :=
  match es with
  | [] => .ok []
  | .ctor 0 [k, v] :: es =>
    match within (.item index) (within (.field "key") (apply key k)) with
    | .error e => .error e
    | .ok k =>
      match within (.item index) (within (.field "value") (apply value v)) with
      | .error e => .error e
      | .ok v =>
        match applyEntries key value es (index + 1) with
        | .ok us => .ok (.ctor 0 [k, v] :: us)
        | .error e => .error e
  | _ :: _ => within (.item index) (fail 0 .misfit)
termination_by (2 * (sizeOf key + sizeOf value) + 1, es.length)

def applyFields (fields : List (Plan.Field Plan)) (vs : List Value) :
    Except Error (List Value) :=
  match fields with
  | [] => .ok []
  | .take name k p :: fields =>
    match vs[k]? with
    | none => fail 0 .misfit
    | some v =>
      match within (.field name) (apply p v) with
      | .error e => .error e
      | .ok u =>
        match applyFields fields vs with
        | .ok us => .ok (u :: us)
        | .error e => .error e
  | .fill u :: fields =>
    match applyFields fields vs with
    | .ok us => .ok (u :: us)
    | .error e => .error e
termination_by (2 * sizeOf fields + 1, 0)

def applyCtor (ctors : List (Plan.Ctor Plan)) (k : Nat) (vs : List Value) :
    Except Error Value :=
  match ctors, k with
  | [], _ => fail 0 .misfit
  | .absent name :: _, 0 => within (.ctor name) (fail 0 .absent)
  | .to _ j none :: _, 0 => .ok (.ctor j vs)
  | .to name j (some fields) :: _, 0 =>
    match within (.ctor name) (applyFields fields vs) with
    | .ok us => .ok (.ctor j us)
    | .error e => .error e
  | _ :: ctors, k + 1 => applyCtor ctors k vs
termination_by (2 * sizeOf ctors + 1, 0)

end

end Plan

namespace Migration

variable {α β : Type}

/-- The migration from `old`'s values to `new`'s through `f`. -/
def of (old : Schema.Of α) (new : Schema.Of β) (f : α → β) : Migration where
  old := old.schema
  new := new.schema
  run v := (old.ofValue v).map fun a => new.toValue (f a)

end Migration

end Schema

namespace Body

open Codec (Limits Error)

variable {α : Type}

/-- The reader's value that is all of `bytes`, written with the schema `writer`, through `plan`,
the plan from `writer` to the reader's schema. -/
def readWith (limits : Limits) (writer : Schema) (plan : Schema.Plan) (bytes : ByteArray) :
    Except Error Value :=
  match read limits writer bytes with
  | .ok v => plan.apply v
  | .error e => .error e

/-- The `α` that is all of `bytes`, written with the schema `writer`, through `plan`, the plan
from `writer` to `s.schema`. Refused as `decode` refuses. -/
def decodeWith (limits : Limits) (writer : Schema) (plan : Schema.Plan) (s : Schema.Of α)
    (bytes : ByteArray) : Except Error α :=
  match readWith limits writer plan bytes with
  | .error e => .error e
  | .ok v =>
    match s.ofValue v with
    | some a => .ok a
    | none =>
      match s.schema with
      | .record type _ _ | .sum type _ _ => within (.type type) (fail 0 .refused)
      | _ => fail 0 .refused

end Body

end Lanes
