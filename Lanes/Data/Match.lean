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
declared migration is used where the writer's type is its old one and the reader's its new one.

A pair of named types, the writer's and the reader's, is matched once, the first time it is met,
and its plan is kept in the plan's table (`Plan.pairs`); every other place it is met refers to it.
Named types that are one type in both schemas, declared the same down every type they use, need
no plan at all (`Plan.alike`). A type that refers to itself is matched so too: a pair met while
it is being matched refers to the plan being made.
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

/-- How a value of the writer's type becomes one of the reader's, where a type is used. -/
inductive Plan.Ty where
  | same
  | list (item : Plan.Ty)
  | map (key value : Plan.Ty)
  /-- A value of the writer's named type `writer`, read as one of the reader's `reader`: through
  the plan of the pair, in the plan's table. -/
  | ref (writer reader : String)
  | convert (type : String) (run : Value → Option Value)

/-- How a value of the writer's named type becomes one of the reader's. A record's fields are
the reader's, in its order; a sum's constructors are the writer's, in its order. -/
inductive Plan.Decl where
  | record (type : String) (fields : List (Plan.Field Plan.Ty))
  | sum (type : String) (ctors : List (Plan.Ctor Plan.Ty))

/-- How a value of the writer's schema becomes one of the reader's: the plan of each pair of
named types that matching met, made once, and the plan of the root. -/
structure Plan where
  pairs : List ((String × String) × Plan.Decl)
  root : Plan.Ty

namespace Plan

/-- The plan of equal schemas: every value as it is. -/
def same : Plan := ⟨[], .same⟩

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
def pick : List (Option (Nat × Ctor Plan.Ty)) → Nat → String → Ctor Plan.Ty
  | [], _, name => .absent name
  | none :: found, k, name => pick found k name
  | some (k', c) :: found, k, name => if k' = k then c else pick found k name

/-- One pass of `alike`: the names whose declarations in `w` use only names among them. -/
def keep (w : List (String × Schema.Decl)) (names : List String) : List String :=
  names.filter fun n => match w.lookup n with
    | some d => d.refs.all names.contains
    | none => false

def prune (w : List (String × Schema.Decl)) : Nat → List String → List String
  | 0, names => names
  | k + 1, names =>
    if (keep w names).length = names.length then names else prune w k (keep w names)

/-- The names of the named types that are one type in `w` and in `r`: each declared the same in
both, using only names that are again one type. The largest such, found by dropping from the
names declared the same each one whose declaration uses a name dropped, until none is; so a type
that refers to itself is one type when its declarations are the same. -/
def alike (w r : List (String × Schema.Decl)) : List String :=
  let start := w.filterMap fun (n, _) =>
    match w.lookup n with
    | some d => if r.lookup n == some d then some n else none
    | none => none
  prune w (start.length + 1) start

/-- What matching has met: each pair of named types, the writer's and the reader's, with its
plan once it is made. A pair met again is not matched again. -/
abbrev Memo := List ((String × String) × Option Plan.Decl)

section

variable (ms : List Migration) (w r : Schema) (names : List String)

/-- Whether the writer's `wt` and the reader's `rt` are one type: the same, with each named type
in it among `names`, the names that are one type in both (`alike`). -/
def sameTy (wt rt : Schema.Ty) : Bool := wt == rt && wt.refs.all names.contains

/-- The declared migration from the writer's `wt` to the reader's `rt`: one whose old schema is
`wt`, its named types declared as the writer declares them, and whose new is `rt`, declared as
the reader declares them. -/
def migrationFor (wt rt : Schema.Ty) : Option Migration :=
  ms.find? fun m => m.old.root == wt && m.new.root == rt
    && m.old.types.all w.types.contains && m.new.types.all r.types.contains

mutual

/-- The plan from the writer's type `wt` to the reader's `rt`; refused, naming what changed, if
a value could not be read. A pair of named types is matched once, through `memo`, nested at most
`fuel` pairs deep. -/
def ofTy (fuel : Nat) (wt rt : Schema.Ty) (memo : Memo) : Except Error (Plan.Ty × Memo) :=
  if sameTy names wt rt then .ok (.same, memo) else
  match migrationFor ms w r wt rt with
  | some m => .ok (.convert rt.name m.run, memo)
  | none =>
    match wt, rt with
    | .list wi, .list ri =>
      match ofTy fuel wi ri memo with
      | .ok (p, memo) => .ok (.list p, memo)
      | .error e => .error e
    | .map wk wv, .map rk rv =>
      match within (.field "key") (ofTy fuel wk rk memo) with
      | .error e => .error e
      | .ok (pk, memo) =>
        match within (.field "value") (ofTy fuel wv rv memo) with
        | .ok (pv, memo) => .ok (.map pk pv, memo)
        | .error e => .error e
    | .ref a, .ref b => ofPair fuel a b memo
    | wt, rt => fail 0 (.changed wt.name rt.name)
termination_by (fuel, 1, sizeOf wt)

/-- The plan of the writer's named type `a` read as the reader's `b`, made the first time the
pair is met. -/
def ofPair (fuel : Nat) (a b : String) (memo : Memo) : Except Error (Plan.Ty × Memo) :=
  if (memo.lookup (a, b)).isSome then .ok (.ref a b, memo) else
  match fuel with
  | 0 => fail 0 .misfit
  | fuel + 1 =>
    let memo := ((a, b), none) :: memo
    match w.types.lookup a, r.types.lookup b with
    | some (.record _ wfs), some (.record type rfs) =>
      let names := wfs.map (·.name)
      match within (.type type) (unambiguous .field names
          (rfs.map fun f => (f.name, claim names f.name f.aliases))) with
      | .error e => .error e
      | .ok () =>
        match within (.type type) (ofFields fuel wfs rfs memo) with
        | .ok (ps, memo) => .ok (.ref a b, ((a, b), some (.record type ps)) :: memo)
        | .error e => .error e
    | some (.sum _ wcs), some (.sum type rcs) =>
      let names := wcs.map (·.name)
      match within (.type type) (unambiguous .ctor names
          (rcs.map fun c => (c.name, claim names c.name c.aliases))) with
      | .error e => .error e
      | .ok () =>
        match within (.type type) (ofCtors fuel wcs rcs 0 memo) with
        | .ok (found, memo) =>
          .ok (.ref a b, ((a, b), some (.sum type (wcs.mapIdx fun k c => pick found k c.name)))
            :: memo)
        | .error e => .error e
    | some _, some _ => fail 0 (.changed a b)
    | none, _ => fail 0 (.undeclared a)
    | _, none => fail 0 (.undeclared b)
termination_by (fuel, 0, 0)

/-- The plan of each of the reader's fields `rfs` from the writer's `wfs`. -/
def ofFields (fuel : Nat) (wfs : List (Schema.Field Schema.Ty))
    (rfs : List (Schema.Field Schema.Ty)) (memo : Memo) :
    Except Error (List (Plan.Field Plan.Ty) × Memo) :=
  match rfs with
  | [] => .ok ([], memo)
  | ⟨name, aliases, s, default⟩ :: rfs =>
    let head : Except Error (Plan.Field Plan.Ty × Memo) :=
      match claim (wfs.map (·.name)) name aliases with
      | some k =>
        match wfs[k]? with
        | some g =>
          match within (.field name) (ofTy fuel g.schema s memo) with
          | .ok (p, memo) => .ok (.take name k p, memo)
          | .error e => .error e
        | none => fail 0 .misfit
      | none =>
        match default with
        | some v => .ok (.fill v, memo)
        | none => within (.field name) (fail 0 .noDefault)
    match head with
    | .error e => .error e
    | .ok (p, memo) =>
      match ofFields fuel wfs rfs memo with
      | .ok (ps, memo) => .ok (p :: ps, memo)
      | .error e => .error e
termination_by (fuel, 2, rfs.length)

/-- For each of the reader's constructors `rcs`, from the `index`th: the writer's constructor
it takes, if any, and that constructor's plan. -/
def ofCtors (fuel : Nat) (wcs : List (Schema.Ctor Schema.Ty))
    (rcs : List (Schema.Ctor Schema.Ty)) (index : Nat) (memo : Memo) :
    Except Error (List (Option (Nat × Ctor Plan.Ty)) × Memo) :=
  match rcs with
  | [] => .ok ([], memo)
  | ⟨name, aliases, fields⟩ :: rcs =>
    let head : Except Error (Option (Nat × Ctor Plan.Ty) × Memo) :=
      match claim (wcs.map (·.name)) name aliases with
      | none => .ok (none, memo)
      | some k =>
        match wcs[k]? with
        | none => fail 0 .misfit
        | some c =>
          if c.fields == fields && fields.all (fun f => sameTy names f.schema f.schema) then
            .ok (some (k, .to name index none), memo)
          else
            match within (.ctor name) (ofFields fuel c.fields fields memo) with
            | .ok (ps, memo) => .ok (some (k, .to name index (some ps)), memo)
            | .error e => .error e
    match head with
    | .error e => .error e
    | .ok (x, memo) =>
      match ofCtors fuel wcs rcs (index + 1) memo with
      | .ok (xs, memo) => .ok (x :: xs, memo)
      | .error e => .error e
termination_by (fuel, 3, rcs.length)

end

end

/-- The plans made, from what matching met. -/
def made (memo : Memo) : List ((String × String) × Plan.Decl) :=
  memo.filterMap fun (pair, d) => d.map (pair, ·)

/-- The plan from `w`, the writer's schema, to `r`, the reader's; refused, naming what changed,
if a value could not be read. Each pair of named types is matched once, so a pair is nested in
no more pairs than there are. -/
def of (ms : List Migration) (w r : Schema) : Except Error Plan :=
  if w == r then .ok .same else
  match migrationFor ms w r w.root r.root with
  | some m => .ok ⟨[], .convert r.name m.run⟩
  | none =>
    match ofTy ms w r (alike w.types r.types) (w.types.length * r.types.length + 1) w.root r.root
        [] with
    | .ok (p, memo) => .ok ⟨made memo, p⟩
    | .error e => .error e

theorem sizeOf_lt_of_getElem? {vs : List Value} {k : Nat} {v : Value} (h : vs[k]? = some v) :
    sizeOf v < sizeOf vs :=
  List.sizeOf_lt_of_mem (List.mem_of_getElem? h)

section

variable (pairs : List ((String × String) × Plan.Decl))

mutual

/-- The reader's value of `v`, a value of the writer's type, with the plans of pairs `pairs`. -/
def applyTy (p : Plan.Ty) (v : Value) : Except Error Value :=
  match p, v with
  | .same, v => .ok v
  | .list item, .list vs =>
    match applyItems item vs 0 with
    | .ok us => .ok (.list us)
    | .error e => .error e
  | .map key value, .list es =>
    match applyEntries key value es 0 with
    | .ok us => .ok (.list us)
    | .error e => .error e
  | .ref a b, v =>
    match pairs.lookup (a, b) with
    | some d => applyDecl d v
    | none => fail 0 .misfit
  | .convert type run, v =>
    match run v with
    | some u => .ok u
    | none => within (.type type) (fail 0 .refused)
  | _, _ => fail 0 .misfit
termination_by (sizeOf v, 3, 0)

def applyDecl (d : Plan.Decl) (v : Value) : Except Error Value :=
  match d, v with
  | .record type fields, .ctor 0 vs =>
    match within (.type type) (applyFields fields vs) with
    | .ok us => .ok (.ctor 0 us)
    | .error e => .error e
  | .sum type ctors, .ctor k vs => within (.type type) (applyCtor ctors k vs)
  | _, _ => fail 0 .misfit
termination_by (sizeOf v, 2, 0)

def applyItems (item : Plan.Ty) (vs : List Value) (index : Nat) : Except Error (List Value) :=
  match vs with
  | [] => .ok []
  | v :: vs =>
    match within (.item index) (applyTy item v) with
    | .error e => .error e
    | .ok u =>
      match applyItems item vs (index + 1) with
      | .ok us => .ok (u :: us)
      | .error e => .error e
termination_by (sizeOf vs, 0, 0)

def applyEntries (key value : Plan.Ty) (es : List Value) (index : Nat) :
    Except Error (List Value) :=
  match es with
  | [] => .ok []
  | .ctor 0 [k, v] :: es =>
    match within (.item index) (within (.field "key") (applyTy key k)) with
    | .error e => .error e
    | .ok k =>
      match within (.item index) (within (.field "value") (applyTy value v)) with
      | .error e => .error e
      | .ok v =>
        match applyEntries key value es (index + 1) with
        | .ok us => .ok (.ctor 0 [k, v] :: us)
        | .error e => .error e
  | _ :: _ => within (.item index) (fail 0 .misfit)
termination_by (sizeOf es, 0, 0)

def applyFields (fields : List (Plan.Field Plan.Ty)) (vs : List Value) :
    Except Error (List Value) :=
  match fields with
  | [] => .ok []
  | .take name k p :: fields =>
    match h : vs[k]? with
    | none => fail 0 .misfit
    | some v =>
      have := sizeOf_lt_of_getElem? h
      match within (.field name) (applyTy p v) with
      | .error e => .error e
      | .ok u =>
        match applyFields fields vs with
        | .ok us => .ok (u :: us)
        | .error e => .error e
  | .fill u :: fields =>
    match applyFields fields vs with
    | .ok us => .ok (u :: us)
    | .error e => .error e
termination_by (sizeOf vs, 0, fields.length)

def applyCtor (ctors : List (Plan.Ctor Plan.Ty)) (k : Nat) (vs : List Value) :
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
termination_by (sizeOf vs, 1, ctors.length)

end

end

/-- The reader's value of `v`, a value of the writer's schema. -/
def apply (p : Plan) (v : Value) : Except Error Value := applyTy p.pairs p.root v

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
      match s.schema.type? with
      | some type => within (.type type) (fail 0 .refused)
      | none => fail 0 .refused

end Body

end Lanes
