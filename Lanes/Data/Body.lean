/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std
public import Lanes.Data.Codec

/-!
The body: the bytes of a `Value`, written and read with its `Schema`, which holds every name, so
the bytes hold none. A constructor is its index in the schema and fields come in the schema's
order. A number is LEB128 and an integer the number of its zigzag (`0, -1, 1, -2, …` are
`0, 1, 2, 3, …`); a string or bytes is its length and then the bytes; a list or a map is its count
and then its items. The second part of a `dependent` pair has no schema here, so it is written
with a tag before each of its values.

A value has one encoding: a number with a needless last byte is refused, so equal values are
equal bytes. A reader takes `Codec.Limits` and refuses past each, naming it, since the bytes may
come from a damaged file or a peer. A count or a length is checked against the bytes left, and a
count against `maxItems` as well, which bounds a list of a type written as no bytes.
The writer refuses what the reader with the same limits would refuse, so whatever is written
reads back (`Body.read_write`).
-/

@[expose] public section

namespace Lanes

namespace Codec

/-- The bounds of a reader, and of the writer that writes for it. -/
structure Limits where
  /-- The longest body, in bytes. -/
  maxBytes : Nat := 16777216
  /-- The most items of a list or entries of a map. -/
  maxItems : Nat := 1048576
  /-- The longest string or bytes, in bytes. -/
  maxLength : Nat := 16777216
  /-- The deepest nesting of lists, maps, records, sums and pairs. -/
  maxDepth : Nat := 64
  /-- The most bytes of one number: LEB128 of `maxNumberBytes` bytes holds `7 * maxNumberBytes`
  bits, and reading a longer number costs time quadratic in its length. -/
  maxNumberBytes : Nat := 32
  deriving Repr, DecidableEq, Inhabited

/-- Where in a value an error is: a type, a constructor or a field by name, an item by its place. -/
inductive Error.Step where
  | type (name : String)
  | ctor (name : String)
  | field (name : String)
  | item (index : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- What is wrong where an error is. -/
inductive Error.Problem where
  /-- The bytes end inside a value. -/
  | ended
  /-- A number written longer than it is: its last byte is zero. -/
  | padded
  /-- Past the limit of that name. -/
  | limit (name : String) (bound : Nat)
  /-- A count or a length larger than the bytes left. -/
  | overrun (count left : Nat)
  /-- A constructor's index past the schema's constructors. -/
  | index (found count : Nat)
  /-- A string whose bytes are not UTF-8. -/
  | utf8
  /-- A tag of a value written with tags that is none of them. -/
  | tag (found : Nat)
  /-- Bytes after the value. -/
  | trailing (count : Nat)
  /-- The writer was given a value that does not fit the schema. -/
  | misfit
  /-- A value that fits the schema but that its type does not take, such as `5` for a `Fin 3`. -/
  | refused
  /-- A reader's field that the data does not have, with no default. -/
  | noDefault
  /-- A type that is not the one the data has: the data's, then the reader's. -/
  | changed (data reader : String)
  /-- A reader's field or constructor that takes, by a former name, one of the data's that
  another takes too. -/
  | ambiguous (data : String)
  /-- A constructor of the data that the reader's type does not have. -/
  | absent
  /-- A named type that the schema uses and does not declare. -/
  | undeclared (name : String)
  deriving Repr, DecidableEq, Inhabited

/-- An error of the body: the byte where it is, the path to it, outermost first, and what. -/
structure Error where
  offset : Nat
  path : List Error.Step := []
  problem : Error.Problem
  deriving Repr, DecidableEq, Inhabited

namespace Error

def Step.text : Step → String
  | .type name => name
  | .ctor name | .field name => "." ++ name
  | .item index => "[" ++ toString index ++ "]"

def Problem.text : Problem → String
  | .ended => "the bytes end inside a value"
  | .padded => "a number has a needless last byte"
  | .limit name bound => s!"past the limit {name} of {bound}"
  | .overrun count left => s!"a count of {count} with {left} bytes left"
  | .index found count => s!"constructor {found} of a type of {count}"
  | .utf8 => "a string that is not UTF-8"
  | .tag found => s!"tag {found}, which no value has"
  | .trailing count => s!"{count} bytes after the value"
  | .misfit => "a value that does not fit its schema"
  | .refused => "a value its type does not take"
  | .noDefault => "a field the data does not have, with no default"
  | .changed data reader => s!"the data's type is {data}, the reader's {reader}"
  | .ambiguous data => s!"takes the data's {data}, which another takes too"
  | .absent => "a constructor of the data that the reader's type does not have"
  | .undeclared name => s!"the type {name}, which the schema does not declare"

/-- Whether the problem is at a byte. One found by matching the writer's schema with the
reader's is not. -/
def Problem.atByte : Problem → Bool
  | .noDefault | .changed _ _ | .ambiguous _ | .absent | .undeclared _ => false
  | _ => true

/-- The path as text: `Shape.circle.centre / Point.x`, a type inside another after a slash. -/
def pathText (path : List Step) : String :=
  path.foldl (fun text step => match step with
    | .type name => if text.isEmpty then name else text ++ " / " ++ name
    | step => text ++ step.text) ""

instance : ToString Error where
  toString e :=
    let place := (if e.problem.atByte then [s!"byte {e.offset}"] else [])
      ++ (if e.path.isEmpty then [] else [pathText e.path])
    if place.isEmpty then e.problem.text else ", ".intercalate place ++ ": " ++ e.problem.text

end Error

end Codec

namespace Body

open Codec (Limits Error)

variable {α : Type}

/-- An error found at `offset`. -/
def fail (offset : Nat) (problem : Error.Problem) : Except Error α :=
  .error { offset, problem }

/-- An error inside `step`. -/
def within (step : Error.Step) : Except Error α → Except Error α
  | .ok a => .ok a
  | .error e => .error { e with path := step :: e.path }

@[simp] theorem within_ok (step : Error.Step) (a : α) : within step (.ok a) = .ok a := rfl

/-! Numbers. -/

/-- LEB128: seven bits a byte, the lowest first, the high bit set on every byte but the last. -/
def writeNat (acc : ByteArray) (n : Nat) : ByteArray :=
  if n < 128 then acc.push n.toUInt8 else writeNat (acc.push (n % 128 + 128).toUInt8) (n / 128)
termination_by n
decreasing_by omega

/-- How many bytes `writeNat` writes. -/
def natBytes (n : Nat) : Nat :=
  if n < 128 then 1 else natBytes (n / 128) + 1
termination_by n
decreasing_by omega

def zigzag (i : Int) : Nat :=
  if i < 0 then 2 * i.natAbs - 1 else 2 * i.natAbs

def unzigzag (n : Nat) : Int :=
  if n % 2 = 0 then ((n / 2 : Nat) : Int) else -(((n + 1) / 2 : Nat) : Int)

/-- A number, refused if it takes more than `maxNumberBytes`. -/
def writeNum (limits : Limits) (acc : ByteArray) (n : Nat) : Except Error ByteArray :=
  if natBytes n ≤ limits.maxNumberBytes then .ok (writeNat acc n)
  else fail acc.size (.limit "maxNumberBytes" limits.maxNumberBytes)

/-- A string's or a byte array's bytes, after their length. -/
def writeBlob (limits : Limits) (acc blob : ByteArray) : Except Error ByteArray :=
  if blob.size ≤ limits.maxLength then (writeNum limits acc blob.size).map (· ++ blob)
  else fail acc.size (.limit "maxLength" limits.maxLength)

/-- A count of items, refused past `maxItems`. -/
def writeCount (limits : Limits) (acc : ByteArray) (n : Nat) : Except Error ByteArray :=
  if n ≤ limits.maxItems then writeNum limits acc n
  else fail acc.size (.limit "maxItems" limits.maxItems)

/-- The rest of a number in LEB128 from `pos`, of at most `budget` bytes; `first` when no byte
of it is read yet. Errors are at `start`, where the number begins. -/
def readNatFrom (bytes : ByteArray) (start bound : Nat) :
    (budget pos : Nat) → (first : Bool) → Except Error (Nat × Nat)
  | 0, _, _ => fail start (.limit "maxNumberBytes" bound)
  | budget + 1, pos, first =>
    match bytes[pos]? with
    | none => fail pos .ended
    | some b =>
      if b < 128 then
        if b = 0 ∧ first = false then fail start .padded else .ok (b.toNat, pos + 1)
      else
        match readNatFrom bytes start bound budget (pos + 1) false with
        | .ok (m, stop) => .ok (b.toNat - 128 + 128 * m, stop)
        | .error e => .error e

def readNat (limits : Limits) (bytes : ByteArray) (pos : Nat) : Except Error (Nat × Nat) :=
  readNatFrom bytes pos limits.maxNumberBytes limits.maxNumberBytes pos true

def readBlob (limits : Limits) (bytes : ByteArray) (pos : Nat) :
    Except Error (ByteArray × Nat) :=
  match readNat limits bytes pos with
  | .error e => .error e
  | .ok (n, start) =>
    if limits.maxLength < n then fail pos (.limit "maxLength" limits.maxLength)
    else if bytes.size - start < n then fail start (.overrun n (bytes.size - start))
    else .ok (bytes.extract start (start + n), start + n)

/-- A count of items, each written as at least one byte when `consumes`. -/
def readCount (limits : Limits) (bytes : ByteArray) (consumes : Bool) (pos : Nat) :
    Except Error (Nat × Nat) :=
  match readNat limits bytes pos with
  | .error e => .error e
  | .ok (n, start) =>
    if limits.maxItems < n then fail pos (.limit "maxItems" limits.maxItems)
    else if consumes ∧ bytes.size - start < n then fail start (.overrun n (bytes.size - start))
    else .ok (n, start)

/-! Values. -/

section

variable (types : List (String × Schema.Decl))

/-- Whether every value of the type is written as at least one byte, at most `depth` deep: past
it, `false`, which is always safe. -/
def consumes : Nat → Schema.Ty → Bool
  | _, .unit => false
  | 0, .ref _ => false
  | d + 1, .ref name =>
    match types.lookup name with
    | some (.record _ fields) => fields.any fun f => consumes d f.schema
    | some (.sum _ _) => true
    | none => false
  | _, _ => true

def consumesFields (depth : Nat) (fields : List (Schema.Field Schema.Ty)) : Bool :=
  fields.any fun f => consumes types depth f.schema

end

/-- The tags of a value written with tags, which is the second part of a `dependent` pair. -/
def Tag.nat : UInt8 := 0
def Tag.int : UInt8 := 1
def Tag.string : UInt8 := 2
def Tag.bytes : UInt8 := 3
def Tag.list : UInt8 := 4
def Tag.ctor : UInt8 := 5

section

variable (limits : Limits) (types : List (String × Schema.Decl))

mutual

/-- `v` of type `s` after `acc`, nested at most `depth` more, with the named types `types`. -/
def writeAt (depth : Nat) (s : Schema.Ty) (v : Value) (acc : ByteArray) :
    Except Error ByteArray :=
  match depth, s, v with
  | _, .nat, .nat n => writeNum limits acc n
  | _, .int, .int i => writeNum limits acc (zigzag i)
  | _, .string, .string t => writeBlob limits acc t.toUTF8
  | _, .bytes, .bytes b => writeBlob limits acc b
  | _, .unit, .ctor 0 [] => .ok acc
  | 0, .list _, _ | 0, .map _ _, _ | 0, .ref _, _ | 0, .dependent _, _ =>
    fail acc.size (.limit "maxDepth" limits.maxDepth)
  | d + 1, .list item, .list vs =>
    match writeCount limits acc vs.length with
    | .ok acc => writeItems d item vs 0 acc
    | .error e => .error e
  | d + 1, .map key value, .list es =>
    match writeCount limits acc es.length with
    | .ok acc => writeEntries d key value es 0 acc
    | .error e => .error e
  | d + 1, .ref name, .ctor k vs =>
    match types.lookup name with
    | none => fail acc.size (.undeclared name)
    | some (.record type fields) =>
      if k = 0 then within (.type type) (writeFields d fields vs acc) else fail acc.size .misfit
    | some (.sum type ctors) =>
      match ctors[k]? with
      | none => fail acc.size .misfit
      | some c =>
        match writeNum limits acc k with
        | .ok acc => within (.type type) (within (.ctor c.name) (writeFields d c.fields vs acc))
        | .error e => .error e
  | d + 1, .dependent index, .ctor 0 [i, x] =>
    match within (.item 0) (writeAt d index i acc) with
    | .ok acc => within (.item 1) (writeTagged d x acc)
    | .error e => .error e
  | _, _, _ => fail acc.size .misfit
termination_by (depth, 0, 0)

def writeFields (depth : Nat) (fields : List (Schema.Field Schema.Ty)) (vs : List Value)
    (acc : ByteArray) : Except Error ByteArray :=
  match fields, vs with
  | [], [] => .ok acc
  | f :: fs, v :: vs =>
    match within (.field f.name) (writeAt depth f.schema v acc) with
    | .ok acc => writeFields depth fs vs acc
    | .error e => .error e
  | _, _ => fail acc.size .misfit
termination_by (depth, 1, vs.length)

def writeItems (depth : Nat) (item : Schema.Ty) (vs : List Value) (index : Nat)
    (acc : ByteArray) : Except Error ByteArray :=
  match vs with
  | [] => .ok acc
  | v :: vs =>
    match within (.item index) (writeAt depth item v acc) with
    | .ok acc => writeItems depth item vs (index + 1) acc
    | .error e => .error e
termination_by (depth, 1, vs.length)

/-- The entries of a map, each a key and a value: `.ctor 0 [k, v]`. -/
def writeEntries (depth : Nat) (key value : Schema.Ty) (es : List Value) (index : Nat)
    (acc : ByteArray) : Except Error ByteArray :=
  match es with
  | [] => .ok acc
  | .ctor 0 [k, v] :: es =>
    match within (.item index) (within (.field "key") (writeAt depth key k acc)) with
    | .error e => .error e
    | .ok acc =>
      match within (.item index) (within (.field "value") (writeAt depth value v acc)) with
      | .ok acc => writeEntries depth key value es (index + 1) acc
      | .error e => .error e
  | _ :: _ => within (.item index) (fail acc.size .misfit)
termination_by (depth, 1, es.length)

/-- A value with a tag before it and before each value inside it. -/
def writeTagged (depth : Nat) (v : Value) (acc : ByteArray) : Except Error ByteArray :=
  match depth, v with
  | _, .nat n => writeNum limits (acc.push Tag.nat) n
  | _, .int i => writeNum limits (acc.push Tag.int) (zigzag i)
  | _, .string t => writeBlob limits (acc.push Tag.string) t.toUTF8
  | _, .bytes b => writeBlob limits (acc.push Tag.bytes) b
  | 0, .list _ | 0, .ctor _ _ => fail acc.size (.limit "maxDepth" limits.maxDepth)
  | d + 1, .list vs =>
    match writeCount limits (acc.push Tag.list) vs.length with
    | .ok acc => writeTaggedItems d vs 0 acc
    | .error e => .error e
  | d + 1, .ctor k vs =>
    match writeNum limits (acc.push Tag.ctor) k with
    | .error e => .error e
    | .ok acc =>
      match writeCount limits acc vs.length with
      | .ok acc => writeTaggedItems d vs 0 acc
      | .error e => .error e
termination_by (depth, 0, 0)

def writeTaggedItems (depth : Nat) (vs : List Value) (index : Nat) (acc : ByteArray) :
    Except Error ByteArray :=
  match vs with
  | [] => .ok acc
  | v :: vs =>
    match within (.item index) (writeTagged depth v acc) with
    | .ok acc => writeTaggedItems depth vs (index + 1) acc
    | .error e => .error e
termination_by (depth, 1, vs.length)

end

variable (bytes : ByteArray)

mutual

/-- The value of type `s` at `pos`, nested at most `depth` more, and where it ends. -/
def readAt (depth : Nat) (s : Schema.Ty) (pos : Nat) : Except Error (Value × Nat) :=
  match depth, s with
  | _, .nat =>
    match readNat limits bytes pos with
    | .ok (n, stop) => .ok (.nat n, stop)
    | .error e => .error e
  | _, .int =>
    match readNat limits bytes pos with
    | .ok (n, stop) => .ok (.int (unzigzag n), stop)
    | .error e => .error e
  | _, .string =>
    match readBlob limits bytes pos with
    | .ok (b, stop) =>
      match String.fromUTF8? b with
      | some t => .ok (.string t, stop)
      | none => fail pos .utf8
    | .error e => .error e
  | _, .bytes =>
    match readBlob limits bytes pos with
    | .ok (b, stop) => .ok (.bytes b, stop)
    | .error e => .error e
  | _, .unit => .ok (.ctor 0 [], pos)
  | 0, .list _ | 0, .map _ _ | 0, .ref _ | 0, .dependent _ =>
    fail pos (.limit "maxDepth" limits.maxDepth)
  | d + 1, .list item =>
    match readCount limits bytes (consumes types d item) pos with
    | .ok (n, pos) =>
      match readItems d item n 0 pos with
      | .ok (vs, stop) => .ok (.list vs, stop)
      | .error e => .error e
    | .error e => .error e
  | d + 1, .map key value =>
    match readCount limits bytes (consumes types d key || consumes types d value) pos with
    | .ok (n, pos) =>
      match readEntries d key value n 0 pos with
      | .ok (es, stop) => .ok (.list es, stop)
      | .error e => .error e
    | .error e => .error e
  | d + 1, .ref name =>
    match types.lookup name with
    | none => fail pos (.undeclared name)
    | some (.record type fields) =>
      match within (.type type) (readFields d fields pos) with
      | .ok (vs, stop) => .ok (.ctor 0 vs, stop)
      | .error e => .error e
    | some (.sum type ctors) =>
      match readNat limits bytes pos with
      | .error e => .error e
      | .ok (k, start) =>
        match ctors[k]? with
        | none => within (.type type) (fail pos (.index k ctors.length))
        | some c =>
          match within (.type type) (within (.ctor c.name) (readFields d c.fields start)) with
          | .ok (vs, stop) => .ok (.ctor k vs, stop)
          | .error e => .error e
  | d + 1, .dependent index =>
    match within (.item 0) (readAt d index pos) with
    | .error e => .error e
    | .ok (i, pos) =>
      match within (.item 1) (readTagged d pos) with
      | .ok (x, stop) => .ok (.ctor 0 [i, x], stop)
      | .error e => .error e
termination_by (depth, 0, 0)

def readFields (depth : Nat) (fields : List (Schema.Field Schema.Ty)) (pos : Nat) :
    Except Error (List Value × Nat) :=
  match fields with
  | [] => .ok ([], pos)
  | f :: fs =>
    match within (.field f.name) (readAt depth f.schema pos) with
    | .error e => .error e
    | .ok (v, pos) =>
      match readFields depth fs pos with
      | .ok (vs, stop) => .ok (v :: vs, stop)
      | .error e => .error e
termination_by (depth, 1, fields.length)

def readItems (depth : Nat) (item : Schema.Ty) (n index pos : Nat) :
    Except Error (List Value × Nat) :=
  match n with
  | 0 => .ok ([], pos)
  | n + 1 =>
    match within (.item index) (readAt depth item pos) with
    | .error e => .error e
    | .ok (v, pos) =>
      match readItems depth item n (index + 1) pos with
      | .ok (vs, stop) => .ok (v :: vs, stop)
      | .error e => .error e
termination_by (depth, 1, n)

def readEntries (depth : Nat) (key value : Schema.Ty) (n index pos : Nat) :
    Except Error (List Value × Nat) :=
  match n with
  | 0 => .ok ([], pos)
  | n + 1 =>
    match within (.item index) (within (.field "key") (readAt depth key pos)) with
    | .error e => .error e
    | .ok (k, pos) =>
      match within (.item index) (within (.field "value") (readAt depth value pos)) with
      | .error e => .error e
      | .ok (v, pos) =>
        match readEntries depth key value n (index + 1) pos with
        | .ok (es, stop) => .ok (.ctor 0 [k, v] :: es, stop)
        | .error e => .error e
termination_by (depth, 1, n)

def readTagged (depth : Nat) (pos : Nat) : Except Error (Value × Nat) :=
  match bytes[pos]? with
  | none => fail pos .ended
  | some tag =>
    if tag = Tag.nat then
      match readNat limits bytes (pos + 1) with
      | .ok (n, stop) => .ok (.nat n, stop)
      | .error e => .error e
    else if tag = Tag.int then
      match readNat limits bytes (pos + 1) with
      | .ok (n, stop) => .ok (.int (unzigzag n), stop)
      | .error e => .error e
    else if tag = Tag.string then
      match readBlob limits bytes (pos + 1) with
      | .ok (b, stop) =>
        match String.fromUTF8? b with
        | some t => .ok (.string t, stop)
        | none => fail pos .utf8
      | .error e => .error e
    else if tag = Tag.bytes then
      match readBlob limits bytes (pos + 1) with
      | .ok (b, stop) => .ok (.bytes b, stop)
      | .error e => .error e
    else if tag = Tag.list ∨ tag = Tag.ctor then
      match depth with
      | 0 => fail pos (.limit "maxDepth" limits.maxDepth)
      | d + 1 =>
        if tag = Tag.list then
          match readCount limits bytes true (pos + 1) with
          | .error e => .error e
          | .ok (n, pos) =>
            match readTaggedItems d n 0 pos with
            | .ok (vs, stop) => .ok (.list vs, stop)
            | .error e => .error e
        else
          match readNat limits bytes (pos + 1) with
          | .error e => .error e
          | .ok (k, pos) =>
            match readCount limits bytes true pos with
            | .error e => .error e
            | .ok (n, pos) =>
              match readTaggedItems d n 0 pos with
              | .ok (vs, stop) => .ok (.ctor k vs, stop)
              | .error e => .error e
    else fail pos (.tag tag.toNat)
termination_by (depth, 0, 0)

def readTaggedItems (depth : Nat) (n index pos : Nat) : Except Error (List Value × Nat) :=
  match n with
  | 0 => .ok ([], pos)
  | n + 1 =>
    match within (.item index) (readTagged depth pos) with
    | .error e => .error e
    | .ok (v, pos) =>
      match readTaggedItems depth n (index + 1) pos with
      | .ok (vs, stop) => .ok (v :: vs, stop)
      | .error e => .error e
termination_by (depth, 1, n)

end

end

/-- The bytes of `v`, a value of `s`; refused where the reader with the same limits would refuse
them. -/
def write (limits : Limits) (s : Schema) (v : Value) : Except Error ByteArray :=
  match writeAt limits s.types limits.maxDepth s.root v .empty with
  | .ok bytes =>
    if bytes.size ≤ limits.maxBytes then .ok bytes
    else fail 0 (.limit "maxBytes" limits.maxBytes)
  | .error e => .error e

/-- The value of `s` that is all of `bytes`. -/
def read (limits : Limits) (s : Schema) (bytes : ByteArray) : Except Error Value :=
  if limits.maxBytes < bytes.size then fail 0 (.limit "maxBytes" limits.maxBytes)
  else
    match readAt limits s.types bytes limits.maxDepth s.root 0 with
    | .ok (v, stop) => if stop = bytes.size then .ok v else fail stop (.trailing (bytes.size - stop))
    | .error e => .error e

/-- A value with no schema: every value inside it is written with a tag, so the bytes carry its
shape. It is the second part of a `dependent` pair whose first is `()`. -/
def writeAny (limits : Limits) (v : Value) : Except Error ByteArray :=
  write limits ⟨[], .dependent .unit⟩ (.ctor 0 [.ctor 0 [], v])

def readAny (limits : Limits) (bytes : ByteArray) : Except Error Value :=
  match read limits ⟨[], .dependent .unit⟩ bytes with
  | .ok (.ctor 0 [_, v]) => .ok v
  | .ok _ => fail 0 .misfit
  | .error e => .error e

variable {α : Type}

/-- The bytes of `a`, written with its type's schema. -/
def encode (limits : Limits) (s : Schema.Of α) (a : α) : Except Error ByteArray :=
  write limits s.schema (s.toValue a)

/-- The `α` that is all of `bytes`, read with its type's schema. A value that reads but that the
type does not take is refused at the value's first byte, `0`, under the type's name when it has
one. -/
def decode (limits : Limits) (s : Schema.Of α) (bytes : ByteArray) : Except Error α :=
  match read limits s.schema bytes with
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
