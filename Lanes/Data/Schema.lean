/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std

/-!
A `Schema` says what a type is, as data: its primitives, and its records and sums with the names
of their fields and constructors, the defaults of its fields and their former names. A `Value` is
a value of any schema: a number, a string, bytes, a list, or a constructor's index and its
fields. `Schema.Of α` ties a schema to a type, with a map each way between `α` and `Value` and
the law that a value read back from its `Value` is itself.

A value carries no names. A constructor is its index in its schema, and fields come in the
schema's order, so that the names are written once, in the schema, and a reader matches them.
-/

@[expose] public section

namespace Lanes

/-- A value of any schema. A record is constructor `0` with its fields. -/
inductive Value where
  | nat (n : Nat)
  | int (i : Int)
  | string (s : String)
  | bytes (b : ByteArray)
  | list (items : List Value)
  | ctor (index : Nat) (fields : List Value)
  deriving Inhabited, BEq

/-- A field of a record or of a constructor. `σ` is `Schema`, given as a parameter so that
`Schema` can hold fields. -/
structure Schema.Field (σ : Type) where
  name : String
  /-- The field's former names. -/
  aliases : List String := []
  schema : σ
  /-- What a reader takes when the data has no such field. -/
  default : Option Value := none
  deriving BEq

structure Schema.Ctor (σ : Type) where
  name : String
  /-- The constructor's former names. -/
  aliases : List String := []
  fields : List (Schema.Field σ)
  deriving BEq

inductive Schema where
  | nat
  | int
  | string
  | bytes
  | unit
  | list (item : Schema)
  /-- A map, whose value is the list of its entries, each a `Prod` of a key and a value. -/
  | map (key value : Schema)
  /-- `type` is the Lean type's name and `args` the schemas of its type parameters. -/
  | record (type : String) (args : List Schema) (fields : List (Schema.Field Schema))
  | sum (type : String) (args : List Schema) (ctors : List (Schema.Ctor Schema))
  /-- A pair whose second part's schema depends on the value of the first (`Codec.sigma`), so
  only the first part's schema is known here. -/
  | dependent (index : Schema)
  deriving BEq, Inhabited

/-- A type's schema, with a map each way between its values and `Value`, and the law that ties
them. -/
structure Schema.Of (α : Type) where
  schema : Schema
  toValue : α → Value
  ofValue : Value → Option α
  ofValue_toValue : ∀ a, ofValue (toValue a) = some a

/-- The fields of a record or of a constructor, over nested pairs that end in `Unit`. -/
structure Schema.Fields (α : Type) where
  schemas : List (Schema.Field Schema)
  toValues : α → List Value
  ofValues : List Value → Option α
  ofValues_toValues : ∀ a, ofValues (toValues a) = some a

/-- The constructors of a sum, over nested sums that end in `Empty`: a value is its
constructor's index and its fields. -/
structure Schema.Ctors (α : Type) where
  schemas : List (Schema.Ctor Schema)
  toValue : α → Nat × List Value
  ofValue : Nat → List Value → Option α
  ofValue_toValue : ∀ a, ofValue (toValue a).1 (toValue a).2 = some a

namespace Schema

variable {α β : Type}

namespace Fields

def nil : Fields Unit where
  schemas := []
  toValues _ := []
  ofValues
    | [] => some ()
    | _ :: _ => none
  ofValues_toValues _ := rfl

def cons (name : String) (aliases : List String) (s : Of α) (default : Option α)
    (rest : Fields β) : Fields (α × β) where
  schemas := { name, aliases, schema := s.schema, default := default.map s.toValue }
    :: rest.schemas
  toValues x := s.toValue x.1 :: rest.toValues x.2
  ofValues
    | v :: vs => do
      let a ← s.ofValue v
      let b ← rest.ofValues vs
      return (a, b)
    | [] => none
  ofValues_toValues x := by simp [s.ofValue_toValue, rest.ofValues_toValues]

end Fields

namespace Ctors

def nil : Ctors Empty where
  schemas := []
  toValue e := nomatch e
  ofValue _ _ := none
  ofValue_toValue e := nomatch e

def cons (name : String) (aliases : List String) (fields : Fields α) (rest : Ctors β) :
    Ctors (α ⊕ β) where
  schemas := { name, aliases, fields := fields.schemas } :: rest.schemas
  toValue
    | .inl a => (0, fields.toValues a)
    | .inr b => ((rest.toValue b).1 + 1, (rest.toValue b).2)
  ofValue
    | 0, vs => (fields.ofValues vs).map .inl
    | k + 1, vs => (rest.ofValue k vs).map .inr
  ofValue_toValue x := by
    cases x <;> simp [fields.ofValues_toValues, rest.ofValue_toValue]

end Ctors

namespace Of

def nat : Of Nat where
  schema := .nat
  toValue := .nat
  ofValue
    | .nat n => some n
    | _ => none
  ofValue_toValue _ := rfl

def int : Of Int where
  schema := .int
  toValue := .int
  ofValue
    | .int i => some i
    | _ => none
  ofValue_toValue _ := rfl

def string : Of String where
  schema := .string
  toValue := .string
  ofValue
    | .string s => some s
    | _ => none
  ofValue_toValue _ := rfl

def bytes : Of ByteArray where
  schema := .bytes
  toValue := .bytes
  ofValue
    | .bytes b => some b
    | _ => none
  ofValue_toValue _ := rfl

def unit : Of Unit where
  schema := .unit
  toValue _ := .ctor 0 []
  ofValue
    | .ctor 0 [] => some ()
    | _ => none
  ofValue_toValue _ := rfl

/-- A type described as another. `back` may refuse what `to` never produces. -/
def map (s : Of β) (to : α → β) (back : β → Option α) (h : ∀ a, back (to a) = some a) :
    Of α where
  schema := s.schema
  toValue a := s.toValue (to a)
  ofValue v := (s.ofValue v).bind back
  ofValue_toValue a := by simp [s.ofValue_toValue, h]

def record (type : String) (args : List Schema) (fields : Fields α) : Of α where
  schema := .record type args fields.schemas
  toValue a := .ctor 0 (fields.toValues a)
  ofValue
    | .ctor 0 vs => fields.ofValues vs
    | _ => none
  ofValue_toValue a := fields.ofValues_toValues a

def variants (type : String) (args : List Schema) (ctors : Ctors α) : Of α where
  schema := .sum type args ctors.schemas
  toValue a := .ctor (ctors.toValue a).1 (ctors.toValue a).2
  ofValue
    | .ctor k vs => ctors.ofValue k vs
    | _ => none
  ofValue_toValue a := ctors.ofValue_toValue a

theorem mapM_map (s : Of α) (as : List α) : (as.map s.toValue).mapM s.ofValue = some as := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [s.ofValue_toValue, ih]

def list (s : Of α) : Of (List α) where
  schema := .list s.schema
  toValue as := .list (as.map s.toValue)
  ofValue
    | .list vs => vs.mapM s.ofValue
    | _ => none
  ofValue_toValue as := mapM_map s as

def bool : Of Bool :=
  (variants "Bool" [] (.cons "false" [] .nil (.cons "true" [] .nil .nil))).map
    (fun | false => .inl () | true => .inr (.inl ()))
    (fun | .inl () => some false | .inr (.inl ()) => some true | .inr (.inr e) => nomatch e)
    (by intro b; cases b <;> rfl)

def pair (a : Of α) (b : Of β) : Of (α × β) :=
  (record "Prod" [a.schema, b.schema] (.cons "fst" [] a none (.cons "snd" [] b none .nil))).map
    (fun (x, y) => (x, y, ())) (fun (x, y, ()) => some (x, y)) (fun _ => rfl)

def sum (a : Of α) (b : Of β) : Of (α ⊕ β) :=
  (variants "Sum" [a.schema, b.schema]
      (.cons "inl" [] (.cons "val" [] a none .nil) (.cons "inr" [] (.cons "val" [] b none .nil)
        .nil))).map
    (fun | .inl x => .inl (x, ()) | .inr y => .inr (.inl (y, ())))
    (fun | .inl (x, ()) => some (.inl x) | .inr (.inl (y, ())) => some (.inr y)
         | .inr (.inr e) => nomatch e)
    (by intro x; cases x <;> rfl)

def option (s : Of α) : Of (Option α) :=
  (variants "Option" [s.schema] (.cons "none" [] .nil (.cons "some" [] (.cons "val" [] s none .nil)
      .nil))).map
    (fun | none => .inl () | some a => .inr (.inl (a, ())))
    (fun | .inl () => some none | .inr (.inl (a, ())) => some (some a) | .inr (.inr e) => nomatch e)
    (by intro x; cases x <;> rfl)

def sigma {ι : Type} {β : ι → Type} (a : Of ι) (b : ∀ i, Of (β i)) : Of ((i : ι) × β i) where
  schema := .dependent a.schema
  toValue x := .ctor 0 [a.toValue x.1, (b x.1).toValue x.2]
  ofValue
    | .ctor 0 [vi, vb] => do
      let i ← a.ofValue vi
      let v ← (b i).ofValue vb
      return ⟨i, v⟩
    | _ => none
  ofValue_toValue x := by simp [a.ofValue_toValue, (b x.1).ofValue_toValue]

end Of


/-! The text of a schema: the type it describes, then a declaration of each named type in it,
written as `lanes_data` writes it. -/

/-- In parentheses unless it is one word. -/
def paren (text : String) : String :=
  if text.contains ' ' then "(" ++ text ++ ")" else text

mutual

/-- The type a schema describes, as Lean writes it. -/
def name : Schema → String
  | .nat => "Nat"
  | .int => "Int"
  | .string => "String"
  | .bytes => "ByteArray"
  | .unit => "Unit"
  | .list item => "List " ++ paren item.name
  | .map key value => "Map " ++ paren key.name ++ " " ++ paren value.name
  | .record type args _ | .sum type args _ => " ".intercalate (type :: names args)
  | .dependent index => "Σ " ++ paren index.name

def names : List Schema → List String
  | [] => []
  | s :: ss => paren s.name :: names ss

end

mutual

/-- Each named type in a schema, the outermost first, with repeats. -/
def named : Schema → List Schema
  | .list item => item.named
  | .map key value => key.named ++ value.named
  | s@(.record _ args fields) => s :: (namedAll args ++ namedFields fields)
  | s@(.sum _ args ctors) => s :: (namedAll args ++ namedCtors ctors)
  | .dependent index => index.named
  | .nat | .int | .string | .bytes | .unit => []

def namedAll : List Schema → List Schema
  | [] => []
  | s :: ss => s.named ++ namedAll ss

def namedFields : List (Field Schema) → List Schema
  | [] => []
  | ⟨_, _, s, _⟩ :: fs => s.named ++ namedFields fs

def namedCtors : List (Ctor Schema) → List Schema
  | [] => []
  | ⟨_, _, fields⟩ :: cs => namedFields fields ++ namedCtors cs

end

/-- A value as an argument: in parentheses if it is a constructor with arguments or a negative
number. -/
def argument (text : String) : String :=
  if text.startsWith "-" || (text.startsWith "." && text.contains ' ') then "(" ++ text ++ ")"
  else text

mutual

/-- A value as Lean writes it, read with its schema; `?` where it does not fit. -/
def display : Schema → Value → String
  | .nat, .nat n => toString n
  | .int, .int i => toString i
  | .string, .string s => s.quote
  | .bytes, .bytes b => toString b.toList
  | .unit, .ctor 0 [] => "()"
  | .list item, .list vs => "[" ++ ", ".intercalate (vs.map item.display) ++ "]"
  | .map key value, .list vs => "{" ++ ", ".intercalate (vs.map fun
      | .ctor 0 [k, v] => key.display k ++ " ↦ " ++ value.display v
      | _ => "?") ++ "}"
  | .record _ _ fields, .ctor 0 vs => "{ " ++ ", ".intercalate (displayFields fields vs) ++ " }"
  | .sum _ _ ctors, .ctor k vs => displayCtor ctors k vs
  | _, _ => "?"

def displayFields : List (Field Schema) → List Value → List String
  | ⟨name, _, s, _⟩ :: fs, v :: vs => (name ++ " := " ++ s.display v) :: displayFields fs vs
  | _, _ => []

def displayArgs : List (Field Schema) → List Value → List String
  | ⟨_, _, s, _⟩ :: fs, v :: vs => argument (s.display v) :: displayArgs fs vs
  | _, _ => []

def displayCtor : List (Ctor Schema) → Nat → List Value → String
  | ⟨name, _, fields⟩ :: _, 0, vs => " ".intercalate (("." ++ name) :: displayArgs fields vs)
  | _ :: cs, k + 1, vs => displayCtor cs k vs
  | [], _, _ => "?"

end

def was (aliases : List String) : String :=
  if aliases.isEmpty then "" else " (was " ++ " ".intercalate aliases ++ ")"

def Field.text (f : Field Schema) : String :=
  let default := match f.default with
    | some v => " := " ++ f.schema.display v
    | none => ""
  f.name ++ was f.aliases ++ " : " ++ f.schema.name ++ default

/-- The declaration of a named type; `none` for any other. -/
def declaration : Schema → Option String
  | s@(.record _ _ fields) =>
    some ("\n".intercalate (("structure " ++ s.name ++ " where") :: fields.map fun f =>
      "  " ++ f.text))
  | s@(.sum _ _ ctors) =>
    some ("\n".intercalate (("inductive " ++ s.name ++ " where") :: ctors.map fun c =>
      "  | " ++ c.name ++ was c.aliases
        ++ String.join (c.fields.map fun f => " (" ++ f.text ++ ")")))
  | _ => none

/-- The type a schema describes, then each named type in it, once, outermost first. -/
def text (s : Schema) : String :=
  let types := s.named.foldl (fun (seen : List Schema) t =>
    if seen.any (·.name == t.name) then seen else seen ++ [t]) []
  "\n\n".intercalate (s.name :: types.filterMap declaration) ++ "\n"

end Schema

end Lanes
