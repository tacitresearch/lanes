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
  deriving Inhabited

mutual

/-- Written by hand: Lean derives no lawful equality for a type nested in `List`. -/
def Value.beq : Value → Value → Bool
  | .nat a, .nat b => a == b
  | .int a, .int b => a == b
  | .string a, .string b => a == b
  | .bytes a, .bytes b => a == b
  | .list as, .list bs => Value.beqAll as bs
  | .ctor i as, .ctor j bs => i == j && Value.beqAll as bs
  | _, _ => false

def Value.beqAll : List Value → List Value → Bool
  | [], [] => true
  | a :: as, b :: bs => Value.beq a b && Value.beqAll as bs
  | _, _ => false

end

instance : BEq Value := ⟨Value.beq⟩

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
  deriving Inhabited

mutual

/-- Written by hand, as `Value.beq` is. -/
def Schema.beq : Schema → Schema → Bool
  | .nat, .nat | .int, .int | .string, .string | .bytes, .bytes | .unit, .unit => true
  | .list a, .list b | .dependent a, .dependent b => Schema.beq a b
  | .map k v, .map k' v' => Schema.beq k k' && Schema.beq v v'
  | .record t as fs, .record t' as' fs' =>
    t == t' && Schema.beqAll as as' && Schema.beqFields fs fs'
  | .sum t as cs, .sum t' as' cs' => t == t' && Schema.beqAll as as' && Schema.beqCtors cs cs'
  | _, _ => false

def Schema.beqAll : List Schema → List Schema → Bool
  | [], [] => true
  | a :: as, b :: bs => Schema.beq a b && Schema.beqAll as bs
  | _, _ => false

def Schema.beqFields : List (Schema.Field Schema) → List (Schema.Field Schema) → Bool
  | [], [] => true
  | ⟨n, a, s, d⟩ :: fs, ⟨n', a', s', d'⟩ :: fs' =>
    n == n' && a == a' && Schema.beq s s' && d == d' && Schema.beqFields fs fs'
  | _, _ => false

def Schema.beqCtors : List (Schema.Ctor Schema) → List (Schema.Ctor Schema) → Bool
  | [], [] => true
  | ⟨n, a, fs⟩ :: cs, ⟨n', a', fs'⟩ :: cs' =>
    n == n' && a == a' && Schema.beqFields fs fs' && Schema.beqCtors cs cs'
  | _, _ => false

end

instance : BEq Schema := ⟨Schema.beq⟩

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

/-! A schema as a value, so that a file can hold the schema of what it holds. -/

/-- A field's default as a value: `none` is `.ctor 0 []`, `some v` is `.ctor 1 [v]`. -/
def defaultValue : Option Value → Value
  | none => .ctor 0 []
  | some v => .ctor 1 [v]

def defaultOf? : Value → Option (Option Value)
  | .ctor 0 [] => some none
  | .ctor 1 [v] => some (some v)
  | _ => none

def stringsOf? : List Value → Option (List String)
  | [] => some []
  | .string s :: vs => (stringsOf? vs).map (s :: ·)
  | _ => none

mutual

/-- Each kind of schema is a constructor, in the order `Schema` declares them. -/
def toValue : Schema → Value
  | .nat => .ctor 0 []
  | .int => .ctor 1 []
  | .string => .ctor 2 []
  | .bytes => .ctor 3 []
  | .unit => .ctor 4 []
  | .list item => .ctor 5 [toValue item]
  | .map key value => .ctor 6 [toValue key, toValue value]
  | .record type args fields => .ctor 7 [.string type, .list (toValues args), .list (fieldValues fields)]
  | .sum type args ctors => .ctor 8 [.string type, .list (toValues args), .list (ctorValues ctors)]
  | .dependent index => .ctor 9 [toValue index]

def toValues : List Schema → List Value
  | [] => []
  | s :: ss => toValue s :: toValues ss

def fieldValues : List (Field Schema) → List Value
  | [] => []
  | ⟨name, aliases, s, default⟩ :: fs =>
    .ctor 0 [.string name, .list (aliases.map .string), toValue s, defaultValue default]
      :: fieldValues fs

def ctorValues : List (Ctor Schema) → List Value
  | [] => []
  | ⟨name, aliases, fields⟩ :: cs =>
    .ctor 0 [.string name, .list (aliases.map .string), .list (fieldValues fields)] :: ctorValues cs

end

mutual

def ofValue? : Value → Option Schema
  | .ctor 0 [] => some .nat
  | .ctor 1 [] => some .int
  | .ctor 2 [] => some .string
  | .ctor 3 [] => some .bytes
  | .ctor 4 [] => some .unit
  | .ctor 5 [item] => (ofValue? item).map .list
  | .ctor 6 [key, value] => do return .map (← ofValue? key) (← ofValue? value)
  | .ctor 7 [.string type, .list args, .list fields] => do
    return .record type (← ofValues? args) (← fieldsOf? fields)
  | .ctor 8 [.string type, .list args, .list ctors] => do
    return .sum type (← ofValues? args) (← ctorsOf? ctors)
  | .ctor 9 [index] => (ofValue? index).map .dependent
  | _ => none

def ofValues? : List Value → Option (List Schema)
  | [] => some []
  | v :: vs => do return (← ofValue? v) :: (← ofValues? vs)

def fieldsOf? : List Value → Option (List (Field Schema))
  | [] => some []
  | .ctor 0 [.string name, .list aliases, s, default] :: fs => do
    return ⟨name, ← stringsOf? aliases, ← ofValue? s, ← defaultOf? default⟩ :: (← fieldsOf? fs)
  | _ :: _ => none

def ctorsOf? : List Value → Option (List (Ctor Schema))
  | [] => some []
  | .ctor 0 [.string name, .list aliases, .list fields] :: cs => do
    return ⟨name, ← stringsOf? aliases, ← fieldsOf? fields⟩ :: (← ctorsOf? cs)
  | _ :: _ => none

end

theorem defaultOf?_defaultValue (d : Option Value) : defaultOf? (defaultValue d) = some d := by
  cases d <;> rfl

theorem stringsOf?_map (ss : List String) : stringsOf? (ss.map .string) = some ss := by
  induction ss with
  | nil => rfl
  | cons s ss ih => simp [stringsOf?, ih]

mutual

theorem ofValue?_toValue : (s : Schema) → ofValue? (toValue s) = some s
  | .nat | .int | .string | .bytes | .unit => rfl
  | .list item => by simp [toValue, ofValue?, ofValue?_toValue item]
  | .dependent index => by simp [toValue, ofValue?, ofValue?_toValue index]
  | .map key value => by simp [toValue, ofValue?, ofValue?_toValue key, ofValue?_toValue value]
  | .record type args fields => by
    simp [toValue, ofValue?, ofValues?_toValues args, fieldsOf?_fieldValues fields]
  | .sum type args ctors => by
    simp [toValue, ofValue?, ofValues?_toValues args, ctorsOf?_ctorValues ctors]

theorem ofValues?_toValues : (ss : List Schema) → ofValues? (toValues ss) = some ss
  | [] => rfl
  | s :: ss => by simp [toValues, ofValues?, ofValue?_toValue s, ofValues?_toValues ss]

theorem fieldsOf?_fieldValues : (fs : List (Field Schema)) → fieldsOf? (fieldValues fs) = some fs
  | [] => rfl
  | ⟨name, aliases, s, default⟩ :: fs => by
    simp [fieldValues, fieldsOf?, stringsOf?_map, ofValue?_toValue s, defaultOf?_defaultValue,
      fieldsOf?_fieldValues fs]

theorem ctorsOf?_ctorValues : (cs : List (Ctor Schema)) → ctorsOf? (ctorValues cs) = some cs
  | [] => rfl
  | ⟨name, aliases, fields⟩ :: cs => by
    simp [ctorValues, ctorsOf?, stringsOf?_map, fieldsOf?_fieldValues fields,
      ctorsOf?_ctorValues cs]

end

end Schema

end Lanes
