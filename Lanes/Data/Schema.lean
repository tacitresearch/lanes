/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std

/-!
A `Schema` says what a type is, as data: a table of the named types it uses, each declared once
as a record or a sum with the names of its fields and constructors, the defaults of its fields
and their former names, and the root, the type itself. Wherever a type is used, in the root or a
field, a primitive, a list, a map or a dependent pair is written out and a named type is a
reference to the table by its name (`Schema.Ty.ref`), so a type used in many places is declared
once and a type may refer to itself. A `Value` is a value of any schema: a number, a string,
bytes, a list, or a constructor's index and its fields. `Schema.Of α` ties a schema to a type,
with a map each way between `α` and `Value` and the law that a value read back from its `Value`
is itself.

A value carries no names. A constructor is its index in its declaration, and fields come in the
declaration's order, so that the names are written once, in the schema, and a reader matches
them.

A named type is named as Lean writes it with its arguments (`Prod Nat String`), and two named
types of one name are one type: the table keeps the first.
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

mutual

theorem Value.beq_refl : (v : Value) → Value.beq v v = true
  | .nat _ | .int _ | .string _ | .bytes _ => by simp [Value.beq]
  | .list vs => by simp only [Value.beq]; exact Value.beqAll_refl vs
  | .ctor _ vs => by simp only [Value.beq, beq_self_eq_true, Bool.true_and]; exact Value.beqAll_refl vs

theorem Value.beqAll_refl : (vs : List Value) → Value.beqAll vs vs = true
  | [] => rfl
  | v :: vs => by simp only [Value.beqAll, Value.beq_refl v, Value.beqAll_refl vs, Bool.and_self]

end

mutual

theorem Value.eq_of_beq : (a b : Value) → Value.beq a b = true → a = b
  | .nat _, b, h | .int _, b, h | .string _, b, h | .bytes _, b, h => by
    cases b <;> simp_all [Value.beq]
  | .list as, b, h => by
    cases b <;> simp [Value.beq] at h
    rw [Value.eq_of_beqAll as _ h]
  | .ctor _ as, b, h => by
    cases b <;> simp [Value.beq] at h
    rw [h.1, Value.eq_of_beqAll as _ h.2]

theorem Value.eq_of_beqAll : (as bs : List Value) → Value.beqAll as bs = true → as = bs
  | [], [], _ => rfl
  | [], _ :: _, h | _ :: _, [], h => by simp [Value.beqAll] at h
  | a :: as, b :: bs, h => by
    simp only [Value.beqAll, Bool.and_eq_true] at h
    rw [Value.eq_of_beq a b h.1, Value.eq_of_beqAll as bs h.2]

end

instance Value.instLawfulBEq : LawfulBEq Value where
  rfl := Value.beq_refl _
  eq_of_beq := Value.eq_of_beq _ _

/-- A field of a record or of a constructor, whose type is a `σ`. -/
structure Schema.Field (σ : Type) where
  name : String
  /-- The field's former names. -/
  aliases : List String := []
  schema : σ
  /-- What a reader takes when the data has no such field. -/
  default : Option Value := none
  deriving BEq, ReflBEq, LawfulBEq

structure Schema.Ctor (σ : Type) where
  name : String
  /-- The constructor's former names. -/
  aliases : List String := []
  fields : List (Schema.Field σ)
  deriving BEq, ReflBEq, LawfulBEq

/-- The type of a value where it is used: a primitive, a list, a map, a dependent pair, or a
named type, by its name in the schema's table. -/
inductive Schema.Ty where
  | nat
  | int
  | string
  | bytes
  | unit
  | list (item : Schema.Ty)
  /-- A map, whose value is the list of its entries, each a `Prod` of a key and a value. -/
  | map (key value : Schema.Ty)
  /-- A pair whose second part's schema depends on the value of the first (`Codec.sigma`), so
  only the first part's type is known here. -/
  | dependent (index : Schema.Ty)
  | ref (name : String)
  deriving DecidableEq, Inhabited, Repr

/-- A named type: a record of fields or a sum of constructors. `type` is the Lean type's name;
the table names it with its arguments. -/
inductive Schema.Decl where
  | record (type : String) (fields : List (Schema.Field Schema.Ty))
  | sum (type : String) (ctors : List (Schema.Ctor Schema.Ty))
  deriving BEq, ReflBEq, LawfulBEq

/-- The named types, each once, by name, the outermost first; and the type described. -/
structure Schema where
  types : List (String × Schema.Decl)
  root : Schema.Ty
  deriving BEq, ReflBEq, LawfulBEq, Inhabited

/-- A type's schema, with a map each way between its values and `Value`, and the law that ties
them. -/
structure Schema.Of (α : Type) where
  schema : Schema
  toValue : α → Value
  ofValue : Value → Option α
  ofValue_toValue : ∀ a, ofValue (toValue a) = some a

/-- The fields of a record or of a constructor, over nested pairs that end in `Unit`, with the
named types their types use. -/
structure Schema.Fields (α : Type) where
  schemas : List (Schema.Field Schema.Ty)
  types : List (String × Schema.Decl)
  toValues : α → List Value
  ofValues : List Value → Option α
  ofValues_toValues : ∀ a, ofValues (toValues a) = some a

/-- The constructors of a sum, over nested sums that end in `Empty`: a value is its
constructor's index and its fields. -/
structure Schema.Ctors (α : Type) where
  schemas : List (Schema.Ctor Schema.Ty)
  types : List (String × Schema.Decl)
  toValue : α → Nat × List Value
  ofValue : Nat → List Value → Option α
  ofValue_toValue : ∀ a, ofValue (toValue a).1 (toValue a).2 = some a

namespace Schema

variable {α β : Type}

/-- In parentheses unless it is one word. -/
def paren (text : String) : String :=
  if text.contains ' ' then "(" ++ text ++ ")" else text

/-- The type as Lean writes it. -/
def Ty.name : Ty → String
  | .nat => "Nat"
  | .int => "Int"
  | .string => "String"
  | .bytes => "ByteArray"
  | .unit => "Unit"
  | .list item => "List " ++ paren item.name
  | .map key value => "Map " ++ paren key.name ++ " " ++ paren value.name
  | .dependent index => "Σ " ++ paren index.name
  | .ref name => name

/-- The named types a type refers to. -/
def Ty.refs : Ty → List String
  | .list item | .dependent item => item.refs
  | .map key value => key.refs ++ value.refs
  | .ref name => [name]
  | .nat | .int | .string | .bytes | .unit => []

def Decl.type : Decl → String
  | .record type _ | .sum type _ => type

/-- The named types a declaration's fields refer to. -/
def Decl.refs : Decl → List String
  | .record _ fields => fields.flatMap (·.schema.refs)
  | .sum _ ctors => ctors.flatMap fun c => c.fields.flatMap (·.schema.refs)

/-- The name of a named type: the Lean type's name and its arguments. -/
def nameOf (type : String) (args : List Ty) : String :=
  " ".intercalate (type :: args.map (paren ·.name))

/-- The type the schema describes, as Lean writes it. -/
def name (s : Schema) : String := s.root.name

/-- The Lean type's name, if the schema describes a named type it declares. -/
def type? (s : Schema) : Option String :=
  match s.root with
  | .ref name => (s.types.lookup name).map (·.type)
  | _ => none

/-- `a`'s named types, then those of `b` that `a` does not name. -/
def merge (a b : List (String × Decl)) : List (String × Decl) :=
  a ++ b.filter fun e => !a.any (·.1 == e.1)

/-- The table with `name` declared as `decl`, first. -/
def declare (name : String) (decl : Decl) (types : List (String × Decl)) :
    List (String × Decl) :=
  (name, decl) :: types.filter (·.1 != name)

@[simp] theorem lookup_declare (name : String) (decl : Decl) (types : List (String × Decl)) :
    (declare name decl types).lookup name = some decl := by
  simp [declare]

/-- A map from `key` to `value`, as `Codec.extTreeMap` writes it. -/
def map (key value : Schema) : Schema := ⟨merge key.types value.types, .map key.root value.root⟩

namespace Fields

def nil : Fields Unit where
  schemas := []
  types := []
  toValues _ := []
  ofValues
    | [] => some ()
    | _ :: _ => none
  ofValues_toValues _ := rfl

def cons (name : String) (aliases : List String) (s : Of α) (default : Option α)
    (rest : Fields β) : Fields (α × β) where
  schemas := { name, aliases, schema := s.schema.root, default := default.map s.toValue }
    :: rest.schemas
  types := merge s.schema.types rest.types
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
  types := []
  toValue e := nomatch e
  ofValue _ _ := none
  ofValue_toValue e := nomatch e

def cons (name : String) (aliases : List String) (fields : Fields α) (rest : Ctors β) :
    Ctors (α ⊕ β) where
  schemas := { name, aliases, fields := fields.schemas } :: rest.schemas
  types := merge fields.types rest.types
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

/-- A type with no named type in it. -/
def prim (t : Ty) (toValue : α → Value) (ofValue : Value → Option α)
    (h : ∀ a, ofValue (toValue a) = some a) : Of α :=
  ⟨⟨[], t⟩, toValue, ofValue, h⟩

def nat : Of Nat :=
  prim .nat .nat (fun | .nat n => some n | _ => none) fun _ => rfl

def int : Of Int :=
  prim .int .int (fun | .int i => some i | _ => none) fun _ => rfl

def string : Of String :=
  prim .string .string (fun | .string s => some s | _ => none) fun _ => rfl

def bytes : Of ByteArray :=
  prim .bytes .bytes (fun | .bytes b => some b | _ => none) fun _ => rfl

def unit : Of Unit :=
  prim .unit (fun _ => .ctor 0 []) (fun | .ctor 0 [] => some () | _ => none) fun _ => rfl

/-- A type described as another. `back` may refuse what `to` never produces. -/
def map (s : Of β) (to : α → β) (back : β → Option α) (h : ∀ a, back (to a) = some a) :
    Of α where
  schema := s.schema
  toValue a := s.toValue (to a)
  ofValue v := (s.ofValue v).bind back
  ofValue_toValue a := by simp [s.ofValue_toValue, h]

/-- The record `type` applied to types of the schemas `args`. -/
def record (type : String) (args : List Ty) (fields : Fields α) : Of α where
  schema := ⟨declare (nameOf type args) (.record type fields.schemas) fields.types,
    .ref (nameOf type args)⟩
  toValue a := .ctor 0 (fields.toValues a)
  ofValue
    | .ctor 0 vs => fields.ofValues vs
    | _ => none
  ofValue_toValue a := fields.ofValues_toValues a

def variants (type : String) (args : List Ty) (ctors : Ctors α) : Of α where
  schema := ⟨declare (nameOf type args) (.sum type ctors.schemas) ctors.types,
    .ref (nameOf type args)⟩
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
  schema := ⟨s.schema.types, .list s.schema.root⟩
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
  (record "Prod" [a.schema.root, b.schema.root]
      (.cons "fst" [] a none (.cons "snd" [] b none .nil))).map
    (fun (x, y) => (x, y, ())) (fun (x, y, ()) => some (x, y)) (fun _ => rfl)

def sum (a : Of α) (b : Of β) : Of (α ⊕ β) :=
  (variants "Sum" [a.schema.root, b.schema.root]
      (.cons "inl" [] (.cons "val" [] a none .nil) (.cons "inr" [] (.cons "val" [] b none .nil)
        .nil))).map
    (fun | .inl x => .inl (x, ()) | .inr y => .inr (.inl (y, ())))
    (fun | .inl (x, ()) => some (.inl x) | .inr (.inl (y, ())) => some (.inr y)
         | .inr (.inr e) => nomatch e)
    (by intro x; cases x <;> rfl)

def option (s : Of α) : Of (Option α) :=
  (variants "Option" [s.schema.root]
      (.cons "none" [] .nil (.cons "some" [] (.cons "val" [] s none .nil) .nil))).map
    (fun | none => .inl () | some a => .inr (.inl (a, ())))
    (fun | .inl () => some none | .inr (.inl (a, ())) => some (some a) | .inr (.inr e) => nomatch e)
    (by intro x; cases x <;> rfl)

def sigma {ι : Type} {β : ι → Type} (a : Of ι) (b : ∀ i, Of (β i)) : Of ((i : ι) × β i) where
  schema := ⟨a.schema.types, .dependent a.schema.root⟩
  toValue x := .ctor 0 [a.toValue x.1, (b x.1).toValue x.2]
  ofValue
    | .ctor 0 [vi, vb] => do
      let i ← a.ofValue vi
      let v ← (b i).ofValue vb
      return ⟨i, v⟩
    | _ => none
  ofValue_toValue x := by simp [a.ofValue_toValue, (b x.1).ofValue_toValue]

end Of


/-! The text of a schema: the type it describes, then the declaration of each named type in its
table, written as `lanes_data` writes it. -/

/-- A value as an argument: in parentheses if it is a constructor with arguments or a negative
number. -/
def argument (text : String) : String :=
  if text.startsWith "-" || (text.startsWith "." && text.contains ' ') then "(" ++ text ++ ")"
  else text

mutual

/-- A value with no schema, as the second part of a `dependent` pair is written: a constructor
is its index after `#`, then its fields. -/
def _root_.Lanes.Value.text : Value → String
  | .nat n => toString n
  | .int i => toString i
  | .string s => s.quote
  | .bytes b => toString b.toList
  | .list vs => "[" ++ ", ".intercalate (Value.texts vs) ++ "]"
  | .ctor k [] => "#" ++ toString k
  | .ctor k vs => "#" ++ toString k ++ "(" ++ ", ".intercalate (Value.texts vs) ++ ")"

def _root_.Lanes.Value.texts : List Value → List String
  | [] => []
  | v :: vs => Value.text v :: Value.texts vs

end

/-- How deep `display` and the other readings of a value with its schema go: further than any
reader's `maxDepth`, so only a value no reader gives is cut short. -/
def displayDepth : Nat := 4096

section

variable (types : List (String × Decl))

/-- A value as Lean writes it, read with its type, nested at most `fuel` more; `?` where it does
not fit and `…` past `fuel`. -/
def displayAt : Nat → Ty → Value → String
  | _, .nat, .nat n => toString n
  | _, .int, .int i => toString i
  | _, .string, .string s => s.quote
  | _, .bytes, .bytes b => toString b.toList
  | _, .unit, .ctor 0 [] => "()"
  | 0, _, _ => "…"
  | d + 1, .list item, .list vs => "[" ++ ", ".intercalate (vs.map (displayAt d item)) ++ "]"
  | d + 1, .map key value, .list vs => "{" ++ ", ".intercalate (vs.map fun
      | .ctor 0 [k, v] => displayAt d key k ++ " ↦ " ++ displayAt d value v
      | _ => "?") ++ "}"
  | d + 1, .dependent index, .ctor 0 [i, v] => "⟨" ++ displayAt d index i ++ ", " ++ v.text ++ "⟩"
  | d + 1, .ref name, .ctor k vs =>
    match types.lookup name with
    | some (.record _ fields) =>
      if k = 0 then
        "{ " ++ ", ".intercalate ((fields.zip vs).map fun (f, v) =>
          f.name ++ " := " ++ displayAt d f.schema v) ++ " }"
      else "?"
    | some (.sum _ ctors) =>
      match ctors[k]? with
      | some c => " ".intercalate (("." ++ c.name) :: (c.fields.zip vs).map fun (f, v) =>
          argument (displayAt d f.schema v))
      | none => "?"
    | none => "?"
  | _, _, _ => "?"

def was (aliases : List String) : String :=
  if aliases.isEmpty then "" else " (was " ++ " ".intercalate aliases ++ ")"

def Field.text (f : Field Ty) : String :=
  let default := match f.default with
    | some v => " := " ++ displayAt types displayDepth f.schema v
    | none => ""
  f.name ++ was f.aliases ++ " : " ++ f.schema.name ++ default

/-- The declaration of the named type `name`. -/
def declaration (name : String) : Decl → String
  | .record _ fields =>
    "\n".intercalate (("structure " ++ name ++ " where") :: fields.map fun f =>
      "  " ++ Field.text types f)
  | .sum _ ctors =>
    "\n".intercalate (("inductive " ++ name ++ " where") :: ctors.map fun c =>
      "  | " ++ c.name ++ was c.aliases
        ++ String.join (c.fields.map fun f => " (" ++ Field.text types f ++ ")"))

end

/-- A value as Lean writes it, read with its schema; `?` where it does not fit. -/
def display (s : Schema) (v : Value) : String := displayAt s.types displayDepth s.root v

/-- The type a schema describes, then each named type in its table, outermost first. -/
def text (s : Schema) : String :=
  "\n\n".intercalate (s.name :: s.types.map fun (name, d) => declaration s.types name d) ++ "\n"

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

/-- Each kind of type is a constructor, in the order `Ty` declares them. -/
def Ty.toValue : Ty → Value
  | .nat => .ctor 0 []
  | .int => .ctor 1 []
  | .string => .ctor 2 []
  | .bytes => .ctor 3 []
  | .unit => .ctor 4 []
  | .list item => .ctor 5 [item.toValue]
  | .map key value => .ctor 6 [key.toValue, value.toValue]
  | .dependent index => .ctor 7 [index.toValue]
  | .ref name => .ctor 8 [.string name]

def Ty.ofValue? : Value → Option Ty
  | .ctor 0 [] => some .nat
  | .ctor 1 [] => some .int
  | .ctor 2 [] => some .string
  | .ctor 3 [] => some .bytes
  | .ctor 4 [] => some .unit
  | .ctor 5 [item] => (Ty.ofValue? item).map .list
  | .ctor 6 [key, value] => do return .map (← Ty.ofValue? key) (← Ty.ofValue? value)
  | .ctor 7 [index] => (Ty.ofValue? index).map .dependent
  | .ctor 8 [.string name] => some (.ref name)
  | _ => none

def fieldValue (f : Field Ty) : Value :=
  .ctor 0 [.string f.name, .list (f.aliases.map .string), f.schema.toValue, defaultValue f.default]

def fieldOf? : Value → Option (Field Ty)
  | .ctor 0 [.string name, .list aliases, s, default] => do
    return ⟨name, ← stringsOf? aliases, ← Ty.ofValue? s, ← defaultOf? default⟩
  | _ => none

def ctorValue (c : Ctor Ty) : Value :=
  .ctor 0 [.string c.name, .list (c.aliases.map .string), .list (c.fields.map fieldValue)]

def ctorOf? : Value → Option (Ctor Ty)
  | .ctor 0 [.string name, .list aliases, .list fields] => do
    return ⟨name, ← stringsOf? aliases, ← fields.mapM fieldOf?⟩
  | _ => none

/-- A record is constructor `0` and a sum `1`, each with its type's name. -/
def Decl.toValue : Decl → Value
  | .record type fields => .ctor 0 [.string type, .list (fields.map fieldValue)]
  | .sum type ctors => .ctor 1 [.string type, .list (ctors.map ctorValue)]

def Decl.ofValue? : Value → Option Decl
  | .ctor 0 [.string type, .list fields] => do return .record type (← fields.mapM fieldOf?)
  | .ctor 1 [.string type, .list ctors] => do return .sum type (← ctors.mapM ctorOf?)
  | _ => none

def entryValue (e : String × Decl) : Value := .ctor 0 [.string e.1, e.2.toValue]

def entryOf? : Value → Option (String × Decl)
  | .ctor 0 [.string name, d] => do return (name, ← Decl.ofValue? d)
  | _ => none

/-- The table, then the root. -/
def toValue (s : Schema) : Value := .ctor 0 [.list (s.types.map entryValue), s.root.toValue]

def ofValue? : Value → Option Schema
  | .ctor 0 [.list types, root] => do return ⟨← types.mapM entryOf?, ← Ty.ofValue? root⟩
  | _ => none

theorem defaultOf?_defaultValue (d : Option Value) : defaultOf? (defaultValue d) = some d := by
  cases d <;> rfl

theorem stringsOf?_map (ss : List String) : stringsOf? (ss.map .string) = some ss := by
  induction ss with
  | nil => rfl
  | cons s ss ih => simp [stringsOf?, ih]

theorem Ty.ofValue?_toValue : (t : Ty) → Ty.ofValue? t.toValue = some t
  | .nat | .int | .string | .bytes | .unit | .ref _ => rfl
  | .list item => by simp [Ty.toValue, Ty.ofValue?, Ty.ofValue?_toValue item]
  | .dependent index => by simp [Ty.toValue, Ty.ofValue?, Ty.ofValue?_toValue index]
  | .map key value => by
    simp [Ty.toValue, Ty.ofValue?, Ty.ofValue?_toValue key, Ty.ofValue?_toValue value]

theorem mapM_some {γ : Type} {g : γ → Option γ} (h : ∀ x, g x = some x) (xs : List γ) :
    xs.mapM g = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [h, ih]

theorem fieldOf?_fieldValue (f : Field Ty) : fieldOf? (fieldValue f) = some f := by
  simp [fieldValue, fieldOf?, stringsOf?_map, Ty.ofValue?_toValue, defaultOf?_defaultValue]

theorem ctorOf?_ctorValue (c : Ctor Ty) : ctorOf? (ctorValue c) = some c := by
  simp [ctorValue, ctorOf?, stringsOf?_map,
    mapM_some (g := fieldOf? ∘ fieldValue) fieldOf?_fieldValue]

theorem Decl.ofValue?_toValue (d : Decl) : Decl.ofValue? d.toValue = some d := by
  cases d <;>
    simp [Decl.toValue, Decl.ofValue?, mapM_some (g := fieldOf? ∘ fieldValue) fieldOf?_fieldValue,
      mapM_some (g := ctorOf? ∘ ctorValue) ctorOf?_ctorValue]

theorem entryOf?_entryValue (e : String × Decl) : entryOf? (entryValue e) = some e := by
  simp [entryValue, entryOf?, Decl.ofValue?_toValue]

theorem ofValue?_toValue (s : Schema) : ofValue? s.toValue = some s := by
  simp [toValue, ofValue?, mapM_some (g := entryOf? ∘ entryValue) entryOf?_entryValue,
    Ty.ofValue?_toValue]

end Schema

end Lanes
