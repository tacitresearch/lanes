/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std
public import Std.Data.String.ToNat
public import Lanes.Data.Schema

/-!
A `Codec` writes a value as a run of records and reads it back, with the law that reading what
was written gives the value and leaves what followed. The law is a field, so a codec without it
cannot be built, and codecs for pairs, sums, lists and mapped types keep it by construction.

A codec also carries its type's `Schema.Of`: the schema, and the map each way to `Value`. The
combinators give the schemas of Lean's own types (`Prod`, `Sum`, `Option`), and `Codec.struct%`
and `Codec.sum%` a record or a sum with the names of the fields and constructors. The records
written are not yet derived from them.

Records are whole byte strings. Where one ends and the next begins is not a codec's concern:
`Lanes.Frame` settles that, with its own proofs.

Every reader is bounded by its input (rule 2.6), since the records may come from a damaged file
or a peer. A list is the one reader that repeats, and it repeats as often as its count says, so
it refuses a count larger than the records left. Each element takes at least one record for
that: an element written as none, such as `()`, is written as one empty record instead.
-/

@[expose] public section

namespace Lanes

structure Codec (α : Type) extends Schema.Of α where
  write : α → List ByteArray
  read : List ByteArray → Option (α × List ByteArray)
  sound : ∀ a rest, read (write a ++ rest) = some (a, rest)
  /-- Whether every value is written as at least one record. Only a list reads this: it pads
  the elements of a codec without it. `false` is always safe. -/
  consumes : Bool := false
  consumes_write : consumes = true → ∀ a, write a ≠ [] := by simp

namespace Codec

variable {α β : Type}

theorem fromUTF8?_toUTF8 (s : String) : String.fromUTF8? s.toUTF8 = some s := by
  simp [String.fromUTF8?, String.fromUTF8, s.isValidUTF8]

def bytes : Codec ByteArray where
  toOf := .bytes
  write b := [b]
  read
    | b :: rest => some (b, rest)
    | [] => none
  sound _ _ := rfl
  consumes := true
  consumes_write _ _ := by simp

def unit : Codec Unit where
  toOf := .unit
  write _ := []
  read rest := some ((), rest)
  sound _ _ := rfl

def string : Codec String where
  toOf := .string
  write s := [s.toUTF8]
  read
    | b :: rest => (String.fromUTF8? b).map (·, rest)
    | [] => none
  sound s rest := by
    show (String.fromUTF8? s.toUTF8).map (·, rest) = _
    rw [fromUTF8?_toUTF8]
    rfl
  consumes := true
  consumes_write _ _ := by simp

def nat : Codec Nat where
  toOf := .nat
  write n := [(toString n).toUTF8]
  read
    | b :: rest => ((String.fromUTF8? b).bind String.toNat?).map (·, rest)
    | [] => none
  sound n rest := by
    show ((String.fromUTF8? (toString n).toUTF8).bind String.toNat?).map (·, rest) = _
    rw [fromUTF8?_toUTF8]
    simp
  consumes := true
  consumes_write _ _ := by simp

/-- One after the other. -/
def pair (a : Codec α) (b : Codec β) : Codec (α × β) where
  toOf := .pair a.toOf b.toOf
  write x := a.write x.1 ++ b.write x.2
  read records := do
    let (x, rest) ← a.read records
    let (y, rest) ← b.read rest
    return ((x, y), rest)
  sound x rest := by simp [List.append_assoc, a.sound, b.sound]
  consumes := a.consumes || b.consumes
  consumes_write h x := by
    rcases Bool.or_eq_true_iff.mp h with h | h
    · exact fun e => a.consumes_write h x.1 (List.append_eq_nil_iff.mp e).1
    · exact fun e => b.consumes_write h x.2 (List.append_eq_nil_iff.mp e).2

/-- A type written as another. `back` may refuse what `to` never produces. -/
def map (c : Codec β) (to : α → β) (back : β → Option α) (h : ∀ a, back (to a) = some a) :
    Codec α where
  toOf := c.toOf.map to back h
  write a := c.write (to a)
  read records := do
    let (b, rest) ← c.read records
    let a ← back b
    return (a, rest)
  sound a rest := by simp [c.sound, h]
  consumes := c.consumes
  consumes_write hc a := c.consumes_write hc (to a)

/-- A pair whose second part's type, and so its codec, depends on the first. -/
def sigma {ι : Type} {β : ι → Type} (a : Codec ι) (b : ∀ i, Codec (β i)) :
    Codec ((i : ι) × β i) where
  toOf := .sigma a.toOf fun i => (b i).toOf
  write x := a.write x.1 ++ (b x.1).write x.2
  read records := do
    let (i, rest) ← a.read records
    let (v, rest) ← (b i).read rest
    return (⟨i, v⟩, rest)
  sound x rest := by simp [List.append_assoc, a.sound, (b x.1).sound]
  consumes := a.consumes
  consumes_write h x e := a.consumes_write h x.1 (List.append_eq_nil_iff.mp e).1

/-- Written as the value; read back only with the property. -/
def subtype {p : α → Prop} [DecidablePred p] (c : Codec α) : Codec {a // p a} :=
  c.map (·.val) (fun a => if h : p a then some ⟨a, h⟩ else none) fun a => by simp [a.property]

/-- Replaces a codec's schema and values, leaving its records. -/
def withSchema (c : Codec α) (s : Schema.Of α) : Codec α := { c with toOf := s }

def bool : Codec Bool :=
  (nat.map (fun b => if b then 1 else 0)
    (fun n => if n = 0 then some false else if n = 1 then some true else none)
    (by intro b; cases b <;> rfl)).withSchema .bool

def fin {n : Nat} : Codec (Fin n) :=
  nat.map (·.val) (fun k => if h : k < n then some ⟨k, h⟩ else none) (by intro a; simp)

def int : Codec Int :=
  ((pair bool nat).map (fun i => (decide (i < 0), i.natAbs))
    (fun (negative, size) => some (if negative then -(size : Int) else size))
    (by intro i; by_cases h : i < 0 <;> simp [h] <;> omega)).withSchema .int

/-- A tag, then the value. -/
def sum (a : Codec α) (b : Codec β) : Codec (α ⊕ β) where
  toOf := .sum a.toOf b.toOf
  write
    | .inl x => nat.write 0 ++ a.write x
    | .inr y => nat.write 1 ++ b.write y
  read records := do
    let (tag, rest) ← nat.read records
    match tag with
    | 0 => (a.read rest).map fun (x, rest) => (.inl x, rest)
    | 1 => (b.read rest).map fun (y, rest) => (.inr y, rest)
    | _ => none
  sound x rest := by
    cases x <;> simp [List.append_assoc, nat.sound, a.sound, b.sound]
  consumes := true
  consumes_write _ x := by cases x <;> simp [nat]

def option (c : Codec α) : Codec (Option α) :=
  ((sum unit c).map (fun | none => .inl () | some a => .inr a)
    (fun | .inl () => some none | .inr a => some (some a)) (by intro a; cases a <;> rfl)).withSchema
    (.option c.toOf)

/-- `c`, with a value written as no records written as one empty record instead, so that it
always consumes. -/
def padded (c : Codec α) : Codec α where
  toOf := c.toOf
  write a := if c.consumes then c.write a else match c.write a with
    | [] => [.empty]
    | records => records
  read records :=
    if c.consumes then c.read records else do
      let (a, rest) ← c.read records
      if c.write a = [] then
        match rest with
        | pad :: rest => if pad.size = 0 then some (a, rest) else none
        | [] => none
      else some (a, rest)
  sound a rest := by
    by_cases hc : c.consumes
    · simp [hc, c.sound]
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      cases hw : c.write a with
      | nil =>
        have := c.sound a (.empty :: rest)
        simp only [hw, List.nil_append] at this
        simp [this, hw]
      | cons r rs =>
        have := c.sound a rest
        simp only [hw, List.cons_append] at this
        simp [this, hw]
  consumes := true
  consumes_write _ a := by
    by_cases hc : c.consumes
    · simpa [hc] using c.consumes_write hc a
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      split <;> simp_all

/-- Whether `records` has at least `n` records, looking at no more than `n`. -/
def hasAtLeast : Nat → List ByteArray → Bool
  | 0, _ => true
  | _ + 1, [] => false
  | n + 1, _ :: rest => hasAtLeast n rest

theorem hasAtLeast_iff {n : Nat} {records : List ByteArray} :
    hasAtLeast n records = true ↔ n ≤ records.length := by
  induction n generalizing records with
  | zero => simp [hasAtLeast]
  | succ n ih => cases records <;> simp [hasAtLeast, ih]

theorem length_le_flatMap (c : Codec α) (h : c.consumes = true) (as : List α) :
    as.length ≤ (as.flatMap c.write).length := by
  induction as with
  | nil => simp
  | cons a as ih =>
    have : 0 < (c.write a).length := List.length_pos_iff.mpr (c.consumes_write h a)
    simp only [List.length_cons, List.flatMap_cons, List.length_append]
    omega

def readMany (c : Codec α) : Nat → List ByteArray → Option (List α × List ByteArray)
  | 0, records => some ([], records)
  | n + 1, records => do
    let (a, rest) ← c.read records
    let (as, rest) ← readMany c n rest
    return (a :: as, rest)

theorem readMany_write (c : Codec α) (as : List α) (rest : List ByteArray) :
    readMany c as.length (as.flatMap c.write ++ rest) = some (as, rest) := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [readMany, List.append_assoc, c.sound, ih]

/-- How many, then each. Every element takes at least one record (`padded`), so a count larger
than the records left is refused before any is read, and a list is never read longer than its
records. -/
def list (c : Codec α) : Codec (List α) where
  toOf := .list c.toOf
  write as := nat.write as.length ++ as.flatMap c.padded.write
  read records := do
    let (n, rest) ← nat.read records
    if hasAtLeast n rest then readMany c.padded n rest else none
  sound as rest := by
    have hlen : as.length ≤ (as.flatMap c.padded.write ++ rest).length := by
      have := length_le_flatMap c.padded rfl as
      simp only [List.length_append]
      omega
    simp [List.append_assoc, nat.sound, hasAtLeast_iff.mpr hlen, readMany_write]
  consumes := true
  consumes_write _ _ := by simp [nat]

theorem extTreeMap_ofList_toList {κ : Type} {cmp : κ → κ → Ordering} [Std.TransCmp cmp]
    [Std.LawfulEqCmp cmp] (t : Std.ExtTreeMap κ α cmp) : .ofList t.toList cmp = t := by
  apply Std.ExtTreeMap.ext_getElem?
  intro k
  cases h : t[k]? with
  | some v =>
    exact Std.ExtTreeMap.getElem?_ofList_of_mem Std.ReflCmp.compare_self
      Std.ExtTreeMap.distinct_keys_toList (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr h)
  | none =>
    letI : BEq κ := ⟨fun a b => cmp a b == .eq⟩
    haveI : Std.LawfulBEqCmp cmp := ⟨beq_iff_eq.symm⟩
    apply Std.ExtTreeMap.getElem?_ofList_of_contains_eq_false
    rw [Bool.eq_false_iff]
    intro hk
    have : k ∈ t := by simpa using hk
    simp_all

/-- The entries, in the order of their keys. The map is the extensional one because the law is
an equality: a `Std.TreeMap` or `Std.HashMap` built again from its entries holds the same and
is another value, so neither has a codec. -/
def extTreeMap {κ : Type} (key : Codec κ) (value : Codec α)
    (cmp : κ → κ → Ordering := by exact compare) [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] :
    Codec (Std.ExtTreeMap κ α cmp) :=
  let c := (list (pair key value)).map (·.toList) (fun entries => some (.ofList entries cmp))
    (fun t => congrArg some (extTreeMap_ofList_toList t))
  { c with schema := Schema.map key.schema value.schema }

end Codec

/-- The codec a type is written with when none is named. -/
class Codable (α : Type) where
  codec : Codec α

namespace Codable

instance : Codable ByteArray := ⟨Codec.bytes⟩
instance : Codable Unit := ⟨Codec.unit⟩
instance : Codable String := ⟨Codec.string⟩
instance : Codable Nat := ⟨Codec.nat⟩
instance : Codable Bool := ⟨Codec.bool⟩
instance : Codable Int := ⟨Codec.int⟩
instance {n : Nat} : Codable (Fin n) := ⟨Codec.fin⟩

variable {α β : Type}

instance [Codable α] : Codable (Option α) := ⟨Codec.option codec⟩
instance [Codable α] : Codable (List α) := ⟨Codec.list codec⟩
instance [Codable α] [Codable β] : Codable (α × β) := ⟨Codec.pair codec codec⟩
instance [Codable α] [Codable β] : Codable (α ⊕ β) := ⟨Codec.sum codec codec⟩
instance {p : α → Prop} [DecidablePred p] [Codable α] : Codable {a // p a} :=
  ⟨Codec.subtype codec⟩

instance {ι : Type} {β : ι → Type} [Codable ι] [∀ i, Codable (β i)] :
    Codable ((i : ι) × β i) :=
  ⟨Codec.sigma codec fun _ => codec⟩

instance {κ : Type} {cmp : κ → κ → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Codable κ] [Codable α] : Codable (Std.ExtTreeMap κ α cmp) :=
  ⟨Codec.extTreeMap codec codec cmp⟩

end Codable

abbrev Codec.of (α : Type) [Codable α] : Codec α := Codable.codec

/-! Codecs for a structure and for an inductive type, one line each. The law is proved by what
the macro writes, so it holds or the line does not compile. -/

open Lean in
/-- `Codec.struct% T { a := codecA, b := codecB }`: the codec of structure `T`, a codec per
field, in the order written. -/
syntax (name := codecStruct) "Codec.struct% " ident " {" (ident " := " term),* "}" : term

open Lean in
/-- `Codec.sum% T { a (x := codecX) (y := codecY), b }`: the codec of inductive type `T`, a
constructor per entry with a codec per argument. -/
syntax (name := codecSum)
  "Codec.sum% " ident " {" (rawIdent ("(" ident " := " term ")")*),* "}" : term

namespace Codec

open Lean

/-- A field as the macros take it: its name, its codec, its former names and its default. -/
abbrev FieldSpec := Ident × TSyntax `term × Array Ident × Option (TSyntax `term)

/-- A constructor as the macros take it: its name, its former names and its fields. -/
abbrev CtorSpec := Ident × Array Ident × Array FieldSpec

/-- Variables for the values of `xs`, named apart from every constant: a value bound to a name
that is also a constructor's would be read as the constructor in a pattern. -/
meta def fresh (xs : Array Ident) : MacroM (Array (TSyntax `term)) :=
  xs.mapM fun x => return mkIdent (← Macro.addMacroScope x.getId)

/-- `(a, b, c)` as nested pairs, as a term or a pattern; `()` when empty. -/
meta def tuple (xs : Array (TSyntax `term)) : MacroM (TSyntax `term) :=
  match xs.toList.reverse with
  | [] => `(())
  | last :: rest => rest.foldlM (fun acc x => `(($x, $acc))) last

/-- `(a, b, c, ())`: nested pairs that end in `()`, as `Schema.Fields` takes them. -/
meta def fieldTuple (xs : Array (TSyntax `term)) : MacroM (TSyntax `term) := do
  xs.foldrM (fun x acc => `(($x, $acc))) (← `(()))

meta def product (codecs : Array (TSyntax `term)) : MacroM (TSyntax `term) :=
  match codecs.toList.reverse with
  | [] => `(Lanes.Codec.unit)
  | last :: rest => rest.foldlM (fun acc c => `(Lanes.Codec.pair $c $acc)) last

/-- The `k`th of `n` alternatives as nested `Sum.inl`/`Sum.inr` around `x`. -/
meta def inject (k n : Nat) (x : TSyntax `term) : MacroM (TSyntax `term) := do
  let inner ← if k + 1 == n then pure x else `(Sum.inl $x)
  (List.range k).foldlM (fun acc _ => `(Sum.inr $acc)) inner

/-- The `k`th alternative of nested sums that end in `Empty`, as `Schema.Ctors` takes them. -/
meta def injectCtor (k : Nat) (x : TSyntax `term) : MacroM (TSyntax `term) := do
  (List.range k).foldlM (fun acc _ => `(Sum.inr $acc)) (← `(Sum.inl $x))

/-- A name as a string literal, as Lean writes it in a declaration but without `«»`. -/
meta def nameLit (x : Ident) : TSyntax `term :=
  ⟨Syntax.mkStrLit (x.getId.eraseMacroScopes.toString (escape := false))⟩

/-- The full name of the type `T`, resolved where the term is elaborated. -/
meta def typeName (T : Ident) : MacroM (TSyntax `term) := do
  let quoted : TSyntax `term :=
    ⟨mkNode `Lean.Parser.Term.doubleQuotedName #[mkAtom "`", mkAtom "`", T]⟩
  `(Lean.Name.toString $quoted)

/-- `Schema.Fields.cons` for each field, then `Schema.Fields.nil`. -/
meta def fieldsTerm (fields : Array FieldSpec) : MacroM (TSyntax `term) := do
  fields.foldrM (init := ← `(Lanes.Schema.Fields.nil)) fun (name, codec, aliases, default) acc => do
    let aliases := aliases.map nameLit
    let default ← match default with
      | some d => `(some $d)
      | none => `(none)
    `(Lanes.Schema.Fields.cons $(nameLit name) [$aliases,*] (Lanes.Codec.toOf $codec) $default
        $acc)

/-- The codec of structure `T`, whose type parameters have the types `args`. -/
meta def structTerm (T : Ident) (args : Array (TSyntax `term)) (fields : Array FieldSpec) :
    MacroM (TSyntax `term) := do
  let names := fields.map (·.1)
  let r := mkIdent (← Macro.addMacroScope `r)
  let projections ← names.mapM fun f => `($r.$f:ident)
  let values ← fresh names
  let bytes ← `(Lanes.Codec.map $(← product (fields.map (·.2.1))) (fun $r => $(← tuple projections))
      (fun $(← tuple values) => some { $[$names:ident := $values],* }) (by intro r; rfl))
  `(Lanes.Codec.withSchema $bytes
      (Lanes.Schema.Of.map
        (Lanes.Schema.Of.record $(← typeName T) [$args,*] $(← fieldsTerm fields))
        (fun $r => $(← fieldTuple projections))
        (fun $(← fieldTuple values) => some { $[$names:ident := $values],* }) (by intro r; rfl)))

/-- The records of inductive type `T`: nested sums of the constructors' products. -/
meta def sumBytes (T : Ident) (ctors : Array CtorSpec) : MacroM (TSyntax `term) := do
  let n := ctors.size
  let products ← ctors.mapM fun (_, _, fields) => product (fields.map (·.2.1))
  let sum ← match products.toList.reverse with
    | [] => `(Lanes.Codec.unit)
    | last :: rest => rest.foldlM (fun acc c => `(Lanes.Codec.sum $c $acc)) last
  let mut cases : Array (TSyntax `term) := #[]
  let mut backs : Array (TSyntax `term) := #[]
  for h : k in [0:n] do
    let (ctor, _, fields) := ctors[k]
    let ctor := mkIdent (T.getId ++ ctor.getId)
    let vars ← fresh (fields.map (·.1))
    let injected ← inject k n (← tuple vars)
    cases := cases.push (← if vars.isEmpty then pure injected else `(fun $vars* => $injected))
    backs := backs.push (← `(fun $(← tuple vars) => some ($ctor $vars*)))
  let back ← match backs.toList.reverse with
    | [] => `(fun _ => none)
    | last :: rest => rest.foldlM (fun acc f => `(Sum.elim $f $acc)) last
  let casesOn := mkIdent (T.getId ++ `casesOn)
  `(Lanes.Codec.map $sum (fun x => $casesOn:ident (motive := fun _ => _) x $cases*) $back
      (by intro x; cases x <;> rfl))

/-- The codec of inductive type `T`, whose type parameters have the types `args`. -/
meta def sumTerm (T : Ident) (args : Array (TSyntax `term)) (ctors : Array CtorSpec) :
    MacroM (TSyntax `term) := do
  if ctors.isEmpty then Macro.throwError "Codec.sum% needs at least one constructor"
  let mut cases : Array (TSyntax `term) := #[]
  let mut backs : Array (TSyntax `term) := #[]
  for h : k in [0:ctors.size] do
    let (ctor, _, fields) := ctors[k]
    let ctor := mkIdent (T.getId ++ ctor.getId)
    let vars ← fresh (fields.map (·.1))
    let injected ← injectCtor k (← fieldTuple vars)
    cases := cases.push (← if vars.isEmpty then pure injected else `(fun $vars* => $injected))
    backs := backs.push (← `(fun $(← fieldTuple vars) => some ($ctor $vars*)))
  let back ← backs.foldrM (fun f acc => `(Sum.elim $f $acc)) (← `(fun e => nomatch e))
  let schemas ← ctors.foldrM (init := ← `(Lanes.Schema.Ctors.nil))
    fun (ctor, aliases, fields) acc => do
      `(Lanes.Schema.Ctors.cons $(nameLit ctor) [$(aliases.map nameLit),*] $(← fieldsTerm fields)
          $acc)
  let casesOn := mkIdent (T.getId ++ `casesOn)
  `(Lanes.Codec.withSchema $(← sumBytes T ctors)
      (Lanes.Schema.Of.map (Lanes.Schema.Of.variants $(← typeName T) [$args,*] $schemas)
        (fun x => $casesOn:ident (motive := fun _ => _) x $cases*) $back
        (by intro x; cases x <;> rfl)))

end Codec

open Lean Codec in
macro_rules
  | `(Codec.struct% $T { $[$fields := $codecs],* }) =>
    structTerm T #[] (fields.zip codecs |>.map fun (f, c) => (f, c, #[], none))

open Lean Codec in
macro_rules
  | `(Codec.sum% $T { $[$ctors $[($args := $codecs)]*],* }) =>
    sumTerm T #[] ((ctors.zip (args.zip codecs)).map fun (ctor, args, codecs) =>
      (ctor, #[], (args.zip codecs).map fun (a, c) => (a, c, #[], none)))

end Lanes
