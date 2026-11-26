/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std
public import Std.Data.String.ToNat

/-!
A `Codec` writes a value as a run of records and reads it back, with the law that reading what
was written gives the value and leaves what followed. The law is a field, so a codec without it
cannot be built, and codecs for pairs, sums, lists and mapped types keep it by construction.

Records are whole byte strings. Where one ends and the next begins is not a codec's concern:
`Lanes.Frame` settles that, with its own proofs.
-/

@[expose] public section

namespace Lanes

structure Codec (α : Type) where
  write : α → List ByteArray
  read : List ByteArray → Option (α × List ByteArray)
  sound : ∀ a rest, read (write a ++ rest) = some (a, rest)

namespace Codec

variable {α β : Type}

theorem fromUTF8?_toUTF8 (s : String) : String.fromUTF8? s.toUTF8 = some s := by
  simp [String.fromUTF8?, String.fromUTF8, s.isValidUTF8]

def bytes : Codec ByteArray where
  write b := [b]
  read
    | b :: rest => some (b, rest)
    | [] => none
  sound _ _ := rfl

def unit : Codec Unit where
  write _ := []
  read rest := some ((), rest)
  sound _ _ := rfl

def string : Codec String where
  write s := [s.toUTF8]
  read
    | b :: rest => (String.fromUTF8? b).map (·, rest)
    | [] => none
  sound s rest := by
    show (String.fromUTF8? s.toUTF8).map (·, rest) = _
    rw [fromUTF8?_toUTF8]
    rfl

def nat : Codec Nat where
  write n := [(toString n).toUTF8]
  read
    | b :: rest => ((String.fromUTF8? b).bind String.toNat?).map (·, rest)
    | [] => none
  sound n rest := by
    show ((String.fromUTF8? (toString n).toUTF8).bind String.toNat?).map (·, rest) = _
    rw [fromUTF8?_toUTF8]
    simp

/-- One after the other. -/
def pair (a : Codec α) (b : Codec β) : Codec (α × β) where
  write x := a.write x.1 ++ b.write x.2
  read records := do
    let (x, rest) ← a.read records
    let (y, rest) ← b.read rest
    return ((x, y), rest)
  sound x rest := by simp [List.append_assoc, a.sound, b.sound]

/-- A type written as another. `back` may refuse what `to` never produces. -/
def map (c : Codec β) (to : α → β) (back : β → Option α) (h : ∀ a, back (to a) = some a) :
    Codec α where
  write a := c.write (to a)
  read records := do
    let (b, rest) ← c.read records
    let a ← back b
    return (a, rest)
  sound a rest := by simp [c.sound, h]

/-- A pair whose second part's type, and so its codec, depends on the first. -/
def sigma {ι : Type} {β : ι → Type} (a : Codec ι) (b : ∀ i, Codec (β i)) :
    Codec ((i : ι) × β i) where
  write x := a.write x.1 ++ (b x.1).write x.2
  read records := do
    let (i, rest) ← a.read records
    let (v, rest) ← (b i).read rest
    return (⟨i, v⟩, rest)
  sound x rest := by simp [List.append_assoc, a.sound, (b x.1).sound]

/-- Written as the value; read back only with the property. -/
def subtype {p : α → Prop} [DecidablePred p] (c : Codec α) : Codec {a // p a} :=
  c.map (·.val) (fun a => if h : p a then some ⟨a, h⟩ else none) fun a => by simp [a.property]

def bool : Codec Bool :=
  nat.map (fun b => if b then 1 else 0)
    (fun n => if n = 0 then some false else if n = 1 then some true else none)
    (by intro b; cases b <;> rfl)

def fin {n : Nat} : Codec (Fin n) :=
  nat.map (·.val) (fun k => if h : k < n then some ⟨k, h⟩ else none) (by intro a; simp)

def int : Codec Int :=
  (pair bool nat).map (fun i => (decide (i < 0), i.natAbs))
    (fun (negative, size) => some (if negative then -(size : Int) else size))
    (by intro i; by_cases h : i < 0 <;> simp [h] <;> omega)

/-- A tag, then the value. -/
def sum (a : Codec α) (b : Codec β) : Codec (α ⊕ β) where
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

def option (c : Codec α) : Codec (Option α) :=
  (sum unit c).map (fun | none => .inl () | some a => .inr a)
    (fun | .inl () => some none | .inr a => some (some a)) (by intro a; cases a <;> rfl)

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

/-- How many, then each. -/
def list (c : Codec α) : Codec (List α) where
  write as := nat.write as.length ++ as.flatMap c.write
  read records := do
    let (n, rest) ← nat.read records
    readMany c n rest
  sound as rest := by simp [List.append_assoc, nat.sound, readMany_write]

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
  (list (pair key value)).map (·.toList) (fun entries => some (.ofList entries cmp))
    (fun t => congrArg some (extTreeMap_ofList_toList t))

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

/-- Variables for the values of `xs`, named apart from every constant: a value bound to a name
that is also a constructor's would be read as the constructor in a pattern. -/
meta def fresh (xs : Array Ident) : MacroM (Array (TSyntax `term)) :=
  xs.mapM fun x => return mkIdent (← Macro.addMacroScope x.getId)

/-- `(a, b, c)` as nested pairs, as a term or a pattern; `()` when empty. -/
meta def tuple (xs : Array (TSyntax `term)) : MacroM (TSyntax `term) :=
  match xs.toList.reverse with
  | [] => `(())
  | last :: rest => rest.foldlM (fun acc x => `(($x, $acc))) last

meta def product (codecs : Array (TSyntax `term)) : MacroM (TSyntax `term) :=
  match codecs.toList.reverse with
  | [] => `(Lanes.Codec.unit)
  | last :: rest => rest.foldlM (fun acc c => `(Lanes.Codec.pair $c $acc)) last

/-- The `k`th of `n` alternatives as nested `Sum.inl`/`Sum.inr` around `x`. -/
meta def inject (k n : Nat) (x : TSyntax `term) : MacroM (TSyntax `term) := do
  let inner ← if k + 1 == n then pure x else `(Sum.inl $x)
  (List.range k).foldlM (fun acc _ => `(Sum.inr $acc)) inner

end Codec

open Lean Codec in
macro_rules
  | `(Codec.struct% $_ { $[$fields := $codecs],* }) => do
    let r := mkIdent (← Macro.addMacroScope `r)
    let projections ← fields.mapM fun f => `($r.$f:ident)
    let out ← tuple projections
    let values ← fresh fields
    let pattern ← tuple values
    `(Lanes.Codec.map $(← product codecs) (fun $r => $out)
        (fun $pattern => some { $[$fields:ident := $values],* }) (by intro r; rfl))

open Lean Codec in
macro_rules
  | `(Codec.sum% $T { $[$ctors $[($args := $codecs)]*],* }) => do
    let n := ctors.size
    if n == 0 then Macro.throwError "Codec.sum% needs at least one constructor"
    let products ← codecs.mapM product
    let sum ← match products.toList.reverse with
      | [] => `(Lanes.Codec.unit)
      | last :: rest => rest.foldlM (fun acc c => `(Lanes.Codec.sum $c $acc)) last
    let mut cases : Array (TSyntax `term) := #[]
    let mut backs : Array (TSyntax `term) := #[]
    for k in [0:n] do
      let ctor := mkIdent (T.getId ++ ctors[k]!.getId)
      let vars ← fresh args[k]!
      let injected ← inject k n (← tuple vars)
      cases := cases.push (← if vars.isEmpty then pure injected
        else `(fun $vars* => $injected))
      backs := backs.push (← `(fun $(← tuple vars) => some ($ctor $vars*)))
    let back ← match backs.toList.reverse with
      | [] => `(fun _ => none)
      | last :: rest => rest.foldlM (fun acc f => `(Sum.elim $f $acc)) last
    let casesOn := mkIdent (T.getId ++ `casesOn)
    `(Lanes.Codec.map $sum
        (fun x => $casesOn:ident (motive := fun _ => _) x $cases*)
        $back (by intro x; cases x <;> rfl))

end Lanes
