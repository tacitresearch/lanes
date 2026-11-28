/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Data.Codec
public import Lanes.Data.Enum

/-!
`lanes_data structure …` and `lanes_data inductive …` declare a type and derive from the same
text what Lean's own deriving handlers cannot give an application that imports only `Std`:
`Codable` (a codec, by `Codec.struct%` or `Codec.sum%`), `Enum`, and `LawfulBEq` (a `BEq` field
by field, with its law, for a structure holding a function on an `Enum` type). Every other class
in the `deriving` clause goes to Lean. A clause `from Old := f` after it says how a value of the
type's previous version becomes one of this (`T.migrate`, an instance of `Migrate`).

A deriving handler needs `Lean.Elab`, which an application must not link, and a macro sees only
syntax: so the declaration is written inside the command, which reads the fields from it.
-/

@[expose] public section

namespace Lanes

/-- How a value of an older version of a type becomes a value of this one. A migration of a
system (`Lanes.Migration`) takes its states and messages through it; `lanes_data` declares one
with `from Old := f`. -/
class Migrate (α β : Type) where
  migrate : α → β

/-- A type that did not change migrates to itself. -/
instance Migrate.same {α : Type} : Migrate α α := ⟨id⟩

theorem Migrate.migrate_same {α : Type} (a : α) : Migrate.migrate (β := α) a = a := rfl

/-- A type written as another that holds the same values: listed by listing the other. -/
@[instance_reducible] def Enum.ofEquiv {α β : Type} [Enum α] (f : α → β) (g : β → α)
    (h : ∀ b, f (g b) = b) : Enum β where
  all := (Enum.all (α := α)).map f
  complete b := h b ▸ List.mem_map_of_mem (Enum.complete (g b))

/-- `(was a b)` after a field, an argument or a constructor: its former names, which a reader of
data written under one of them takes for it. `was` stays an ordinary identifier elsewhere. -/
syntax lanesDataWas := atomic(" (" &"was " rawIdent+ ")")
syntax lanesDataField :=
  ppLine (docComment)? ident (lanesDataWas)? " : " term (" := " term)?
syntax lanesDataArg := ident (lanesDataWas)?
syntax lanesDataArgs := " (" lanesDataArg+ " : " term (" := " term)? ")"
syntax lanesDataCtor := ppLine (docComment)? "| " rawIdent (lanesDataWas)? lanesDataArgs*
syntax lanesDataDeriving := ppLine "deriving " ident,+
syntax lanesDataFrom := ppLine "from " term " := " term

syntax (name := lanesDataStructure) (docComment)? "lanes_data " "structure " ident
  bracketedBinder* " where" manyIndent(lanesDataField) (lanesDataDeriving)? (lanesDataFrom)? :
  command

syntax (name := lanesDataInductive) (docComment)? "lanes_data " "inductive " ident
  bracketedBinder* " where" lanesDataCtor* (lanesDataDeriving)? (lanesDataFrom)? : command

namespace Declare

open Lean

/-- The parameters of a declared type: binders for an instance, the arguments to apply it to,
and those that are types. -/
structure Params where
  binders : Array (TSyntax `Lean.Parser.Term.bracketedBinder) := #[]
  args : Array Ident := #[]
  types : Array Ident := #[]

meta def params (bs : Array (TSyntax `Lean.Parser.Term.bracketedBinder)) : MacroM Params :=
  bs.foldlM (init := {}) fun p b => do
    match b with
    | `(bracketedBinder| ($xs:ident* : Type)) =>
      return { p with binders := p.binders.push (← `(bracketedBinder| {$xs* : Type})),
                      args := p.args ++ xs, types := p.types ++ xs }
    | `(bracketedBinder| ($xs:ident* : $t)) =>
      return { p with binders := p.binders.push (← `(bracketedBinder| {$xs* : $t})),
                      args := p.args ++ xs }
    | _ => return { p with binders := p.binders.push ⟨b⟩ }

meta def classBinders (cls : Name) (xs : Array Ident) :
    MacroM (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) :=
  xs.mapM fun x => `(bracketedBinder| [$(mkIdent cls) $x])

meta def productType (ts : Array (TSyntax `term)) : MacroM (TSyntax `term) :=
  match ts.toList.reverse with
  | [] => `(Unit)
  | last :: rest => rest.foldlM (fun acc t => `($t × $acc)) last

meta def sumType (ts : Array (TSyntax `term)) : MacroM (TSyntax `term) :=
  match ts.toList.reverse with
  | [] => `(Empty)
  | last :: rest => rest.foldlM (fun acc t => `($t ⊕ $acc)) last

meta def splitDeriving (classes : Array Ident) : Array Ident × Array Name :=
  classes.foldl (init := (#[], #[])) fun (lean, ours) c =>
    if [`Codable, `Enum, `LawfulBEq].contains c.getId then (lean, ours.push c.getId)
    else (lean.push c, ours)

meta def leanDeriving (T : Ident) (classes : Array Ident) : MacroM (Array (TSyntax `command)) :=
  if classes.isEmpty then pure #[] else do
    let classes : Array (TSyntax `Lean.Parser.Command.derivingClass) := classes.map fun c =>
      ⟨mkNode `Lean.Parser.Command.derivingClass #[mkNullNode, c]⟩
    return #[← `(deriving instance $[$classes],* for $T:ident)]

/-- `T.codec`, taking a codec for each type parameter, and the `Codable` instance from it.
`body` is given the types of the type parameters, which the codec's schema names. -/
meta def codable (T : Ident) (p : Params)
    (body : Array (TSyntax `term) → MacroM (TSyntax `term)) :
    MacroM (Array (TSyntax `command)) := do
  let body ← body (← p.types.mapM fun x => `((Lanes.Codec.of $x).schema.root))
  let codecs ← p.types.mapM fun x =>
    return mkIdent (← Macro.addMacroScope (x.getId.appendBefore "codec"))
  let codecBinders ← (p.types.zip codecs).mapM fun (x, c) =>
    `(bracketedBinder| ($c : Lanes.Codec $x))
  let args := p.args
  let applied ← `($T $args*)
  let name := mkIdentFrom T (T.getId ++ `codec)
  let body ← (p.types.zip codecs).foldrM (init := body) fun (x, c) acc =>
    `(letI : Lanes.Codable $x := ⟨$c⟩; $acc)
  let defaults := p.types.map fun _ => (mkIdent ``Lanes.Codable.codec : TSyntax `term)
  let instBinders ← classBinders ``Lanes.Codable p.types
  let defBinders := p.binders ++ codecBinders
  let instBinders := p.binders ++ instBinders
  return #[← `(def $name $defBinders:bracketedBinder* : Lanes.Codec $applied := $body),
    ← `(instance $instBinders:bracketedBinder* : Lanes.Codable $applied :=
        ⟨$name $defaults*⟩)]

meta def conjunction (cs : Array (TSyntax `term)) : MacroM (TSyntax `term) :=
  match cs.toList with
  | [] => `(true)
  | c :: cs => cs.foldlM (fun acc c => `($acc && $c)) c

meta def fieldwise (fields : Array Ident) (a b : Ident) : MacroM (TSyntax `term) := do
  conjunction (← fields.mapM fun f => `($a.$f:ident == $b.$f:ident))

/-- The type parameters that `fieldwise` needs only `BEq` of: each is the whole type of a field
and inside no other. The rest need `DecidableEq`, which is what derived types compare with. -/
meta def comparedByBEq (p : Params) (types : Array (TSyntax `term)) : Array Ident :=
  p.types.filter fun x =>
    types.any (fun t => t.raw.isIdent && t.raw.getId == x.getId)
      && !types.any fun t => !t.raw.isIdent && (t.raw.find? (·.getId == x.getId)).isSome

/-- What `lanes_data` derives takes each field by its type alone, so it refuses a field whose
type names an earlier one, such as a proof about it. -/
meta def independent (ours : Array Name) (names : Array Ident) (types : Array (TSyntax `term)) :
    MacroM Unit := do
  if ours.isEmpty then return
  for h : k in [0:types.size] do
    let named? := names.extract 0 k |>.find? fun n =>
      (types[k].raw.find? fun s =>
        s.isIdent && s.getId.eraseMacroScopes.getRoot == n.getId.eraseMacroScopes).isSome
    if let some named := named? then
      let classes := ", ".intercalate (ours.toList.map fun c => s!"`{c}`")
      Macro.throwErrorAt types[k] s!"lanes_data: this type names `{named.getId}`, and \
        {classes} takes each field by its type alone. Put the property in the type of \
        `{named.getId}` instead, as a subtype `\{x : α // p x}`, or both in a sigma type."

/-- `from Old := f`: `T.migrate`, how a value of the type's previous version becomes one of
this, and the `Migrate` instance from it. -/
meta def migrate (T : Ident) (p : Params) (applied : TSyntax `term)
    (previous : Option (TSyntax `term × TSyntax `term)) : MacroM (Array (TSyntax `command)) := do
  let some (old, f) := previous | return #[]
  let name := mkIdentFrom T (T.getId ++ `migrate)
  let binders := p.binders
  return #[← `(def $name $binders:bracketedBinder* : $old → $applied := $f),
    ← `(instance $binders:bracketedBinder* : Lanes.Migrate $old $applied := ⟨$name⟩)]

meta def enum (p : Params) (applied : TSyntax `term) (code : TSyntax `term)
    (to back : TSyntax `term) : MacroM (TSyntax `command) := do
  let instBinders := p.binders ++ (← classBinders ``Lanes.Enum p.types)
  `(instance $instBinders:bracketedBinder* : Lanes.Enum $applied :=
      Lanes.Enum.ofEquiv (α := $code) $back $to (by intro x; cases x <;> rfl))

/-- A schema holds a default as a value, so `Codable` refuses a default that names a field. -/
meta def constantDefaults (ours : Array Name) (names : Array Ident)
    (defaults : Array (Option (TSyntax `term))) : MacroM Unit := do
  unless ours.contains `Codable do return
  for d in defaults do
    let some d := d | continue
    let named? := names.find? fun n =>
      (d.raw.find? fun s =>
        s.isIdent && s.getId.eraseMacroScopes.getRoot == n.getId.eraseMacroScopes).isSome
    if let some named := named? then
      Macro.throwErrorAt d s!"lanes_data: this default names `{named.getId}`, and the schema \
        `Codable` derives holds a default as a value. Give one that names no field."

/-- A constructor's arguments, one by one: the name, its former names, the type and the
default. -/
meta def ctorArgs (groups : Array (TSyntax `Lanes.lanesDataArgs)) :
    MacroM (Array (Ident × Array Ident × TSyntax `term × Option (TSyntax `term))) :=
  groups.foldlM (init := #[]) fun acc g => do
    match g with
    | `(lanesDataArgs| ($[$xs $[(was $olds*)]?]* : $t $[:= $d]?)) =>
      return acc ++ (xs.zip olds).map fun (x, o) => (x, o.getD #[], t, d)
    | _ => Macro.throwUnsupported

/-- A group of arguments as a binder of `inductive`, without the former names. -/
meta def ctorBinder (g : TSyntax `Lanes.lanesDataArgs) :
    MacroM (TSyntax `Lean.Parser.Term.bracketedBinder) := do
  match g with
  | `(lanesDataArgs| ($[$xs $[(was $_olds*)]?]* : $t)) => `(bracketedBinder| ($xs* : $t))
  | `(lanesDataArgs| ($[$xs $[(was $_olds*)]?]* : $t := $d)) =>
    `(bracketedBinder| ($xs* : $t := $d))
  | _ => Macro.throwUnsupported

end Declare

open Lean Declare in
macro_rules
  | `(lanesDataStructure|
      $[$doc:docComment]? lanes_data structure $T $bs:bracketedBinder* where
        $[$[$fdocs:docComment]? $fields $[(was $folds*)]? : $types $[:= $defaults]?]*
        $[deriving $classes,*]? $[from $old := $f]?) => do
    let p ← params bs
    let (lean, ours) := splitDeriving (classes.map (·.getElems) |>.getD #[])
    independent ours fields types
    constantDefaults ours fields defaults
    let pargs := p.args
    let applied ← `($T $pargs*)
    let decl ← `(command| $[$doc:docComment]? structure $T:ident $bs:bracketedBinder* where
      $[$[$fdocs:docComment]? $fields:ident : $types $[:= $defaults]?]*)
    let mut cmds := #[decl] ++ (← leanDeriving T lean) ++ (← migrate T p applied ((old.bind fun o => f.map (o, ·))))
    if ours.contains `Codable then
      let specs ← (fields.zip (folds.zip (types.zip defaults))).mapM fun (x, olds, t, d) => do
        let d ← d.mapM fun d => `(($d : $t))
        return (x, ← `((Lanes.Codable.codec : Lanes.Codec $t)), olds.getD #[], d)
      cmds := cmds ++ (← codable T p fun args => Codec.structTerm T args specs)
    if ours.contains `Enum then
      let r := mkIdent (← Macro.addMacroScope `r)
      let projections ← fields.mapM fun f => `($r.$f:ident)
      let values ← Codec.fresh fields
      cmds := cmds.push (← enum p applied (← productType types)
        (← `(fun $r => $(← Codec.tuple projections)))
        (← `(fun $(← Codec.tuple values) => { $[$fields:ident := $values],* })))
    if ours.contains `LawfulBEq then
      let a := mkIdent (← Macro.addMacroScope `a)
      let b := mkIdent (← Macro.addMacroScope `b)
      let same ← fieldwise fields a b
      let sameSelf ← fieldwise fields a a
      let beqTypes := comparedByBEq p types
      let eqTypes := p.types.filter fun x => !beqTypes.contains x
      let ctx := p.binders ++ (← classBinders ``DecidableEq eqTypes)
        ++ (← classBinders ``BEq beqTypes)
      let lawCtx := ctx ++ (← classBinders ``LawfulBEq beqTypes)
      cmds := cmds ++ #[
        ← `(instance $ctx:bracketedBinder* : BEq $applied := ⟨fun $a $b => $same⟩),
        ← `(instance $lawCtx:bracketedBinder* : LawfulBEq $applied where
              rfl := by intro $a:ident; change $sameSelf = true; simp
              eq_of_beq := by
                intro $a:ident $b:ident h
                change $same = true at h
                cases $a:ident; cases $b:ident; simpa [and_assoc, Subtype.ext_iff] using h)]
    return mkNullNode (cmds.map (·.raw))

open Lean Declare in
macro_rules
  | `(lanesDataInductive|
      $[$doc:docComment]? lanes_data inductive $T $bs:bracketedBinder* where
        $[$[$cdocs:docComment]? | $ctors $[(was $colds*)]? $argss*]* $[deriving $classes,*]?
        $[from $old := $f]?) => do
    let p ← params bs
    let (lean, ours) := splitDeriving (classes.map (·.getElems) |>.getD #[])
    let pargs := p.args
    let applied ← `($T $pargs*)
    let binders ← argss.mapM (·.mapM ctorBinder)
    let decl ← `(command| $[$doc:docComment]? inductive $T $bs:bracketedBinder* where
      $[$[$cdocs:docComment]? | $ctors:ident $binders*]*)
    let mut cmds := #[decl] ++ (← leanDeriving T lean) ++ (← migrate T p applied ((old.bind fun o => f.map (o, ·))))
    let fieldss ← argss.mapM ctorArgs
    let args : Array (Array Ident) := fieldss.map (·.map (·.1))
    let argTypes : Array (Array (TSyntax `term)) := fieldss.map (·.map (·.2.2.1))
    for fields in fieldss do
      independent ours (fields.map (·.1)) (fields.map (·.2.2.1))
      constantDefaults ours (fields.map (·.1)) (fields.map (·.2.2.2))
    if ours.contains `Codable then
      let specs ← (ctors.zip (colds.zip fieldss)).mapM fun (ctor, olds, fields) => do
        let fields ← fields.mapM fun (x, xolds, t, d) => do
          let d ← d.mapM fun d => `(($d : $t))
          return (x, ← `((Lanes.Codable.codec : Lanes.Codec $t)), xolds, d)
        return (ctor, olds.getD #[], fields)
      cmds := cmds ++ (← codable T p fun args => Codec.sumTerm T args specs)
    if ours.contains `Enum then
      let n := ctors.size
      let mut cases : Array (TSyntax `term) := #[]
      let mut backs : Array (TSyntax `term) := #[]
      for k in [0:n] do
        let ctor := mkIdent (T.getId ++ ctors[k]!.getId)
        let vars ← Codec.fresh args[k]!
        let injected ← Codec.inject k n (← Codec.tuple vars)
        cases := cases.push (← if vars.isEmpty then pure injected
          else `(fun $vars* => $injected))
        backs := backs.push (← `(fun $(← Codec.tuple vars) => $ctor $vars*))
      let back ← match backs.toList.reverse with
        | [] => `(fun x => nomatch x)
        | last :: rest => rest.foldlM (fun acc f => `(Sum.elim $f $acc)) last
      let casesOn := mkIdent (T.getId ++ `casesOn)
      cmds := cmds.push (← enum p applied (← sumType (← argTypes.mapM productType))
        (← `(fun x => $casesOn:ident (motive := fun _ => _) x $cases*)) back)
    if ours.contains `LawfulBEq then
      Macro.throwError "lanes_data: `LawfulBEq` is derived for a structure only"
    return mkNullNode (cmds.map (·.raw))

end Lanes
