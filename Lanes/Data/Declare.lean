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
in the `deriving` clause goes to Lean.

A deriving handler needs `Lean.Elab`, which an application must not link, and a macro sees only
syntax: so the declaration is written inside the command, which reads the fields from it.
-/

@[expose] public section

namespace Lanes

/-- A type written as another that holds the same values: listed by listing the other. -/
@[instance_reducible] def Enum.ofEquiv {α β : Type} [Enum α] (f : α → β) (g : β → α)
    (h : ∀ b, f (g b) = b) : Enum β where
  all := (Enum.all (α := α)).map f
  complete b := h b ▸ List.mem_map_of_mem (Enum.complete (g b))

syntax lanesDataField := ppLine (docComment)? ident " : " term (" := " term)?
syntax lanesDataArgs := " (" ident+ " : " term ")"
syntax lanesDataCtor := ppLine (docComment)? "| " rawIdent lanesDataArgs*
syntax lanesDataDeriving := ppLine "deriving " ident,+

syntax (name := lanesDataStructure) (docComment)? "lanes_data " "structure " ident
  bracketedBinder* " where" manyIndent(lanesDataField) (lanesDataDeriving)? : command

syntax (name := lanesDataInductive) (docComment)? "lanes_data " "inductive " ident
  bracketedBinder* " where" lanesDataCtor* (lanesDataDeriving)? : command

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

/-- `T.codec`, taking a codec for each type parameter, and the `Codable` instance from it. -/
meta def codable (T : Ident) (p : Params) (body : TSyntax `term) :
    MacroM (Array (TSyntax `command)) := do
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

meta def enum (p : Params) (applied : TSyntax `term) (code : TSyntax `term)
    (to back : TSyntax `term) : MacroM (TSyntax `command) := do
  let instBinders := p.binders ++ (← classBinders ``Lanes.Enum p.types)
  `(instance $instBinders:bracketedBinder* : Lanes.Enum $applied :=
      Lanes.Enum.ofEquiv (α := $code) $back $to (by intro x; cases x <;> rfl))

end Declare

open Lean Declare in
macro_rules
  | `(lanesDataStructure|
      $[$doc:docComment]? lanes_data structure $T $bs:bracketedBinder* where
        $[$[$fdocs:docComment]? $fields : $types $[:= $defaults]?]* $[deriving $classes,*]?) => do
    let p ← params bs
    let (lean, ours) := splitDeriving (classes.map (·.getElems) |>.getD #[])
    independent ours fields types
    let pargs := p.args
    let applied ← `($T $pargs*)
    let decl ← `(command| $[$doc:docComment]? structure $T:ident $bs:bracketedBinder* where
      $[$[$fdocs:docComment]? $fields:ident : $types $[:= $defaults]?]*)
    let mut cmds := #[decl] ++ (← leanDeriving T lean)
    if ours.contains `Codable then
      let codecs ← types.mapM fun t => `((Lanes.Codable.codec : Lanes.Codec $t))
      cmds := cmds ++ (← codable T p (← `(Codec.struct% $T { $[$fields := $codecs],* })))
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
        $[$[$cdocs:docComment]? | $ctors $[($argss* : $tyss)]*]* $[deriving $classes,*]?) => do
    let p ← params bs
    let (lean, ours) := splitDeriving (classes.map (·.getElems) |>.getD #[])
    let pargs := p.args
    let applied ← `($T $pargs*)
    let binders ← (argss.zip tyss).mapM fun (xs, ts) =>
      (xs.zip ts).mapM fun (x, t) => `(bracketedBinder| ($x* : $t))
    let decl ← `(command| $[$doc:docComment]? inductive $T $bs:bracketedBinder* where
      $[$[$cdocs:docComment]? | $ctors:ident $binders*]*)
    let mut cmds := #[decl] ++ (← leanDeriving T lean)
    let args : Array (Array Ident) := (argss.zip tyss).map fun (xs, ts) =>
      (xs.zip ts).foldl (init := #[]) fun acc (ys, _) => acc ++ ys
    let argTypes : Array (Array (TSyntax `term)) := (argss.zip tyss).map fun (xs, ts) =>
      (xs.zip ts).foldl (init := #[]) fun acc (ys, t) => acc ++ ys.map fun _ => t
    for (xs, ts) in args.zip argTypes do independent ours xs ts
    if ours.contains `Codable then
      let codecs ← argTypes.mapM (·.mapM fun t => `((Lanes.Codable.codec : Lanes.Codec $t)))
      cmds := cmds ++
        (← codable T p (← `(Codec.sum% $T { $[$ctors $[($args := $codecs)]*],* })))
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
