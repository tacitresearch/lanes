/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Data.Enum

/-!
`lanes_data structure …` and `lanes_data inductive …` declare a type and derive from the same
text what Lean's own deriving handlers cannot give an application that imports only `Std`:

- `ToJson` and `FromJson`, together, with `LawfulJson` and `NonNullJson`: a `Json.Codec` built
  from the pieces of `Lanes/Lib/Encoding/Fields.lean` and `Lanes/Lib/Encoding/Json/Derive.lean`,
  whose laws give the round trip;
- `ToCbor` and `FromCbor` in the same way, by the same code (`Declare.Format`), with the pieces of
  `Lanes/Lib/Encoding/Cbor/Derive.lean`: so a type's CBOR has the shape of its JSON;
- `Enum`;
- `LawfulBEq`: a `BEq` field by field, with its law, for a structure holding a function on an
  `Enum` type;
- a `TableOf`, for a structure, from a `table` line after `deriving`: the columns of
  `Lanes/Db/Columns.lean`, whose laws give the round trip.

Every other class in the `deriving` clause goes to Lean. The code a command writes names
`Lanes.Json`, `Lanes.Cbor` and `Lanes.Db`, which this file does not import: a file that derives
them imports them, as `import Lanes` does for JSON and rows. CBOR is imported on its own
(`import Lanes.Lib.Encoding.Cbor`).

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

syntax lanesDataField :=
  ppLine (docComment)? atomic(ident " : ") term (" := " term)?
syntax lanesDataArgs := " (" ident+ " : " term (" := " term)? ")"
syntax lanesDataCtor := ppLine (docComment)? "| " rawIdent lanesDataArgs*
syntax lanesDataDeriving := ppLine "deriving " ident,+
/-- A secondary index of a table, on some of its fields. -/
declare_syntax_cat lanesDataIndex (behavior := symbol)
/-- `index byOwner on owner, title`. -/
syntax ppLine &"index" ident (str)? &"on" ident,+ : lanesDataIndex
/-- `unique index byEmail on email`: no two rows have the same values in these fields. -/
syntax ppLine &"unique" &"index" ident (str)? &"on" ident,+ : lanesDataIndex
/-- `table todos key id`: the table `todos`, whose primary key is these fields. -/
syntax lanesDataTable := ppLine &"table" ident (str)? &"key" ident,+ lanesDataIndex*

syntax (name := lanesDataStructure) (docComment)? "lanes_data " "structure " ident
  bracketedBinder* " where" manyIndent(lanesDataField) (lanesDataDeriving)? (lanesDataTable)? :
  command

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

/-- Variables for the values of `xs`, named apart from every constant: a value bound to a name
that is also a constructor's would be read as the constructor in a pattern. -/
meta def fresh (xs : Array Ident) : MacroM (Array (TSyntax `term)) :=
  xs.mapM fun x => return mkIdent (← Macro.addMacroScope x.getId)

/-- `(a, b, c)` as nested pairs, as a term or a pattern; `()` when empty. -/
meta def tuple (xs : Array (TSyntax `term)) : MacroM (TSyntax `term) :=
  match xs.toList.reverse with
  | [] => `(())
  | last :: rest => rest.foldlM (fun acc x => `(($x, $acc))) last

/-- The parts of a nested pair `x` of `n` parts: `x.1`, `x.2.1`, …, `x.2.….2`. -/
meta def parts (x : TSyntax `term) : Nat → MacroM (Array (TSyntax `term))
  | 0 => pure #[]
  | 1 => pure #[x]
  | n + 2 => do return #[← `($x.1)] ++ (← parts (← `($x.2)) (n + 1))

/-- `f a (f b c)`, or `unit` when empty. -/
meta def nest (f : TSyntax `term → TSyntax `term → MacroM (TSyntax `term)) (unit : TSyntax `term)
    (xs : Array (TSyntax `term)) : MacroM (TSyntax `term) :=
  match xs.toList.reverse with
  | [] => pure unit
  | last :: rest => rest.foldlM (fun acc x => f x acc) last

meta def productType (ts : Array (TSyntax `term)) : MacroM (TSyntax `term) := do
  nest (fun t acc => `($t × $acc)) (← `(Unit)) ts

meta def sumType (ts : Array (TSyntax `term)) : MacroM (TSyntax `term) := do
  nest (fun t acc => `($t ⊕ $acc)) (← `(Empty)) ts

/-- The `k`th of `n` alternatives as nested `Sum.inl`/`Sum.inr` around `x`. -/
meta def inject (k n : Nat) (x : TSyntax `term) : MacroM (TSyntax `term) := do
  let inner ← if k + 1 == n then pure x else `(Sum.inl $x)
  (List.range k).foldlM (fun acc _ => `(Sum.inr $acc)) inner

meta def nameString (x : Ident) : String :=
  x.getId.eraseMacroScopes.toString (escape := false)

/-- `createdAt` as `created_at`: the name PostgreSQL takes as it is. -/
meta def snake (s : String) : String :=
  String.ofList <| s.toList.foldr (init := []) fun c acc =>
    if c.isUpper then '_' :: c.toLower :: acc else c :: acc

meta def splitDeriving (classes : Array Ident) : MacroM (Array Ident × Array Name) :=
  classes.foldlM (init := (#[], #[])) fun (lean, ours) c => do
    match c.getId with
    | `TableOf => Macro.throwErrorAt c "lanes_data: a table is declared by a line after \
        `deriving`: `table todos key id`, then `index byOwner on owner` lines"
    | n =>
      if [`ToJson, `FromJson, `ToCbor, `FromCbor, `Enum, `LawfulBEq].contains n then
        return (lean, ours.push n)
      else return (lean.push c, ours)

meta def leanDeriving (T : Ident) (classes : Array Ident) : MacroM (Array (TSyntax `command)) :=
  if classes.isEmpty then pure #[] else do
    let classes : Array (TSyntax `Lean.Parser.Command.derivingClass) := classes.map fun c =>
      ⟨mkNode `Lean.Parser.Command.derivingClass #[mkNullNode, c]⟩
    return #[← `(deriving instance $[$classes],* for $T:ident)]

/-- A format `lanes_data` derives an encoding to, with its laws: JSON or CBOR. Each has a
`Codec` whose four fields are the two functions and the two laws, in that order, `Fields.field`,
`Codec.object`, `Alts.ctor` and `Codec.ofAlts` in its namespace, and four classes; the rest of
the pieces are `Lanes.Fields` and `Lanes.Alts`, which both share. -/
structure Format where
  name : String
  ns : Name
  toClass : Name
  fromClass : Name
  lawful : Name
  nonNull : Name
  codec : Name

meta def Format.json : Format :=
  { name := "JSON", ns := `Lanes.Json, toClass := `ToJson, fromClass := `FromJson,
    lawful := `LawfulJson, nonNull := `NonNullJson, codec := `jsonCodec }

meta def Format.cbor : Format :=
  { name := "CBOR", ns := `Lanes.Cbor, toClass := `ToCbor, fromClass := `FromCbor,
    lawful := `LawfulCbor, nonNull := `NonNullCbor, codec := `cborCodec }

meta def Format.all : List Format := [.json, .cbor]

/-- Whether to derive a format: both its classes, or neither. -/
meta def wants (ours : Array Name) (f : Format) : MacroM Bool := do
  match ours.contains f.toClass, ours.contains f.fromClass with
  | true, true => return true
  | false, false => return false
  | _, _ => Macro.throwError s!"lanes_data: `{f.toClass}` and `{f.fromClass}` are derived \
      together, with the law that one reads back what the other writes"

meta def strings (xs : Array String) : MacroM (TSyntax `term) := do
  let lits := xs.map Syntax.mkStrLit
  `(([$[$lits],*] : List String))

/-- That the names are distinct, by `decide` on the list, which holds no variable. -/
meta def distinct (xs : Array String) : MacroM (TSyntax `term) := do
  `((show List.Nodup $(← strings xs) by decide))

/-- That no name of `xs` is one of `ys`. -/
meta def apart (xs ys : Array String) : MacroM (TSyntax `term) := do
  `((show (List.all $(← strings xs) fun t => !List.contains $(← strings ys) t) = true by decide))

set_option hygiene false in
/-- An object of the fields `(name, type)`, as the format's `Fields`. -/
meta def fieldsOf (f : Format) (fields : Array (Ident × TSyntax `term)) :
    MacroM (TSyntax `term) := do
  let field := mkIdent (f.ns ++ `Fields.field)
  let each ← fields.mapM fun (x, t) =>
    `(($field $(Syntax.mkStrLit (nameString x)) (β := $t)))
  nest (fun f acc => `(Lanes.Fields.pair $f $acc)) (← `(Lanes.Fields.unit)) each

set_option hygiene false in
/-- `T.jsonCodec` or `T.cborCodec`, and the instances made from it. A type parameter needs the
format's classes, and its `NonNull` class if a field's type mentions `Option`. -/
meta def instances (f : Format) (T : Ident) (p : Params) (types : Array (TSyntax `term))
    (codec : TSyntax `term) : MacroM (Array (TSyntax `command)) := do
  let pargs := p.args
  let applied ← `($T $pargs*)
  let name := mkIdentFrom T (T.getId ++ f.codec)
  let cls (n : Name) := mkIdent (`Lanes ++ n)
  let mentions (x : Ident) (t : TSyntax `term) : Bool :=
    (t.raw.find? (·.getId == x.getId)).isSome
  let optional := p.types.filter fun x =>
    types.any fun t => mentions x t && (t.raw.find? (·.getId == `Option)).isSome
  let ctx := p.binders ++ (← classBinders (`Lanes ++ f.toClass) p.types)
    ++ (← classBinders (`Lanes ++ f.fromClass) p.types) ++ (← p.types.mapM fun x =>
      `(bracketedBinder| [$(cls f.lawful) $x]))
    ++ (← optional.mapM fun x => `(bracketedBinder| [$(cls f.nonNull) $x]))
  let codecType := mkIdent (f.ns ++ `Codec)
  return #[← `(def $name $ctx:bracketedBinder* : $codecType $applied := $codec),
    ← `(instance $ctx:bracketedBinder* : $(cls f.toClass) $applied := ⟨($name).1⟩),
    ← `(instance $ctx:bracketedBinder* : $(cls f.fromClass) $applied := ⟨($name).2⟩),
    ← `(instance $ctx:bracketedBinder* : $(cls f.lawful) $applied := ⟨($name).3⟩),
    ← `(instance $ctx:bracketedBinder* : $(cls f.nonNull) $applied := ⟨($name).4⟩)]

set_option hygiene false in
meta def structCodec (f : Format) (fields : Array (Ident × TSyntax `term)) :
    MacroM (TSyntax `term) := do
  let names := fields.map (·.1)
  let r := mkIdent (← Macro.addMacroScope `r)
  let x := mkIdent (← Macro.addMacroScope `x)
  let projections ← names.mapM fun f => `($r.$f:ident)
  let values ← parts x names.size
  `($(mkIdent (f.ns ++ `Codec.object))
      (Lanes.Fields.map $(← fieldsOf f fields) (fun $r => $(← tuple projections))
        (fun $x => { $[$names:ident := $values],* }) (fun _ => rfl))
      $(← distinct (names.map nameString)))

set_option hygiene false in
meta def sumCodec (f : Format) (T : Ident) (ctors : Array Ident)
    (fieldss : Array (Array (Ident × TSyntax `term))) : MacroM (TSyntax `term) := do
  let n := ctors.size
  if n == 0 then Macro.throwError s!"lanes_data: {f.name} needs at least one constructor"
  let alts ← (ctors.zip fieldss).mapM fun (ctor, fields) => do
    `($(mkIdent (f.ns ++ `Alts.ctor)) $(Syntax.mkStrLit (nameString ctor)) $(← fieldsOf f fields)
        $(← distinct (fields.map (nameString ·.1))))
  let tags := ctors.map nameString
  let mut sum := alts[n - 1]!
  for k in (List.range (n - 1)).reverse do
    sum ← `(Lanes.Alts.sum $(alts[k]!) $sum $(← apart #[tags[k]!] (tags.extract (k + 1) n)))
  let mut cases : Array (TSyntax `term) := #[]
  let mut backs : Array (TSyntax `term) := #[]
  let t := mkIdent (← Macro.addMacroScope `t)
  for k in [0:n] do
    let ctor := mkIdent (T.getId ++ ctors[k]!.getId)
    let vars ← fresh (fieldss[k]!.map (·.1))
    let injected ← inject k n (← tuple vars)
    cases := cases.push (← if vars.isEmpty then pure injected else `(fun $vars* => $injected))
    let values ← parts t vars.size
    backs := backs.push (← `(fun $t => $ctor $values*))
  let back ← nest (fun f acc => `(Sum.elim $f $acc)) (← `(fun x => nomatch x)) backs
  let casesOn := mkIdent (T.getId ++ `casesOn)
  `($(mkIdent (f.ns ++ `Codec.ofAlts))
      (Lanes.Alts.map $sum (fun x => $casesOn:ident (motive := fun _ => _) x $cases*) $back
        (by intro x; cases x <;> rfl)))

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

/-- A constructor's arguments, one by one: the name and the type. -/
meta def ctorArgs (groups : Array (TSyntax `Lanes.lanesDataArgs)) :
    MacroM (Array (Ident × TSyntax `term)) :=
  groups.foldlM (init := #[]) fun acc g => do
    match g with
    | `(lanesDataArgs| ($xs* : $t $[:= $_d]?)) => return acc ++ xs.map fun x => (x, t)
    | _ => Macro.throwUnsupported

/-- A group of arguments as a binder of `inductive`. -/
meta def ctorBinder (g : TSyntax `Lanes.lanesDataArgs) :
    MacroM (TSyntax `Lean.Parser.Term.bracketedBinder) := do
  match g with
  | `(lanesDataArgs| ($xs* : $t)) => `(bracketedBinder| ($xs* : $t))
  | `(lanesDataArgs| ($xs* : $t := $d)) => `(bracketedBinder| ($xs* : $t := $d))
  | _ => Macro.throwUnsupported

/-- The position of field `x` among the columns. -/
meta def position (columns : Array Ident) (x : Ident) : MacroM Nat :=
  match columns.findIdx? (·.getId == x.getId) with
  | some k => pure k
  | none => Macro.throwErrorAt x s!"lanes_data: the structure has no field `{x.getId}`"

set_option hygiene false in
/-- The table a `table` line declares, and its indexes, each `table.index`. The columns are
the key's fields, then the others in their order. A name in PostgreSQL is the Lean name in
`snake_case`, and an index's starts with its table's, since PostgreSQL names indexes per schema;
a string after the Lean name gives another. -/
meta def table (T : Ident) (p : Params) (fields : Array (Ident × TSyntax `term))
    (clause : TSyntax `Lanes.lanesDataTable) : MacroM (Array (TSyntax `command)) := do
  let `(lanesDataTable| table $name $[$sql]? key $keys,* $indexes*) := clause
    | Macro.throwUnsupported
  unless p.args.isEmpty do
    Macro.throwErrorAt clause "lanes_data: a table's type has no parameters"
  let keys := keys.getElems
  for k in keys do discard <| position (fields.map (·.1)) k
  let others := fields.filter fun (x, _) => !keys.any (·.getId == x.getId)
  let columns := keys.filterMap (fun k => fields.find? (·.1.getId == k.getId)) ++ others
  let names := columns.map (·.1)
  let sqlName := sql.map (·.getString) |>.getD (snake (nameString name))
  let mut cmds := #[]
  let mut idents := #[]
  for i in indexes do
    let (u, idx, isql, on) ← match i with
      | `(lanesDataIndex| index $idx $[$isql]? on $on,*) => pure (false, idx, isql, on)
      | `(lanesDataIndex| unique index $idx $[$isql]? on $on,*) => pure (true, idx, isql, on)
      | _ => Macro.throwUnsupported
    let positions ← on.getElems.mapM fun x => return Syntax.mkNumLit (toString (← position names x))
    let ident := mkIdentFrom idx (name.getId ++ idx.getId)
    let isql := isql.map (·.getString) |>.getD (sqlName ++ "_" ++ snake (nameString idx))
    let unique ← if u then `(true) else `(false)
    cmds := cmds.push (← `(def $ident : Lanes.Db.Index :=
      { name := $(Syntax.mkStrLit isql), columns := [$[$positions],*], unique := $unique }))
    idents := idents.push ident
  let each ← columns.mapM fun (x, t) =>
    `((Lanes.Db.Columns.column $(Syntax.mkStrLit (snake (nameString x))) (β := $t)))
  let product ← nest (fun c acc => `(Lanes.Db.Columns.pair $c $acc)) (← `(Lanes.Db.Columns.unit))
    each
  let r := mkIdent (← Macro.addMacroScope `r)
  let x := mkIdent (← Macro.addMacroScope `x)
  let projections ← names.mapM fun f => `($r.$f:ident)
  let values ← parts x names.size
  let indexTerms : Array (TSyntax `term) := idents.map (⟨·.raw⟩)
  cmds := cmds.push (← `(def $name : Lanes.Db.TableOf $T :=
    Lanes.Db.Columns.table
      (Lanes.Db.Columns.map $product (fun $r => $(← tuple projections))
        (fun $x => { $[$names:ident := $values],* }) (fun _ => rfl) (fun _ => rfl))
      $(Syntax.mkStrLit sqlName) $(Syntax.mkNumLit (toString keys.size)) [$[$indexTerms],*]))
  return cmds

end Declare

open Lean Declare in
macro_rules
  | `(lanesDataStructure|
      $[$doc:docComment]? lanes_data structure $T $bs:bracketedBinder* where
        $[$[$fdocs:docComment]? $fields : $types $[:= $defaults]?]*
        $[deriving $classes,*]? $[$tableClause:lanesDataTable]?) => do
    let p ← params bs
    let (lean, ours) ← splitDeriving (classes.map (·.getElems) |>.getD #[])
    independent (if tableClause.isSome then ours.push `TableOf else ours) fields types
    let pargs := p.args
    let applied ← `($T $pargs*)
    let decl ← `(command| $[$doc:docComment]? structure $T:ident $bs:bracketedBinder* where
      $[$[$fdocs:docComment]? $fields:ident : $types $[:= $defaults]?]*)
    let mut cmds := #[decl] ++ (← leanDeriving T lean)
    for f in Format.all do
      if ← wants ours f then
        cmds := cmds ++ (← instances f T p types (← structCodec f (fields.zip types)))
    if ours.contains `Enum then
      let r := mkIdent (← Macro.addMacroScope `r)
      let projections ← fields.mapM fun f => `($r.$f:ident)
      let values ← fresh fields
      cmds := cmds.push (← enum p applied (← productType types)
        (← `(fun $r => $(← tuple projections)))
        (← `(fun $(← tuple values) => { $[$fields:ident := $values],* })))
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
    if let some clause := tableClause then
      cmds := cmds ++ (← table T p (fields.zip types) clause)
    return mkNullNode (cmds.map (·.raw))

open Lean Declare in
macro_rules
  | `(lanesDataInductive|
      $[$doc:docComment]? lanes_data inductive $T $bs:bracketedBinder* where
        $[$[$cdocs:docComment]? | $ctors $argss*]* $[deriving $classes,*]?) => do
    let p ← params bs
    let (lean, ours) ← splitDeriving (classes.map (·.getElems) |>.getD #[])
    let pargs := p.args
    let applied ← `($T $pargs*)
    let binders ← argss.mapM (·.mapM ctorBinder)
    let decl ← `(command| $[$doc:docComment]? inductive $T $bs:bracketedBinder* where
      $[$[$cdocs:docComment]? | $ctors:ident $binders*]*)
    let mut cmds := #[decl] ++ (← leanDeriving T lean)
    let fieldss ← argss.mapM ctorArgs
    let args : Array (Array Ident) := fieldss.map (·.map (·.1))
    let argTypes : Array (Array (TSyntax `term)) := fieldss.map (·.map (·.2))
    for fields in fieldss do
      independent ours (fields.map (·.1)) (fields.map (·.2))
    for f in Format.all do
      if ← wants ours f then
        cmds := cmds ++ (← instances f T p argTypes.flatten (← sumCodec f T ctors fieldss))
    if ours.contains `Enum then
      let n := ctors.size
      let mut cases : Array (TSyntax `term) := #[]
      let mut backs : Array (TSyntax `term) := #[]
      for k in [0:n] do
        let ctor := mkIdent (T.getId ++ ctors[k]!.getId)
        let vars ← fresh args[k]!
        let injected ← inject k n (← tuple vars)
        cases := cases.push (← if vars.isEmpty then pure injected
          else `(fun $vars* => $injected))
        backs := backs.push (← `(fun $(← tuple vars) => $ctor $vars*))
      let back ← nest (fun f acc => `(Sum.elim $f $acc)) (← `(fun x => nomatch x)) backs
      let casesOn := mkIdent (T.getId ++ `casesOn)
      cmds := cmds.push (← enum p applied (← sumType (← argTypes.mapM productType))
        (← `(fun x => $casesOn:ident (motive := fun _ => _) x $cases*)) back)
    if ours.contains `LawfulBEq then
      Macro.throwError "lanes_data: `LawfulBEq` is derived for a structure only"
    return mkNullNode (cmds.map (·.raw))

end Lanes
