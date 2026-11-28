module

public meta import Lanes.Data.Declare
public meta import Lanes.Lib.Encoding.Json.Classes
public meta import Lean.Elab.Deriving.Basic

/-!
`deriving ToJson, FromJson, Enum` on a plain `structure` or `inductive`, for Lanes' classes, with
the codecs and laws `lanes_data` builds. A handler reads the type from the environment, turns each
field's type back into syntax with the delaborator, and hands the result to the same functions
`lanes_data` uses (`Lanes.Declare.json`, `structJson`, `sumJson`, `enum`). An application imports
this file with `meta import`, so none of it, nor `Lean.Elab`, is in its binary.
-/

open Lean Elab Command Meta

namespace Spike.Lanes

/-- A field or a constructor's argument: its name and its type as syntax. -/
abbrev Field := Ident × Term

/-- What a handler needs of a type: its parameters, as `lanes_data` keeps them, and each
constructor with its fields. -/
structure Shape where
  T : Ident
  params : Lanes.Declare.Params
  ctors : Array (Ident × Array Field)
  isStructure : Bool

meta def delabType (e : Expr) : MetaM Term :=
  withOptions (fun o => o.setBool `pp.fullNames true |>.setBool `pp.funBinderTypes true)
    (PrettyPrinter.delab e)

/-- The fields `xs` of a constructor, refusing a type that names an earlier field or the type
itself: a codec is built from each field's type alone. -/
meta def fieldsOf (declName : Name) (xs : Array Expr) : MetaM (Array Field) := do
  let mut out := #[]
  for h : k in [0:xs.size] do
    let d ← xs[k].fvarId!.getDecl
    if d.type.hasAnyFVar (fun f => xs.extract 0 k |>.any (·.fvarId! == f)) then
      throwError "deriving: the type of `{d.userName}` names an earlier field. Put the property \
        in that field's type, as a subtype `\{x : α // p x}`."
    if d.type.find? (·.isConstOf declName) |>.isSome then
      throwError "deriving: `{d.userName}` is of a type that refers to `{privateToUserName declName}`: a derived \
        codec is a value and cannot refer to itself"
    out := out.push (mkIdent d.userName, ← delabType d.type)
  return out

meta def shapeOf (declName : Name) : TermElabM Shape := do
  let ind ← getConstInfoInduct declName
  if ind.numIndices != 0 then throwError "deriving: `{declName}` has indices"
  forallBoundedTelescope ind.type ind.numParams fun ps _ => do
    let mut params : Lanes.Declare.Params := {}
    for p in ps do
      let d ← p.fvarId!.getDecl
      let x := mkIdent d.userName
      let t ← delabType d.type
      params := { params with
        binders := params.binders.push (← `(bracketedBinder| {$x : $t}))
        args := params.args.push x
        types := if d.type.isType then params.types.push x else params.types }
    let env ← getEnv
    let ctors ← if isStructure env declName then
        -- A structure's fields flattened, as `{ x := …, colour := … }` takes them, `extends` too.
        withLocalDeclD `self (mkAppN (.const declName (ind.levelParams.map .param)) ps) fun self => do
          let fields := getStructureFieldsFlattened env declName (includeSubobjectFields := false)
          let mut out := #[]
          for f in fields do
            let t ← inferType (← mkProjection self f)
            if t.containsFVar self.fvarId! then
              throwError "deriving: the type of `{f}` names another field. Put the property \
                in that field's type, as a subtype `\{x : α // p x}`."
            out := out.push (mkIdent f, ← delabType t)
          return #[(mkIdent `mk, out)]
      else ind.ctors.toArray.mapM fun c => do
        let info ← getConstInfoCtor c
        forallTelescope (← instantiateForall info.type ps) fun xs _ =>
          return (mkIdent (c.replacePrefix declName .anonymous), ← fieldsOf declName xs)
    return { T := mkIdent (`_root_ ++ privateToUserName declName), params, ctors,
             isStructure := isStructure env declName }

meta def emit (cmds : Array (TSyntax `command)) : CommandElabM Unit :=
  cmds.forM fun c => elabCommand c

/-- `ToJson` and `FromJson` are made together, from one codec, with `LawfulJson` and
`NonNullJson`: whichever handler runs first makes them all, and the other finds the codec. -/
meta def jsonHandler (names : Array Name) : CommandElabM Bool := do
  for n in names do
    if (← getEnv).contains (n ++ `jsonCodec) then continue
    let s ← liftTermElabM (shapeOf n)
    let types := s.ctors.flatMap (·.2.map (·.2))
    let codec ← liftMacroM <|
      if s.isStructure then Lanes.Declare.structJson s.ctors[0]!.2
      else Lanes.Declare.sumJson s.T (s.ctors.map (·.1)) (s.ctors.map (·.2))
    emit (← liftMacroM (Lanes.Declare.json s.T s.params types codec))
  return true

meta def enumHandler (names : Array Name) : CommandElabM Bool := do
  for n in names do
    let s ← liftTermElabM (shapeOf n)
    let pargs := s.params.args
    let applied ← `($s.T $pargs*)
    let cmd ← liftMacroM <| do
      if s.isStructure then
        let (_, fields) := s.ctors[0]!
        let r := mkIdent (← Macro.addMacroScope `r)
        let names := fields.map (·.1)
        let projections ← names.mapM fun f => `($r.$f:ident)
        let values ← Lanes.Declare.fresh names
        Lanes.Declare.enum s.params applied (← Lanes.Declare.productType (fields.map (·.2)))
          (← `(fun $r => $(← Lanes.Declare.tuple projections)))
          (← `(fun $(← Lanes.Declare.tuple values) => { $[$names:ident := $values],* }))
      else
        let k := s.ctors.size
        let mut cases : Array Term := #[]
        let mut backs : Array Term := #[]
        for h : i in [0:k] do
          let (c, fields) := s.ctors[i]
          let ctor := mkIdent (s.T.getId ++ c.getId)
          let vars ← Lanes.Declare.fresh (fields.map (·.1))
          let injected ← Lanes.Declare.inject i k (← Lanes.Declare.tuple vars)
          cases := cases.push (← if vars.isEmpty then pure injected else `(fun $vars* => $injected))
          backs := backs.push (← `(fun $(← Lanes.Declare.tuple vars) => $ctor $vars*))
        let back ← Lanes.Declare.nest (fun f acc => `(Sum.elim $f $acc)) (← `(fun x => nomatch x)) backs
        let casesOn := mkIdent (s.T.getId ++ `casesOn)
        let code ← Lanes.Declare.sumType
          (← s.ctors.mapM fun (_, fs) => Lanes.Declare.productType (fs.map (·.2)))
        Lanes.Declare.enum s.params applied code
          (← `(fun x => $casesOn:ident (motive := fun _ => _) x $cases*)) back
    elabCommand cmd
  return true

/-- `lanes_table todos : Todo key id`, then `index` lines: `lanes_data`'s `table` line as a command of
its own, for a structure declared anywhere before it. -/
syntax (name := tableCmd) "lanes_table " ident (str)? " : " ident &" key " ident,+
  lanesDataIndex* : command

@[command_elab tableCmd] public meta def elabTable : CommandElab
  | `(lanes_table $name $[$sql]? : $T key $keys,* $indexes*) => do
    let declName ← liftCoreM (realizeGlobalConstNoOverloadWithInfo T)
    unless isStructure (← getEnv) declName do throwErrorAt T "table: `{T}` is not a structure"
    let s ← liftTermElabM (shapeOf declName)
    let clause ← `(Lanes.lanesDataTable| table $name $[$sql]? key $keys,* $indexes*)
    emit (← liftMacroM (Lanes.Declare.table s.T s.params s.ctors[0]!.2 clause))
  | _ => throwUnsupportedSyntax

meta initialize
  registerDerivingHandler ``Lanes.ToJson jsonHandler
  registerDerivingHandler ``Lanes.FromJson jsonHandler
  registerDerivingHandler ``Lanes.Enum enumHandler

end Spike.Lanes
