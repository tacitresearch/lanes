module

public import Spike.Class
public meta import Lean.Elab.Deriving.Basic

/-! A deriving handler for `Spike.Describe`. It runs in the elaborator, so it needs `Lean.Elab`. -/

open Lean Elab Command

namespace Spike.Derive

meta def describeHandler (names : Array Name) : CommandElabM Bool := do
  let env ← getEnv
  for n in names do
    let some info := getStructureInfo? env n | return false
    let lits := info.fieldNames.map fun f => Syntax.mkStrLit f.toString
    let T := mkIdent n
    elabCommand (← `(instance : Spike.Describe $T := ⟨[$[$lits],*]⟩))
  return true

meta initialize registerDerivingHandler ``Spike.Describe describeHandler

end Spike.Derive
