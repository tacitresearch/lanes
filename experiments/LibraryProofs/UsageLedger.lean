import Ledger.Proofs
import Lean

/-! Which Mathlib, CSLib and Batteries declarations the proof layer of Lanes uses directly, in the
types and proofs of its own declarations. Run from `examples/ledger` with `lake env lean ../../experiments/LibraryProofs/UsageLedger.lean`. -/

open Lean Meta

def libOf (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  let m := env.header.moduleNames[idx.toNat]!
  let r := m.getRoot
  if r == `Mathlib || r == `Cslib || r == `Batteries then some m else none

#eval show MetaM Unit from do
  let env ← getEnv
  let mut uses : Std.HashMap Name (Nat × Name) := {}
  let mut users : Std.HashMap Name Nat := {}
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[idx.toNat]!
    unless m.getRoot == `Ledger do continue
    let cs := ci.getUsedConstantsAsSet
    let mut any := false
    for c in cs do
      if let some lm := libOf env c then
        any := true
        let (k, _) := uses.getD c (0, lm)
        uses := uses.insert c (k + 1, lm)
    if any then users := users.insert m (users.getD m 0 + 1)
  let arr := uses.toArray.qsort (fun a b => a.2.1 > b.2.1)
  IO.println s!"distinct library constants used: {arr.size}"
  let byRoot := arr.foldl (init := ({} : Std.HashMap Name Nat))
    fun acc (_, _, m) => acc.insert m.getRoot (acc.getD m.getRoot 0 + 1)
  IO.println s!"by library: {byRoot.toList}"
  let mut kinds : Std.HashMap String Nat := {}
  for (c, k, m) in arr do
    let some ci := env.find? c | continue
    let kind :=
      if isInstanceCore env c then "instance"
      else if c.isInternalDetail || (`_simp_1).isSuffixOf c || c.toString.endsWith "._simp_1" then "simp-aux"
      else if m.getRoot == `Mathlib && (m.toString.startsWith "Mathlib.Tactic") then "tactic"
      else match ci with
        | .thmInfo _ => "theorem"
        | .inductInfo _ => "type"
        | .ctorInfo _ | .recInfo _ => "constructor/recursor"
        | _ => "definition"
    kinds := kinds.insert s!"{m.getRoot} {kind}" (kinds.getD s!"{m.getRoot} {kind}" 0 + 1)
    IO.println s!"{k}\t{c}\t{m}\t{kind}"
  IO.println s!"--- by kind: {kinds.toList}"
  IO.println "--- Lanes modules with declarations that use them"
  for (m, k) in users.toList do IO.println s!"{k}\t{m}"
