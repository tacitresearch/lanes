/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LanesCli.Inventory
import Lanes.Lib.Crypto.Native
import Lanes.Runtime.IO.Park

/-! The inventory's rules, checked when this file is built: on facts written by hand, and on a
theorem of this file. -/

namespace Tests.Inventory

open Lean Lanes.Cli.Inventory

/-- Module `A` runs `run`, which calls `helper`, and states it with a predicate abbreviation
`Holds` and a predicate `Def`; `Wrap` is an abbreviation of a value that calls `other`, of
module `C`. Each of `B`'s theorems is gated and states one of them. -/
def facts (env : Environment) : Facts :=
  let map {α} (xs : List (Name × α)) : NameMap α := xs.foldl (fun m (k, v) => m.insert k v) {}
  let set (xs : List Name) : NameSet := xs.foldl (·.insert ·) {}
  let value : Shape := .value none
  { env
    moduleOf := map [(`A.run, `A), (`A.helper, `A), (`A.main, `A), (`A.Holds, `A),
      (`A.Def, `A), (`A.Wrap, `A), (`C.other, `C)]
    shape := map [(`A.run, value), (`A.helper, value), (`A.main, value), (`A.Holds, .prop),
      (`A.Def, .prop), (`A.Wrap, value), (`C.other, value)]
    uses := map [(`A.run, set [`A.helper]), (`A.helper, {}),
      (`A.main, set [`A.run, `A.Wrap]), (`A.Holds, set [`A.run]),
      (`A.Def, set [`A.run]), (`A.Wrap, set [`C.other]), (`C.other, {})]
    stated := set [`A.Holds, `A.Def, `A.Wrap]
    gated := map [(`B.viaAbbrev, set [`A.Holds]), (`B.viaDef, set [`A.Def]),
      (`B.viaWrap, set [`A.Wrap])]
    reducible := set [`A.Holds, `A.Wrap] }

def credited (env : Environment) (thm c : Name) : Bool :=
  let f := facts env
  ((provedBy f (specs f)).getD c #[]).any (·.1 == thm)

theorem byCases (n : Nat) : n + 0 = n := by
  match n with
  | 0 => rfl
  | _ + 1 => rfl

#eval show MetaM Unit from do
  let env ← getEnv
  let matchers := env.constants.map₂.toList.filterMap fun (n, _) =>
    if Meta.isMatcherCore env n && owner n == ``byCases then some n else none
  let checks := [
    ("a predicate abbreviation states what its body names, in another module",
      credited env `B.viaAbbrev `A.run),
    ("and what that runs in its own module", credited env `B.viaAbbrev `A.helper),
    ("a predicate defined with `def` does not", !credited env `B.viaDef `A.run),
    ("an abbreviation of a value is not read as its body", credited env `B.viaWrap `A.Wrap
      && !credited env `B.viaWrap `C.other),
    ("a theorem's matcher is part of its proof",
      !matchers.isEmpty && matchers.all fun n => ofTheorem env (owner n)),
    ("a definition is not a theorem", !ofTheorem env ``facts),
    ("an `@[extern]` with a Lean body is bound; its reference, and an `opaque` binding, are not",
      isBound env ``Lanes.Bytes.same && isBound env ``Lanes.Sha256.hash
        && !isBound env ``Lanes.Sha256.reference && !isBound env ``Lanes.Parker.new)]
  for (name, ok) in checks do
    unless ok do throwError "inventory: {name}"

end Tests.Inventory
