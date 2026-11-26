/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Semantics
import Examples.BankProofs
import Tests.SystemSound

/-!
The bank on two shards conserves money: `Examples.Bank.money_conserved` carried to the split by
`System.Invariant.split`. Conservation reads the credits in flight, so it has to be shown not to
depend on their order. Built by `lake build`, not linked into the test executable.
-/

namespace Tests.SplitProofs

open Lanes Examples.Bank

variable {A : Type} [DecidableEq A] [Fintype A] {opening : Nat}

theorem conserved_of_equiv {env : EnvModel (sig A)} (a b : SysState (bank A opening))
    (h : SysState.Equiv env a b) (ha : Conserved a) : Conserved b := by
  refine ⟨?_, fun i => h.timers ▸ ha.2 i⟩
  rw [← h.state, ← Tests.SystemSound.sum_perm (h.net.toPerm.map inFlight)]
  exact ha.1

theorem split_money_conserved (hosts : A → Bool) (env : EnvModel (sig A)) (henv : env.Faultless)
    {c : SysState ((bank A opening).split hosts)}
    (hc : (bank A opening).SplitReachable hosts env c) : Conserved c.merged :=
  (money_conserved env henv).split conserved_of_equiv (fun _ hi => nomatch hi) hc

end Tests.SplitProofs
