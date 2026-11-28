/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Semantics
import Tests.Fixtures.Bank

/-!
# The bank conserves money, for every number of accounts

`Tests/Bank.lean` checks conservation on two accounts and three transfers. Here it is proved for
any finite set of accounts, any opening balance and any run, under any environment model that
does not lose or duplicate messages and does not crash accounts. The model checker shows the
assumption is needed: with lossy links it finds a lost credit in four steps.

The invariant counts the money in the accounts and the money in flight:

  sum of all balances + sum of all credits in flight = number of accounts × opening balance
-/

namespace Tests.Fixtures.Bank

open Lanes

variable {A : Type} [DecidableEq A] [Fintype A] {opening : Nat}

/-- The money a message in flight carries. -/
def inFlight (e : Envelope (sig A)) : Int :=
  match e.msg with
  | .credit amount => amount
  | .transfer .. | .query _ => 0

/-- Money is conserved, and no account has a timer pending. The second part makes the first
inductive: a timeout would otherwise be a step to account for. -/
def Conserved (c : SysState (bank A opening)) : Prop :=
  (∑ a : A, (c.state a).balance) + (c.net.map inFlight).sum = Fintype.card A * opening ∧
    ∀ a : A, c.timers a = []

/-- What handling a message does to the whole state: the money moved, and nothing else that
`Conserved` reads. -/
theorem handle_spec (env : EnvModel (sig A)) (c : SysState (bank A opening)) (a : A)
    (msg : Msg A) :
    let c' := c.handle env a msg
    (∑ b : A, (c'.state b).balance) + (c'.net.map inFlight).sum
        = (∑ b : A, (c.state b).balance) + (c.net.map inFlight).sum
          + (match msg with | .credit amount => (amount : Int) | _ => 0)
      ∧ c'.timers = c.timers := by
  cases msg with
  | transfer req dst amount =>
    by_cases h : (amount : Int) ≤ (c.state a).balance
    · simp [SysState.handle, SysState.settle, SysState.perform, Effect.isStop, bank, account, h,
        sum_update (fun _ (s : Account) => s.balance), inFlight]
    · simp [SysState.handle, SysState.settle, SysState.perform, Effect.isStop, bank, account, h]
  | credit amount =>
    simp [SysState.handle, SysState.settle, bank, account,
      sum_update (fun _ (s : Account) => s.balance)]
    omega
  | query req =>
    simp [SysState.handle, SysState.settle, SysState.perform, Effect.isStop, bank, account]

/--
Money is conserved in every reachable state of the bank, for any accounts and any opening
balance, as long as the environment loses, duplicates and crashes nothing.
-/
theorem money_conserved (env : EnvModel (sig A)) (henv : env.Faultless) :
    (bank A opening).Invariant env Conserved := by
  apply System.Inductive.invariant
  constructor
  · simp [Conserved, SysState.init, SysState.blank, bank, account]
  · rintro c ev c' ⟨hsum, htimers⟩ hstep
    cases ev with
    | input x =>
      obtain rfl := SysState.step_input.mp hstep
      refine ⟨?_, htimers⟩
      cases x <;> simpa [bank, inFlight] using hsum
    | deliver e =>
      obtain ⟨_, hdeliverable, rfl⟩ := SysState.step_deliver.mp hstep
      have hmem := SysState.mem_of_deliverable hdeliverable
      obtain ⟨hmoney, htimers'⟩ := handle_spec env { c with net := c.net.erase e } e.dst e.msg
      refine ⟨?_, fun a => by rw [htimers']; exact htimers a⟩
      rw [hmoney]
      simp only [sum_map_erase inFlight hmem]
      obtain ⟨src, dst, msg⟩ := e
      cases msg <;> simp [inFlight] at hsum ⊢ <;> omega
    | duplicate e =>
      obtain ⟨_, hdup, _⟩ := SysState.step_duplicate.mp hstep
      simp [henv.noDuplicates] at hdup
    | drop e =>
      obtain ⟨hlossy, _⟩ := SysState.step_drop.mp hstep
      simp [henv.lossless] at hlossy
    | timeout a msg =>
      obtain ⟨_, hpending, _⟩ := SysState.step_timeout.mp hstep
      simp [htimers a] at hpending
    | output out =>
      obtain ⟨_, rfl⟩ := SysState.step_output.mp hstep
      exact ⟨hsum, htimers⟩
    | crash a =>
      obtain ⟨_, hcrash, _⟩ := SysState.step_crash.mp hstep
      simp [henv.noCrashes] at hcrash
    | start a =>
      obtain ⟨_, _, rfl⟩ := SysState.step_start.mp hstep
      refine ⟨?_, ?_⟩
      · simpa [SysState.startActor, SysState.settle, Effect.isStop, bank, account,
          sum_update (fun _ (s : Account) => s.balance)] using hsum
      · simpa [SysState.startActor, SysState.settle, Effect.isStop, bank, account] using htimers
    | restart =>
      obtain ⟨hmay, -⟩ := SysState.step_restart.mp hstep
      simp [henv.noRestarts] at hmay

end Tests.Fixtures.Bank
