/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Semantics
import Tests.Tutorial.Counter

/-!
The theorems. Nothing executable imports this file, so the application binary stays small, and
`Check.lean` does not, so a broken proof does not stop the checks: `lake test` runs the checks,
then builds this file with warnings as errors, and a `sorry` fails it.

The invariant is proved per transaction: each transaction, run on a database whose counts are
within the limit, leaves one whose counts are (`preserves`). The store runs transactions at
`SERIALIZABLE`, so the database is always what some order of them, one after another, would
leave, and the invariant holds in every database the store's model allows (`within_always`):
with lost `COMMIT`s, failures, retries and restarts.
-/

namespace Tut

open Lanes Lanes.Db

/-- A count is between zero and the limit. -/
def Count.Within (config : Config) (c : Count) : Prop :=
  0 ≤ c.value.toInt ∧ c.value.toInt ≤ config.limit

/-- Every count of the table is between zero and the limit. -/
def Within (config : Config) (db : Db) : Prop :=
  counts.Every (Count.Within config) db

variable {config : Config}

/-- `current` reads, and what it reads is within the limit. -/
theorem current_within {db : Db} (hw : Within config db) {c : Count} {db' : Db}
    (h : current.run db = .ok (c, db')) : db' = db ∧ c.Within config := by
  obtain ⟨found, db₁, h₁, h₂⟩ := Txn.run_bind_ok_inv h
  obtain rfl := (TableOf.get_reads _ _).run h₁
  simp only [Txn.pure_eq, Txn.run_pure, Except.ok.injEq, Prod.mk.injEq] at h₂
  obtain ⟨rfl, rfl⟩ := h₂
  refine ⟨rfl, ?_⟩
  cases found with
  | none => simp [Count.Within]
  | some c => exact counts.get_every hw h₁

/-- Writing a count within the limit keeps every count within it. -/
theorem upsert_within {db : Db} (hw : Within config db) {c : Count} (hc : c.Within config)
    {b : Bool} {db' : Db} (h : (counts.upsert c).run db = .ok (b, db')) : Within config db' :=
  counts.every_apply _ (fun _ => rfl) (fun r hr c' hc' => by
    simp only [Op.written, Option.some.injEq] at hr
    subst hr
    rw [counts.ofRow_toRow] at hc'
    cases hc'
    exact hc) (Txn.run_single h) hw

/-- A count of `n` is within the limit when `n` is. -/
theorem ofNat_within (hlimit : config.limit < 2 ^ 63) (name : String) {n : Nat}
    (h : n ≤ config.limit) : Count.Within config { name, value := Int64.ofNat n } := by
  simp only [Count.Within, Int64.toInt_ofNat_of_lt (by omega : n < 2 ^ 63)]
  omega

/-- Every transaction keeps every count within the limit. -/
theorem preserves (hlimit : config.limit < 2 ^ 63) :
    Preserves (handler config) (Within config) := by
  intro q db a db' hw h
  cases q with
  | increment =>
    obtain ⟨c, db₁, h₁, h₂⟩ := Txn.run_bind_ok_inv (t := current) h
    obtain ⟨rfl, hc⟩ := current_within hw h₁
    split at h₂
    · next hlt =>
      obtain ⟨b, db₂, h₃, h₄⟩ := Txn.run_bind_ok_inv h₂
      simp only [Txn.pure_eq, Txn.run_pure, Except.ok.injEq, Prod.mk.injEq] at h₄
      rw [← h₄.2]
      exact upsert_within hw (ofNat_within hlimit _ (by omega)) h₃
    · simp only [Txn.pure_eq, Txn.run_pure, Except.ok.injEq, Prod.mk.injEq] at h₂
      rw [← h₂.2]
      exact hw
  | decrement =>
    obtain ⟨c, db₁, h₁, h₂⟩ := Txn.run_bind_ok_inv (t := current) h
    obtain ⟨rfl, hc⟩ := current_within hw h₁
    split at h₂
    · obtain ⟨b, db₂, h₃, h₄⟩ := Txn.run_bind_ok_inv h₂
      simp only [Txn.pure_eq, Txn.run_pure, Except.ok.injEq, Prod.mk.injEq] at h₄
      rw [← h₄.2]
      exact upsert_within hw (ofNat_within hlimit _ (by have := hc.2; omega)) h₃
    · simp only [Txn.pure_eq, Txn.run_pure, Except.ok.injEq, Prod.mk.injEq] at h₂
      rw [← h₂.2]
      exact hw
  | read =>
    obtain ⟨c, db₁, h₁, h₂⟩ := Txn.run_bind_ok_inv (t := current) h
    obtain ⟨rfl, -⟩ := current_within hw h₁
    simp only [Txn.pure_eq, Txn.run_pure, Except.ok.injEq, Prod.mk.injEq] at h₂
    rw [← h₂.2]
    exact hw

theorem within_empty : Within config (Db.empty schema) := by
  intro x hx
  simp [Db.empty, Db.rows, schema] at hx

/-- **The count never passes the limit**, in any database the store may hold after any run of
the front beside the store's model: with lost `COMMIT`s, failures, calls taking effect late,
restarts, and every call still outstanding taking effect. -/
theorem within_always (hlimit : config.limit < 2 ^ 63) (cfg : Db.Config)
    {events : List (Event sig)} {s : Db.State Request Response}
    (hrun : (Db.outside cfg (handler config) (Db.empty schema) port).after events = some s) :
    ∀ w ∈ s.worlds, ∀ w' ∈ w.expand (handler config) w.fuel, Within config w'.db :=
  Db.invariant cfg port within_empty (preserves hlimit) hrun

end Tut

/-- info: 'Tut.preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Tut.preserves

/-- info: 'Tut.within_always' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Tut.within_always
