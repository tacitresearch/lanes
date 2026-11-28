/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Db.JobsSound
public import Lanes.Web.Auth.Rows

/-!
What the rows of `Lanes/Web/Auth/Rows.lean` keep, for every database:

- **Failed log-ins stay within their limit.** Every transaction of `Failures` keeps each user's
  row `Auth.Attempts.Bounded` (`Failures.bounded`): at most `limit` failures, and an account with
  that many is locked. With `Db.invariant`, so is every database the store may hold, across
  restarts, lost `COMMIT`s and retries.
- **A closed session stays closed.** After `close` commits, `accepts` lets nobody in with its id
  (`Sessions.closed_refused`).
-/

@[expose] public section

namespace Lanes.Auth.Rows

open Lanes.Db

namespace Failures

variable (cfg : Config)

/-- Every user's row is within the limit. -/
def Bounded (db : Db) : Prop := (table cfg).Every (fun r => Auth.Attempts.Bounded cfg.limit r.attempts) db

theorem attempts_of {user : String} {a : Auth.Attempts} (h : a.failures < 2 ^ 63) :
    (AttemptsRow.of user a).attempts = a := by
  simp [AttemptsRow.of, AttemptsRow.attempts, Int64.toInt_ofNat_of_lt h]

/-- An operation of these transactions: on the table, writing only rows within the limit. -/
def Good (o : Op) : Prop :=
  (o.table.name = (table cfg).table.name → o.table = (table cfg).table) ∧
    ∀ r, o.written = some r → ∀ a, (table cfg).ofRow r = some a → Auth.Attempts.Bounded cfg.limit a.attempts

theorem read_good (user : String) : (read cfg user).All (Good cfg) :=
  Txn.All.bind (Txn.All.bind (Txn.All.single ⟨fun _ => rfl, fun _ h => by cases h⟩) fun r => by
    cases r with
    | some x =>
      refine Txn.All.bind ?_ fun _ => .pure _
      unfold TableOf.decode; split
      · exact .pure _
      · exact .abort _
    | none => exact .pure _) fun _ => .pure _

theorem write_good (hlimit : cfg.limit < 2 ^ 63) (user : String) {a : Auth.Attempts}
    (ha : Auth.Attempts.Bounded cfg.limit a) : (write cfg user a).All (Good cfg) := by
  refine Txn.All.map _ (Txn.All.single ⟨fun _ => rfl, fun r hr b hb => ?_⟩)
  simp only [Op.written, Option.some.injEq] at hr
  subst hr
  rw [(table cfg).ofRow_toRow] at hb
  obtain rfl := Option.some.inj hb
  rw [attempts_of (by have := ha.1; omega)]
  exact ha

theorem good_bounded {α : Type} {t : Txn α} (ht : t.All (Good cfg)) :
    ∀ db a db', Bounded cfg db → t.run db = .ok (a, db') → Bounded cfg db' :=
  ht.keeps fun o ho _ _ _ hP h => (table cfg).every_apply o ho.1 ho.2 h hP

/-- **Failed log-ins stay within their limit.** Every transaction of `Failures` keeps every
user's row within it. -/
theorem bounded (hlimit : cfg.limit < 2 ^ 63) (user : String) :
    (∀ db a db', Bounded cfg db → (failed cfg user).run db = .ok (a, db') → Bounded cfg db') ∧
    (∀ db a db', Bounded cfg db → (succeeded cfg user).run db = .ok (a, db') → Bounded cfg db') ∧
    (∀ db a db', Bounded cfg db → (unlock cfg user).run db = .ok (a, db') → Bounded cfg db') ∧
    (∀ db a db', Bounded cfg db → (locked cfg user).run db = .ok (a, db') → Bounded cfg db') := by
  refine ⟨good_bounded cfg ?_, good_bounded cfg ?_, good_bounded cfg ?_, good_bounded cfg ?_⟩
  · exact Txn.All.bind (read_good cfg user) fun x =>
      Txn.All.bind (write_good cfg hlimit user (Auth.Attempts.bounded_fail _ _)) fun _ => .pure _
  · exact Txn.All.bind (read_good cfg user) fun x => write_good cfg hlimit user (Auth.Attempts.bounded_succeed _ _)
  · exact write_good cfg hlimit user (by simp [Auth.Attempts.Bounded, Auth.Attempts.unlock]; omega)
  · exact Txn.All.bind (read_good cfg user) fun _ => .pure _

end Failures

namespace Sessions

variable (cfg : Config)

/-- **A closed session stays closed.** Once `close id` has committed, `accepts id` lets nobody
in, at any time, and changes nothing. -/
theorem closed_refused (id now_s : Int64) {db : Db} {u : Unit} {db' : Db}
    (h : (close cfg id).run db = .ok (u, db')) : (accepts cfg id now_s).run db' = .ok (none, db') := by
  obtain ⟨b, hb, -⟩ := Lanes.Db.Jobs.Queue.run_map _ _ h
  have ha := Txn.run_single hb
  have hrows := Op.rows_apply _ ha (table cfg).table.name
  simp only [Op.writes, Op.table, true_and, ↓reduceIte] at hrows
  have hnone : (db'.rows (table cfg).table.name).find? ((table cfg).table.hasKey [.int id]) = none := by
    rw [hrows, Op.delete_rows]
    exact List.find?_eq_none.mpr fun x hx => by simpa using (List.mem_filter.mp hx).2
  have hget : (Op.get (table cfg).table [.int id]).apply db' = .ok (none, db') := by
    obtain ⟨hv, -⟩ := Op.apply_ok _ ha
    unfold Op.apply
    have hv' : (Op.get (table cfg).table [.int id]).valid = true := by
      simpa [Op.valid] using hv
    simp only [hv', ↓reduceIte, Op.writes, Op.onRows, Op.table]
    rw [hnone]
    rfl
  simp only [accepts, TableOf.get, Txn.bind_eq, Txn.get]
  rw [Txn.run_bind, Txn.run_bind]
  erw [Txn.run_op_ok _ hget]
  rfl

end Sessions

end Lanes.Auth.Rows
