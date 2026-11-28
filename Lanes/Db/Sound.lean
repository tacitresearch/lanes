/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Db.Model

/-!
What the typed store promises, proved for every handler:

- **Invariants are proved per transaction.** For an invariant of the database that the start
  satisfies and every transaction of a handler keeps (`Preserves`), every database the model
  allows after every run, with every call that may still take effect applied, satisfies it
  (`invariant`). So a lost `COMMIT` that takes effect late, or a retry, cannot break it.
- **A retry is one run.** A call that committed after attempts that conflicted or lost their
  connection answers what one run of its transaction answers on the state it committed against,
  and leaves the state that run leaves (`Retry.loop_committed`).
- **The driver runs the meaning.** A transaction interpreted with each operation answered by its
  meaning, as a serializable server answers it, is `Txn.run` (`Txn.interp_apply`).

And the facts a proof of `Preserves` takes apart a transaction with: `Txn.run_bind`, that a read
leaves the database as it was (`Op.apply_read`), and that a write changes only its own table
(`Op.rows_apply`).
-/

@[expose] public section

namespace Lanes.Db

variable {Q A : Type}

/-- Every transaction of the handler keeps `I`. -/
def Preserves (h : Handler Q A) (I : Db → Prop) : Prop :=
  ∀ q db a db', I db → (h q).run db = .ok (a, db') → I db'

/-! ## Transactions -/

namespace Txn

@[simp] theorem run_pure {α : Type} (a : α) (db : Db) : (Txn.pure a).run db = .ok (a, db) := rfl

@[simp] theorem run_abort {α : Type} (why : String) (db : Db) :
    (Txn.abort why : Txn α).run db = .error why := rfl

theorem run_op_ok {α : Type} {o : Op} (k : o.Ret → Txn α) {db : Db} {r : o.Ret} {db' : Db}
    (h : o.apply db = .ok (r, db')) : (Txn.op o k).run db = (k r).run db' := by
  simp [run, h]

theorem run_op_error {α : Type} {o : Op} (k : o.Ret → Txn α) {db : Db} {e : String}
    (h : o.apply db = .error e) : (Txn.op o k).run db = .error e := by
  simp [run, h]

@[simp] theorem pure_eq {α : Type} (a : α) : (Pure.pure a : Txn α) = Txn.pure a := rfl

@[simp] theorem bind_eq {α β : Type} (t : Txn α) (f : α → Txn β) : t >>= f = t.bind f := rfl

theorem run_bind {α β : Type} (t : Txn α) (f : α → Txn β) (db : Db) :
    (t.bind f).run db = match t.run db with
      | .ok (a, db') => (f a).run db'
      | .error e => .error e := by
  induction t generalizing db with
  | pure a => rfl
  | abort why => rfl
  | op o k ih =>
    simp only [bind]
    cases h : o.apply db with
    | error e => simp [run_op_error _ h]
    | ok p => rw [run_op_ok _ h, run_op_ok _ h]; exact ih p.1 p.2

/-- A transaction answered operation by operation by each one's meaning, in the state monad of
the database, is its meaning. -/
theorem interp_apply {α : Type} (t : Txn α) (db : Db) :
    (t.interp (m := StateT Db (Except String)) (fun o => StateT.mk o.apply)).run db = t.run db := by
  induction t generalizing db with
  | pure a => rfl
  | abort why => rfl
  | op o k ih =>
    simp only [interp, StateT.run_bind]
    show (StateT.mk o.apply).run db >>= _ = _
    simp only [StateT.run_mk]
    cases h : o.apply db with
    | error e => rw [run_op_error _ h]; rfl
    | ok p => rw [run_op_ok _ h]; exact ih p.1 p.2

end Txn

/-! ## Operations -/

theorem Op.apply_read (o : Op) (hread : o.writes = false) {db : Db} {r : o.Ret} {db' : Db}
    (h : o.apply db = .ok (r, db')) : db' = db := by
  unfold Op.apply at h
  split at h
  · simp only [hread, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at h
    exact h.2.symm
  · cases h

theorem lookup_replace (l : List (String × List Row)) (n m : String) (rows : List Row) :
    (l.map fun (k, rs) => if k == n then (k, rows) else (k, rs)).lookup m
      = if m = n then (if l.any (·.1 == n) then some rows else none) else l.lookup m := by
  induction l with
  | nil => simp [List.lookup]
  | cons p l ih =>
    obtain ⟨k, rs⟩ := p
    simp only [List.map_cons, List.lookup, List.any_cons]
    by_cases hk : k = n
    · subst hk
      simp only [beq_self_eq_true, ↓reduceIte, Bool.true_or]
      split <;> simp_all
    · have hkn : (k == n) = false := by simpa using hk
      simp only [hkn, Bool.false_eq_true, ↓reduceIte, Bool.false_or]
      split <;> simp_all

theorem Db.rows_setRows (db : Db) (n m : String) (rows : List Row) :
    (db.setRows n rows).rows m = if m = n then rows else db.rows m := by
  unfold Db.setRows Db.rows
  split
  · rename_i hany
    simp only [lookup_replace, hany, ↓reduceIte]
    split <;> simp
  · rename_i hany
    simp only [Bool.not_eq_true, List.any_eq_false, beq_iff_eq] at hany
    by_cases hm : m = n
    · subst hm
      have : db.tables.lookup m = none := by
        rw [List.lookup_eq_none_iff]
        intro p hp
        have := hany p hp
        simp only [bne_iff_ne, ne_eq]
        exact fun h => this h.symm
      simp [List.lookup_append, this, List.lookup]
    · cases h : db.tables.lookup m with
      | some rs => simp [List.lookup_append, h, hm]
      | none =>
        have : (m == n) = false := by simpa using hm
        simp [List.lookup_append, h, hm, List.lookup, this]

/-- A valid operation answers what it answers on its table's rows; a write leaves those rows as
`onRows` says, and every other table as it was. -/
theorem Op.rows_apply (o : Op) {db : Db} {r : o.Ret} {db' : Db} (h : o.apply db = .ok (r, db'))
    (name : String) :
    db'.rows name = if o.writes ∧ name = o.table.name then (o.onRows (db.rows o.table.name)).2
      else db.rows name := by
  unfold Op.apply at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    by_cases hw : o.writes = true
    · simp [hw, Db.rows_setRows]
    · simp [hw]
  · cases h

theorem Op.apply_ok (o : Op) {db : Db} {r : o.Ret} {db' : Db} (h : o.apply db = .ok (r, db')) :
    o.valid = true ∧ r = (o.onRows (db.rows o.table.name)).1 := by
  unfold Op.apply at h
  split at h
  · rename_i hv
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    exact ⟨hv, h.1.symm⟩
  · cases h

/-! ## Retries -/

namespace Retry

/-- What a retryable attempt is: one rolled back by a conflict, or that lost its connection
before `COMMIT`. -/
def Served.retryable : Served → Bool
  | .conflict | .dropped => true
  | .against _ => false

/-- A call that committed after attempts that conflicted or lost their connection is one run of
its transaction against the state it committed against: the answer and the state after are that
run's. -/
theorem loop_committed {α : Type} (t : Txn α) (attempts_max : Nat) :
    ∀ (served : List Served) (n : Nat) (a : α) (db' : Db),
      loop attempts_max n (served.map (Served.attempt t)) = .committed (a, db') →
      ∃ (k : Nat) (db : Db), (∀ i, i < k → ∀ s, served[i]? = some s → Served.retryable s = true)
        ∧ served[k]? = some (Served.against db) ∧ t.run db = .ok (a, db') := by
  intro served
  induction served with
  | nil => intro n a db' h; simp [loop] at h
  | cons s rest ih =>
    intro n a db' h
    have retry : ∀ s, Served.retryable s = true → (∀ r, Served.attempt t s = r →
        loop attempts_max n (r :: rest.map (Served.attempt t)) = .committed (a, db') →
        loop attempts_max (n + 1) (rest.map (Served.attempt t)) = .committed (a, db')) →
        loop attempts_max n ((s :: rest).map (Served.attempt t)) = .committed (a, db') →
        ∃ (k : Nat) (db : Db), (∀ i, i < k → ∀ s', (s :: rest)[i]? = some s' → Served.retryable s' = true)
          ∧ (s :: rest)[k]? = some (Served.against db) ∧ t.run db = .ok (a, db') := by
      intro s hs hstep h
      obtain ⟨k, db, hk, hs', hrun⟩ := ih (n + 1) a db' (hstep _ rfl h)
      refine ⟨k + 1, db, fun i hi s' hs'' => ?_, by simpa using hs', hrun⟩
      cases i with
      | zero => simp at hs''; subst hs''; exact hs
      | succ i => exact hk i (by omega) s' (by simpa using hs'')
    cases s with
    | conflict =>
      refine retry .conflict rfl (fun r hr h => ?_) h
      subst hr
      by_cases hn : n + 1 < attempts_max
      · simpa [Served.attempt, loop, next, hn] using h
      · simp [Served.attempt, loop, next, hn] at h
    | dropped =>
      refine retry .dropped rfl (fun r hr h => ?_) h
      subst hr
      by_cases hn : n + 1 < attempts_max
      · simpa [Served.attempt, loop, next, hn] using h
      · simp [Served.attempt, loop, next, hn] at h
    | against db =>
      refine ⟨0, db, fun i hi => absurd hi (Nat.not_lt_zero i), rfl, ?_⟩
      simp only [List.map_cons, Served.attempt, loop] at h
      cases hrun : t.run db with
      | error e => simp [hrun, next] at h
      | ok p => simp [hrun, next] at h; rw [h]

end Retry

/-! ## The model -/

section Model

variable [DecidableEq Q] [DecidableEq A] {h : Handler Q A} {I : Db → Prop}

omit [DecidableEq A] in
theorem World.effects_inv (hI : Preserves h I) (w : World Q A) (hw : I w.db) :
    ∀ w' ∈ w.effects h, I w'.db := by
  intro w' hw'
  simp only [World.effects, List.mem_append, List.mem_filterMap, Option.map_eq_some_iff] at hw'
  rcases hw' with ⟨c, -, ⟨a, db⟩, hrun, rfl⟩ | ⟨q, -, ⟨a, db⟩, hrun, rfl⟩
  · cases hr : (h c.request).run w.db with
    | error e => simp [hr, Except.toOption] at hrun
    | ok p =>
      simp only [hr, Except.toOption, Option.some.injEq] at hrun
      subst hrun
      exact hI _ _ _ _ hw hr
  · cases hr : (h q).run w.db with
    | error e => simp [hr, Except.toOption] at hrun
    | ok p =>
      simp only [hr, Except.toOption, Option.some.injEq] at hrun
      subst hrun
      exact hI _ _ _ _ hw hr

omit [DecidableEq A] in
theorem World.expand_inv (hI : Preserves h I) :
    ∀ (fuel : Nat) (w : World Q A), I w.db → ∀ w' ∈ w.expand h fuel, I w'.db := by
  intro fuel
  induction fuel with
  | zero => intro w hw w' hw'; simp only [World.expand, List.mem_singleton] at hw'; exact hw' ▸ hw
  | succ fuel ih =>
    intro w hw w' hw'
    simp only [World.expand, List.mem_cons, List.mem_flatMap] at hw'
    rcases hw' with rfl | ⟨v, hv, hw'⟩
    · exact hw
    · exact ih v (World.effects_inv hI w hw v hv) w' hw'

theorem World.answer_db (w : World Q A) (r : Reply A) : ∀ w' ∈ w.answer r, w'.db = w.db := by
  intro w' hw'
  simp only [World.answer] at hw'
  split at hw' <;> (try split at hw') <;> (try split at hw') <;> simp_all

theorem mem_dedup {α : Type} [DecidableEq α] {xs : List α} {x : α} (h : x ∈ dedup xs) : x ∈ xs := by
  unfold dedup at h
  suffices ∀ (acc : List α), x ∈ xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) acc →
      x ∈ acc ∨ x ∈ xs from (this [] h).resolve_left (by simp)
  clear h
  induction xs with
  | nil => intro acc h; exact .inl h
  | cons y ys ih =>
    intro acc h
    simp only [List.foldl_cons] at h
    rcases ih _ h with h | h
    · split at h
      · exact .inl h
      · simp only [List.mem_append, List.mem_singleton] at h
        rcases h with h | rfl
        · exact .inl h
        · exact .inr List.mem_cons_self
    · exact .inr (List.mem_cons_of_mem _ h)

/-- What every world of the model satisfies, with every call that may still take effect applied. -/
def Holds (h : Handler Q A) (I : Db → Prop) (s : State Q A) : Prop :=
  ∀ w ∈ s.worlds, ∀ w' ∈ w.expand h w.fuel, I w'.db

omit [DecidableEq A] in
theorem expand_self (w : World Q A) (fuel : Nat) : w ∈ w.expand h fuel := by
  cases fuel <;> simp [World.expand]

theorem allow_holds (hI : Preserves h I) {s s' : State Q A} {r : Reply A}
    (hs : Holds h I s) (ha : s.allow h r = some s') : Holds h I s' := by
  simp only [State.allow] at ha
  split at ha
  · cases ha
  · simp only [Option.some.injEq] at ha
    subst ha
    intro w hw w' hw'
    have hw := mem_dedup hw
    simp only [List.mem_flatMap] at hw
    obtain ⟨v, hv, u, hu, hw⟩ := hw
    have hu' : I u.db := hs v hv u hu
    have : I w.db := by rw [World.answer_db u r w hw]; exact hu'
    exact World.expand_inv hI _ w this w' hw'

omit [DecidableEq A] in
theorem observe_holds (cfg : Config) (hI : Preserves h I) {s : State Q A} (c : Call Q)
    (hs : Holds h I s) : Holds h I (s.observe cfg c) := by
  intro w hw w' hw'
  simp only [State.observe, List.mem_map] at hw
  obtain ⟨v, hv, rfl⟩ := hw
  have hv' : I v.db := hs v hv v (expand_self v _)
  have : (v.send cfg c).db = v.db := by unfold World.send; split <;> rfl
  exact World.expand_inv hI _ _ (this ▸ hv') w' hw'

/-- **The invariant theorem.** If the start satisfies `I` and every transaction of the handler
keeps it, then after every run the model allows at `SERIALIZABLE`, with lost `COMMIT`s, failures
and calls taking effect at any moment, every database the store may hold satisfies `I`, also
once any call still outstanding or lost takes effect. -/
theorem invariant {σ : Signature} (cfg : Config) (port : Port σ Q A) {start : Db} (hstart : I start)
    (hI : Preserves h I) {events : List (Event σ)} {s : State Q A}
    (hrun : (outside cfg h start port).after events = some s) :
    ∀ w ∈ s.worlds, ∀ w' ∈ w.expand h w.fuel, I w'.db := by
  refine (outside cfg h start port).after_invariant (fun _ => True) (Holds h I) ?_ ?_ ?_
    (fun _ _ => trivial) hrun
  · intro w hw w' hw'
    simp only [outside, List.mem_singleton] at hw
    subst hw
    exact World.expand_inv hI _ _ hstart w' hw'
  · intro d x d' hd hx
    simp only [outside, Option.bind_eq_some_iff] at hx
    obtain ⟨r, -, hr⟩ := hx
    exact allow_holds hI hd hr
  · intro d out hd _
    simp only [outside]
    split
    · exact observe_holds cfg hI _ hd
    · exact hd

end Model

end Lanes.Db
