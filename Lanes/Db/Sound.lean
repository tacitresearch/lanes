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
leaves the database as it was (`Op.apply_read`), that a write changes only its own table
(`Op.rows_apply`), what each write leaves of its table (`Op.insert_rows`, `Op.update_rows`,
`Op.delete_rows`), and that a lookup that found nothing means no row has those values
(`Scan.run_eq_nil`, `Scan.matches_lookup`).
-/

@[expose] public section

namespace Lanes.Db

variable {Q A : Type}

/-- Every transaction of the handler keeps `I`. -/
def Preserves (h : Handler Q A) (I : Db → Prop) : Prop :=
  ∀ q db a db', I db → (h q).run db = .ok (a, db') → I db'

/-! ## Transactions -/

theorem Op.apply_read (o : Op) (hread : o.writes = false) {db : Db} {r : o.Ret} {db' : Db}
    (h : o.apply db = .ok (r, db')) : db' = db := by
  unfold Op.apply at h
  split at h
  · simp only [hread, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at h
    exact h.2.symm
  · cases h


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

theorem run_op_ok_inv {α : Type} {o : Op} {k : o.Ret → Txn α} {db : Db} {x : α × Db}
    (h : (Txn.op o k).run db = .ok x) : ∃ r db₁, o.apply db = .ok (r, db₁) ∧ (k r).run db₁ = .ok x := by
  cases ha : o.apply db with
  | error e => rw [run_op_error _ ha] at h; cases h
  | ok p => exact ⟨p.1, p.2, rfl, by rw [run_op_ok _ ha] at h; exact h⟩

/-- One operation, as a transaction: its meaning. -/
theorem run_single {o : Op} {db : Db} {r : o.Ret} {db' : Db}
    (h : (Txn.op o Txn.pure).run db = .ok (r, db')) : o.apply db = .ok (r, db') := by
  obtain ⟨r', db₁, ha, hk⟩ := run_op_ok_inv h
  simp only [run, Except.ok.injEq] at hk
  rw [ha, hk]

theorem run_bind_ok_inv {α β : Type} {t : Txn α} {f : α → Txn β} {db : Db} {x : β × Db}
    (h : (t.bind f).run db = .ok x) : ∃ a db₁, t.run db = .ok (a, db₁) ∧ (f a).run db₁ = .ok x := by
  rw [run_bind] at h
  cases ht : t.run db with
  | error e => simp [ht] at h
  | ok p => exact ⟨p.1, p.2, rfl, by simpa [ht] using h⟩

/-- A transaction that only reads. -/
inductive Reads {α : Type} : Txn α → Prop where
  | pure (a : α) : Reads (.pure a)
  | abort (why : String) : Reads (.abort why)
  | op (o : Op) (k : o.Ret → Txn α) : o.writes = false → (∀ r, Reads (k r)) → Reads (.op o k)

theorem Reads.run {α : Type} {t : Txn α} (h : t.Reads) {db : Db} {a : α} {db' : Db}
    (hrun : t.run db = .ok (a, db')) : db' = db := by
  induction h generalizing db with
  | pure a => simp at hrun; exact hrun.2.symm
  | abort why => simp at hrun
  | op o k hw _ ih =>
    obtain ⟨r, db₁, ha, hk⟩ := run_op_ok_inv hrun
    rw [ih r hk, Op.apply_read o hw ha]

theorem Reads.bind {α β : Type} {t : Txn α} {f : α → Txn β} (ht : t.Reads) (hf : ∀ a, (f a).Reads) :
    (t.bind f).Reads := by
  induction ht with
  | pure a => exact hf a
  | abort why => exact .abort why
  | op o k hw _ ih => exact .op o _ hw ih

theorem Reads.mapM {α β : Type} (f : α → Txn β) (hf : ∀ a, (f a).Reads) :
    ∀ xs : List α, (xs.mapM f).Reads := by
  intro xs
  induction xs with
  | nil => exact .pure []
  | cons x xs ih =>
    simp only [List.mapM_cons]
    exact Reads.bind (hf x) fun b => Reads.bind ih fun bs => .pure _

theorem run_mapM_length {α β : Type} (f : α → Txn β) :
    ∀ (xs : List α) {db : Db} {ys : List β} {db' : Db}, (xs.mapM f).run db = .ok (ys, db') → ys.length = xs.length := by
  intro xs
  induction xs with
  | nil => intro db ys db' h; simp [List.mapM_nil] at h; simp [← h.1]
  | cons x xs ih =>
    intro db ys db' h
    simp only [List.mapM_cons, bind_eq] at h
    obtain ⟨b, db₁, -, h⟩ := run_bind_ok_inv h
    obtain ⟨bs, db₂, hbs, h⟩ := run_bind_ok_inv h
    simp at h
    rw [← h.1]
    simp [ih hbs]

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

theorem TableOf.decode_reads {α : Type} (t : TableOf α) (r : Row) : (t.decode r).Reads := by
  unfold TableOf.decode; split
  · exact .pure _
  · exact .abort _

theorem TableOf.scan_reads {α : Type} (t : TableOf α) (s : Scan) : (t.scan s).Reads :=
  Txn.Reads.bind (.op _ _ rfl fun _ => .pure _) fun rows => Txn.Reads.mapM _ t.decode_reads rows

theorem TableOf.lookup_reads {α : Type} (t : TableOf α) (i : Index) (vals : Row) (limit : Nat) :
    (t.lookup i vals limit).Reads :=
  Txn.Reads.bind (.op _ _ rfl fun _ => .pure _) fun rows => Txn.Reads.mapM _ t.decode_reads rows

theorem TableOf.get_reads {α : Type} (t : TableOf α) (key : Row) : (t.get key).Reads := by
  refine Txn.Reads.bind (.op _ _ rfl fun _ => .pure _) fun r => ?_
  cases r with
  | some r => exact Txn.Reads.bind (t.decode_reads r) fun _ => .pure _
  | none => exact .pure _

theorem TableOf.run_decode {α : Type} (t : TableOf α) {r : Row} {db : Db} {a : α} {db' : Db}
    (h : (t.decode r).run db = .ok (a, db')) : t.ofRow r = some a := by
  unfold TableOf.decode at h
  split at h
  · simp at h; rw [← h.1]; assumption
  · simp at h

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
once any call still outstanding or lost takes effect. The run may restart the process
(`Event.restart`): the store is outside it and sees nothing of a restart, and a call the process
forgot may still take effect. -/
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

/-! ## Properties of worlds

A property of a world may speak of its calls as well as its database: of the answer a call that
took effect will be given (`World.done`). `WorldInv` is what keeps one in every world the model
holds, also once any call still outstanding or lost takes effect (`world_invariant`). -/

/-- A property of worlds that every call taking effect, every answer and every call sent keeps. -/
structure WorldInv (h : Handler Q A) (J : World Q A → Prop) : Prop where
  effects : ∀ w, J w → ∀ w' ∈ w.effects h, J w'
  answer : ∀ w r, J w → ∀ w' ∈ w.answer r, J w'
  send : ∀ (cfg : Config) w c, J w → J (w.send cfg c)

/-- `J` holds of every world of the model, with every call that may still take effect applied. -/
def WorldHolds (h : Handler Q A) (J : World Q A → Prop) (s : State Q A) : Prop :=
  ∀ w ∈ s.worlds, ∀ w' ∈ w.expand h w.fuel, J w'

variable {J : World Q A → Prop}

theorem WorldInv.expand (hJ : WorldInv h J) :
    ∀ (fuel : Nat) (w : World Q A), J w → ∀ w' ∈ w.expand h fuel, J w' := by
  intro fuel
  induction fuel with
  | zero => intro w hw w' hw'; simp only [World.expand, List.mem_singleton] at hw'; exact hw' ▸ hw
  | succ fuel ih =>
    intro w hw w' hw'
    simp only [World.expand, List.mem_cons, List.mem_flatMap] at hw'
    rcases hw' with rfl | ⟨v, hv, hw'⟩
    · exact hw
    · exact ih v (hJ.effects w hw v hv) w' hw'

theorem WorldInv.allow (hJ : WorldInv h J) {s s' : State Q A} {r : Reply A}
    (hs : WorldHolds h J s) (ha : s.allow h r = some s') : WorldHolds h J s' := by
  simp only [State.allow] at ha
  split at ha
  · cases ha
  · simp only [Option.some.injEq] at ha
    subst ha
    intro w hw w' hw'
    have hw := mem_dedup hw
    simp only [List.mem_flatMap] at hw
    obtain ⟨v, hv, u, hu, hw⟩ := hw
    exact hJ.expand _ w (hJ.answer u r (hs v hv u hu) w hw) w' hw'

theorem WorldInv.observe (cfg : Config) (hJ : WorldInv h J) {s : State Q A} (c : Call Q)
    (hs : WorldHolds h J s) : WorldHolds h J (s.observe cfg c) := by
  intro w hw w' hw'
  simp only [State.observe, List.mem_map] at hw
  obtain ⟨v, hv, rfl⟩ := hw
  exact hJ.expand _ _ (hJ.send cfg v c (hs v hv v (expand_self v _))) w' hw'

/-- **Properties of worlds.** If the start's world satisfies `J`, and every call taking effect,
every answer and every call sent keeps it, it holds of every world the model allows after every
run, also once any call still outstanding or lost takes effect. -/
theorem world_invariant {σ : Signature} (cfg : Config) (port : Port σ Q A) {start : Db}
    (hJ : WorldInv h J) (hstart : J { db := start }) {events : List (Event σ)} {s : State Q A}
    (hrun : (outside cfg h start port).after events = some s) : WorldHolds h J s := by
  refine (outside cfg h start port).after_invariant (fun _ => True) (WorldHolds h J) ?_ ?_ ?_
    (fun _ _ => trivial) hrun
  · intro w hw w' hw'
    simp only [outside, List.mem_singleton] at hw
    subst hw
    exact hJ.expand _ _ hstart w' hw'
  · intro d x d' hd hx
    simp only [outside, Option.bind_eq_some_iff] at hx
    obtain ⟨r, -, hr⟩ := hx
    exact hJ.allow hd hr
  · intro d out hd _
    simp only [outside]
    split
    · exact hJ.observe cfg _ hd
    · exact hd

/-- The model always keeps some world: an answer no world allows is refused. -/
theorem worlds_ne_nil {σ : Signature} (cfg : Config) (port : Port σ Q A) {start : Db}
    {events : List (Event σ)} {s : State Q A}
    (hrun : (outside cfg h start port).after events = some s) : s.worlds ≠ [] := by
  refine (outside cfg h start port).after_invariant (fun _ => True) (fun s => s.worlds ≠ []) ?_ ?_ ?_
    (fun _ _ => trivial) hrun
  · simp [outside]
  · intro d x d' _ hx
    simp only [outside, Option.bind_eq_some_iff] at hx
    obtain ⟨r, -, hr⟩ := hx
    simp only [State.allow] at hr
    split at hr
    · cases hr
    · next hne => simp only [Option.some.injEq] at hr; subst hr; simpa using hne
  · intro d out hd _
    simp only [outside]
    split
    · simpa [State.observe] using hd
    · exact hd

/-- A world in which a committed answer comes had the call take effect with that answer, and
has the same database. -/
theorem World.answer_committed {w w' : World Q A} {id : Nat} {a : A}
    (h : w' ∈ w.answer ⟨id, .committed a⟩) : (id, a) ∈ w.done ∧ w'.db = w.db := by
  simp only [World.answer] at h
  split at h
  · next hc => simp at h; exact ⟨List.contains_iff_mem.mp hc, by rw [h]⟩
  · simp at h

theorem World.answer_done {w w' : World Q A} {r : Reply A} (h : w' ∈ w.answer r) :
    ∀ p ∈ w'.done, p ∈ w.done := by
  simp only [World.answer] at h
  split at h <;> (try split at h) <;> (try split at h) <;> simp at h <;> subst h <;>
    first | exact fun p hp => List.mem_of_mem_erase hp | exact fun p hp => hp

omit [DecidableEq Q] [DecidableEq A] in
theorem World.send_done (cfg : Config) (w : World Q A) (c : Call Q) :
    (w.send cfg c).db = w.db ∧ (w.send cfg c).done = w.done := by
  unfold World.send; split <;> exact ⟨rfl, rfl⟩

omit [DecidableEq A] in
/-- A world after a call takes effect: its database is one run of a call's transaction on the
world's, and its answers to come are those it had, with the answer of that call if it was
pending. -/
theorem World.mem_effects {w w' : World Q A} (hw : w' ∈ w.effects h) :
    (∃ c ∈ w.pending, ∃ a, (h c.request).run w.db = .ok (a, w'.db) ∧ w'.done = w.done ++ [(c.id, a)])
      ∨ ∃ q ∈ w.lost, ∃ a, (h q).run w.db = .ok (a, w'.db) ∧ w'.done = w.done := by
  simp only [World.effects, List.mem_append, List.mem_filterMap, Option.map_eq_some_iff] at hw
  rcases hw with ⟨c, hc, ⟨a, db⟩, hrun, rfl⟩ | ⟨q, hq, ⟨a, db⟩, hrun, rfl⟩
  · left
    refine ⟨c, hc, a, ?_, rfl⟩
    cases hr : (h c.request).run w.db with
    | error e => simp [hr, Except.toOption] at hrun
    | ok p => simp only [hr, Except.toOption, Option.some.injEq] at hrun; rw [hrun]
  · right
    refine ⟨q, hq, a, ?_, rfl⟩
    cases hr : (h q).run w.db with
    | error e => simp [hr, Except.toOption] at hrun
    | ok p => simp only [hr, Except.toOption, Option.some.injEq] at hrun; rw [hrun]

end Model

/-! ## Rows: what a proof of `Preserves` reads off an operation -/

theorem Value.compare_eq_iff (a b : Value) : a.compare b = .eq ↔ a = b := by
  cases a <;> cases b <;> simp [Value.compare, Value.rank, Int64.toInt_inj]

/-- A scan with a limit that found nothing: no row matches it. -/
theorem Scan.run_eq_nil (s : Scan) {rows : List Row} (h : s.run rows = []) (hlimit : 0 < s.limit) :
    ∀ r ∈ rows, s.matches r = false := by
  unfold Scan.run at h
  rw [List.take_eq_nil_iff] at h
  rcases h with h | h
  · omega
  · have hlen := List.length_mergeSort (le := s.before) (rows.filter s.matches)
    rw [h] at hlen
    have hnil : rows.filter s.matches = [] := List.eq_nil_of_length_eq_zero hlen.symm
    intro r hr
    simpa using List.filter_eq_nil_iff.mp hnil r hr

theorem all_eq_iff_map (r : Row) : ∀ (cs : List Nat) (vs : Row), cs.length = vs.length →
    (((cs.zip vs).all fun (n, v) => (Cond.eq v).holds (r.getD n .null)) = true ↔ cs.map (r.getD · .null) = vs) := by
  intro cs
  induction cs with
  | nil => intro vs h; cases vs <;> simp_all
  | cons c cs ih =>
    intro vs h
    cases vs with
    | nil => simp at h
    | cons v vs =>
      have ih' := ih vs (by simpa using h)
      simp only [Cond.holds] at ih'
      simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true, List.map_cons, List.cons.injEq,
        Cond.holds, beq_iff_eq, Value.compare_eq_iff]
      rw [ih']

/-- A lookup by an index, with a value for each of its columns, finds the rows whose values in
the index are those. -/
theorem Scan.matches_lookup (t : Table) (i : Index) (vals : Row) (limit : Nat)
    (hlen : vals.length = i.columns.length) (r : Row) :
    Scan.matches { table := t, index := some i, eq := vals, limit } r = true ↔ i.project r = vals := by
  have hnone : i.columns[vals.length]? = none := by simp [hlen]
  simp only [Scan.matches, Scan.conds, Scan.columns, hnone, List.append_nil, List.all_map]
  unfold Index.project
  rw [← all_eq_iff_map r i.columns vals hlen.symm]
  rfl

theorem Table.insertSorted_perm (t : Table) (row : Row) :
    ∀ rows : List Row, (t.insertSorted row rows).Perm (row :: rows) := by
  intro rows
  induction rows with
  | nil => exact .refl _
  | cons r rest ih =>
    unfold Table.insertSorted
    split
    · exact .refl _
    · exact (List.Perm.cons r ih).trans (List.Perm.swap row r rest)

/-- What an insert leaves of a table's rows: the same rows, or the row added to rows none of
which has its key. -/
theorem Op.insert_rows (t : Table) (row : Row) (rows : List Row) :
    ((Op.insert t row).onRows rows).2 = rows ∨ (((Op.insert t row).onRows rows).2.Perm (row :: rows)
      ∧ ∀ x ∈ rows, t.keyOf x ≠ t.keyOf row) := by
  simp only [Op.onRows]
  split
  · exact .inl rfl
  · rename_i h
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true, List.any_eq_false] at h
    refine .inr ⟨t.insertSorted_perm row rows, fun x hx heq => ?_⟩
    have := h.1 x hx
    simp [Table.hasKey, heq] at this

/-- An update leaves the rows of other keys, and puts the row in place of the row of its key. -/
theorem Op.update_rows (t : Table) (row : Row) (rows : List Row) :
    ((Op.update t row).onRows rows).2 = rows ∨
      ((Op.update t row).onRows rows).2 = rows.map fun x => if t.hasKey (t.keyOf row) x then row else x := by
  simp only [Op.onRows]
  split
  · exact .inl rfl
  · exact .inr rfl

/-- An insert that answered `true` added the row to rows none of which has its key. -/
theorem Op.insert_onRows (t : Table) (row : Row) (rows : List Row)
    (h : ((Op.insert t row).onRows rows).1 = true) :
    ((Op.insert t row).onRows rows).2 = t.insertSorted row rows ∧ ∀ x ∈ rows, t.keyOf x ≠ t.keyOf row := by
  simp only [Op.onRows] at h ⊢
  split
  · next hc => simp [hc] at h
  · next hc =>
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true, List.any_eq_false] at hc
    refine ⟨rfl, fun x hx heq => ?_⟩
    have := hc.1 x hx
    simp [Table.hasKey, heq] at this

theorem Op.delete_rows (t : Table) (key : Row) (rows : List Row) :
    ((Op.delete t key).onRows rows).2 = rows.filter (!t.hasKey key ·) := rfl


/-! ## Unique indexes

The store refuses a write that would give two rows of distinct keys the values of a unique index
(`Table.clashes`), so a unique index stays unique under every operation on its table
(`Op.unique_apply`). -/

/-- No two rows of distinct keys have the same values in the index `i`. -/
def Table.Unique (t : Table) (i : Index) (rows : List Row) : Prop :=
  ∀ x ∈ rows, ∀ y ∈ rows, i.project x = i.project y → t.keyOf x = t.keyOf y

theorem Table.not_clashes {t : Table} {rows : List Row} {r : Row} (h : t.clashes rows r = false)
    {i : Index} (hi : i ∈ t.indexes) (hu : i.unique = true) :
    ∀ x ∈ rows, i.project x = i.project r → t.keyOf x = t.keyOf r := by
  intro x hx hp
  simp only [Table.clashes, List.any_eq_false, Bool.and_eq_true, not_and] at h
  by_cases hk : t.keyOf x = t.keyOf r
  · exact hk
  · exfalso
    apply h i hi hu
    rw [List.any_eq_true]
    exact ⟨x, hx, by simp [hk, hp]⟩

theorem Table.Unique.sub {t : Table} {i : Index} {rows rows' : List Row} (h : t.Unique i rows)
    (hsub : ∀ x ∈ rows', x ∈ rows) : t.Unique i rows' :=
  fun x hx y hy hp => h x (hsub x hx) y (hsub y hy) hp

theorem Table.Unique.add {t : Table} {i : Index} {rows rows' : List Row} {r : Row} (h : t.Unique i rows)
    (hsub : ∀ x ∈ rows', x = r ∨ x ∈ rows)
    (hr : ∀ x ∈ rows', x ≠ r → i.project x = i.project r → t.keyOf x = t.keyOf r) : t.Unique i rows' := by
  intro x hx y hy hp
  rcases hsub x hx with rfl | hx' <;> rcases hsub y hy with rfl | hy'
  · rfl
  · by_cases hyx : y = x
    · rw [hyx]
    · exact (hr y hy hyx hp.symm).symm
  · by_cases hxy : x = y
    · rw [hxy]
    · exact hr x hx hxy hp
  · exact h x hx' y hy' hp

theorem Table.mem_insertSorted (t : Table) (r : Row) (rows : List Row) :
    ∀ x, x ∈ t.insertSorted r rows ↔ x = r ∨ x ∈ rows := by
  intro x
  rw [(t.insertSorted_perm r rows).mem_iff, List.mem_cons]

/-- **A unique index stays unique.** Every operation on a table keeps each of its unique indexes
unique: a write that would break one does nothing. -/
theorem Op.unique_rows (o : Op) {i : Index} (hi : i ∈ o.table.indexes) (hu : i.unique = true)
    (rows : List Row) (h : o.table.Unique i rows) : o.table.Unique i (o.onRows rows).2 := by
  cases o with
  | get t k => exact h
  | scan s => exact h
  | insert t r =>
    simp only [Op.onRows]
    split
    · exact h
    · next hc =>
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hc
      refine h.add (fun x hx => (t.mem_insertSorted r rows x).mp hx) fun x hx hxr hp => ?_
      rcases (t.mem_insertSorted r rows x).mp hx with rfl | hx
      · exact absurd rfl hxr
      · exact Table.not_clashes hc.2 hi hu x hx hp
  | update t r =>
    simp only [Op.onRows]
    split
    · exact h
    · next hc =>
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hc
      have hmem : ∀ x ∈ rows.map (fun x => if t.hasKey (t.keyOf r) x then r else x), x = r ∨ x ∈ rows := by
        intro x hx
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        split
        · exact .inl rfl
        · exact .inr hy
      exact h.add hmem fun x hx _ hp => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        by_cases hk : t.hasKey (t.keyOf r) y = true
        · simp [hk]
        · simp only [hk, Bool.false_eq_true, ↓reduceIte] at hp ⊢
          exact Table.not_clashes hc.2 hi hu y hy hp
  | upsert t r =>
    simp only [Op.onRows]
    split
    · exact h
    · next hc =>
      simp only [Bool.not_eq_true] at hc
      have hmem : ∀ x ∈ t.insertSorted r (t.without (t.keyOf r) rows), x = r ∨ x ∈ rows := by
        intro x hx
        rcases (t.mem_insertSorted r _ x).mp hx with rfl | hx
        · exact .inl rfl
        · exact .inr (List.mem_filter.mp hx).1
      exact h.add hmem fun x hx hxr hp => by
        rcases (t.mem_insertSorted r _ x).mp hx with rfl | hx
        · exact absurd rfl hxr
        · exact Table.not_clashes hc hi hu x (List.mem_filter.mp hx).1 hp
  | delete t k => exact h.sub fun x hx => (List.mem_filter.mp hx).1

theorem Op.unique_apply (o : Op) {db : Db} {r : o.Ret} {db' : Db} (h : o.apply db = .ok (r, db'))
    (t : Table) (i : Index) (hi : i ∈ t.indexes) (hu : i.unique = true)
    (ht : o.table.name = t.name → o.table = t) (hU : t.Unique i (db.rows t.name)) :
    t.Unique i (db'.rows t.name) := by
  rw [Op.rows_apply o h]
  split
  · next hw =>
    obtain ⟨-, hn⟩ := hw
    have := ht hn.symm
    subst this
    rw [← hn]
    exact o.unique_rows hi hu _ hU
  · exact hU

/-- Every operation a transaction may ask satisfies `P`. -/
inductive Txn.All {α : Type} (P : Op → Prop) : Txn α → Prop where
  | pure (a : α) : Txn.All P (.pure a)
  | abort (why : String) : Txn.All P (.abort why)
  | op (o : Op) (k : o.Ret → Txn α) : P o → (∀ r, Txn.All P (k r)) → Txn.All P (.op o k)

namespace Txn.All

variable {P : Op → Prop}

theorem bind {α β : Type} {t : Txn α} {f : α → Txn β} (ht : t.All P) (hf : ∀ a, (f a).All P) :
    (t.bind f).All P := by
  induction ht with
  | pure a => exact hf a
  | abort why => exact .abort why
  | op o k hp _ ih => exact .op o _ hp ih

theorem map {α β : Type} {t : Txn α} (f : α → β) (ht : t.All P) : (f <$> t).All P :=
  bind ht fun a => .pure (f a)

theorem of_reads {α : Type} {t : Txn α} (ht : t.Reads) (hP : ∀ o, o.writes = false → P o) : t.All P := by
  induction ht with
  | pure a => exact .pure a
  | abort why => exact .abort why
  | op o k hw _ ih => exact .op o k (hP o hw) ih

theorem single {o : Op} (hp : P o) : (Txn.op o Txn.pure).All P := .op o _ hp fun r => .pure r

theorem mono {α : Type} {t : Txn α} {Q : Op → Prop} (ht : t.All P) (h : ∀ o, P o → Q o) : t.All Q := by
  induction ht with
  | pure a => exact .pure a
  | abort why => exact .abort why
  | op o k hp _ ih => exact .op o k (h o hp) ih

theorem mapM {α β : Type} (f : α → Txn β) (hf : ∀ a, (f a).All P) : ∀ xs : List α, (xs.mapM f).All P := by
  intro xs
  induction xs with
  | nil => exact .pure []
  | cons x xs ih =>
    simp only [List.mapM_cons]
    exact bind (hf x) fun b => bind ih fun bs => .pure _

/-- What every operation keeps, a transaction of them keeps. -/
theorem keeps {α : Type} {t : Txn α} (ht : t.All P) {I : Db → Prop}
    (hI : ∀ o, P o → ∀ db r db', I db → o.apply db = .ok (r, db') → I db') :
    ∀ db a db', I db → t.run db = .ok (a, db') → I db' := by
  induction ht with
  | pure a => intro db a' db' h hrun; simp at hrun; exact hrun.2 ▸ h
  | abort why => intro _ _ _ _ hrun; simp at hrun
  | op o k hp _ ih =>
    intro db a db' h hrun
    obtain ⟨r, db₁, ha, hk⟩ := run_op_ok_inv hrun
    exact ih r db₁ a db' (hI o hp db r db₁ h ha) hk

end Txn.All

/-- A unique index of a table stays unique under every transaction whose operations on a table
of its name are on that table. -/
theorem Txn.All.unique {α : Type} {t : Txn α} (tbl : Table) {i : Index} (hi : i ∈ tbl.indexes)
    (hu : i.unique = true) (ht : t.All fun o => o.table.name = tbl.name → o.table = tbl) :
    ∀ db a db', tbl.Unique i (db.rows tbl.name) → t.run db = .ok (a, db') → tbl.Unique i (db'.rows tbl.name) :=
  ht.keeps fun o ho _ _ _ hU ha => Op.unique_apply o ha tbl i hi hu ho hU

/-! ## Every row of a table -/

/-- The row a write asks to put in its table. -/
def Op.written : Op → Option Row
  | .insert _ r | .update _ r | .upsert _ r => some r
  | _ => none

/-- After an operation, every row of its table was there before, or is the one it wrote. -/
theorem Op.onRows_sub (o : Op) (rows : List Row) :
    ∀ x ∈ (o.onRows rows).2, x ∈ rows ∨ o.written = some x := by
  intro x hx
  cases o with
  | get t k => exact .inl hx
  | scan s => exact .inl hx
  | insert t r =>
    simp only [Op.onRows] at hx
    split at hx
    · exact .inl hx
    · rcases (t.mem_insertSorted r rows x).mp hx with rfl | hx
      · exact .inr rfl
      · exact .inl hx
  | update t r =>
    simp only [Op.onRows] at hx
    split at hx
    · exact .inl hx
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      split
      · exact .inr rfl
      · exact .inl hy
  | upsert t r =>
    simp only [Op.onRows] at hx
    split at hx
    · exact .inl hx
    · rcases (t.mem_insertSorted r _ x).mp hx with rfl | hx
      · exact .inr rfl
      · exact .inl (List.mem_filter.mp hx).1
  | delete t k => exact .inl (List.mem_filter.mp hx).1

/-- Every row of the table that reads back is a value `P` admits. -/
def TableOf.Every {α : Type} (t : TableOf α) (P : α → Prop) (db : Db) : Prop :=
  ∀ x ∈ db.rows t.table.name, ∀ a, t.ofRow x = some a → P a

/-- An operation on the table, or on another one, that writes only values `P` admits keeps every
row of the table admitted. -/
theorem TableOf.every_apply {α : Type} (t : TableOf α) {P : α → Prop} (o : Op)
    (ht : o.table.name = t.table.name → o.table = t.table)
    (hw : ∀ r, o.written = some r → ∀ a, t.ofRow r = some a → P a)
    {db : Db} {r : o.Ret} {db' : Db} (h : o.apply db = .ok (r, db')) (hP : t.Every P db) :
    t.Every P db' := by
  intro x hx a ha
  rw [Op.rows_apply o h] at hx
  split at hx
  · next hc =>
    have := ht hc.2.symm
    rw [← hc.2] at hx
    rcases o.onRows_sub _ x hx with hx | hx
    · exact hP x (hc.2 ▸ hx) a ha
    · exact hw x hx a ha
  · exact hP x hx a ha

end Lanes.Db
