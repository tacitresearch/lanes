/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Db.Sound
public import Lanes.Db.Jobs

/-!
What the transactions of a jobs table (`Lanes/Db/Jobs.lean`) do to it, for every database:

- **A job's work never changes.** Every transaction of the worker (`Queue.handler`), and
  `enqueue` and `cancel`, keeps each job of the table, with its id and work (`Queue.Keeps`):
  a claim and a finish change how far a job has got, never what it is. With an application whose
  transactions keep it too (`Queue.keeps_beside`), the jobs a database holds only grow.
- **A claim answers jobs of the table.** Every job a claim answers is a job of the table after
  it, with its id and work (`Queue.claimed_has`): what the worker performs, it read from a
  transaction that committed.
- **Bounds.** A claim answers at most `batch_max` jobs (`Queue.claim_length`); each job it
  answers is leased for one more attempt, never one past `attempts_max` (`Queue.claim_attempts`).
- **Every job due is taken.** A claim whose answer is short of its limit took every pending job
  due by its time (`Queue.claim_takes`).
- **Only the current attempt counts.** A finish with a lease that is not the job's changes
  nothing (`Queue.finish_stale`).
-/

@[expose] public section

namespace Lanes.Db.Jobs

variable {W : Type} (q : Queue W)

namespace Queue

/-- The jobs of the table. -/
def jobs (db : Db) : List (Job W) := (db.rows q.name).filterMap q.ofRow

/-- No two jobs of the table have one id and different work. -/
def Functional (db : Db) : Prop :=
  ∀ j ∈ q.jobs db, ∀ j' ∈ q.jobs db, j.id = j'.id → j.work = j'.work

/-- The table has a job with this id and this work. -/
def Has (db : Db) (id : Int64) (w : W) : Prop := ∃ j ∈ q.jobs db, j.id = id ∧ j.work = w

/-- A transaction keeps every job of the table, with its id and work, and no id comes to have
two works. -/
def Keeps {α : Type} (t : Txn α) : Prop :=
  ∀ db a db', q.Functional db → t.run db = .ok (a, db') →
    q.Functional db' ∧ ∀ id w, q.Has db id w → q.Has db' id w

variable {q}

theorem mem_jobs {db : Db} {j : Job W} : j ∈ q.jobs db ↔ ∃ x ∈ db.rows q.name, q.ofRow x = some j :=
  List.mem_filterMap

theorem ofRow_some {x : Row} {j : Job W} (h : q.ofRow x = some j) : ∃ rest, x = .int j.id :: rest := by
  unfold ofRow at h
  split at h
  · next id key work due status attempts lease every note =>
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨_, _, _, _, rfl⟩ := h
    exact ⟨_, rfl⟩
  · cases h

theorem ofRow_key {x : Row} {j : Job W} (h : q.ofRow x = some j) : x.getD 1 .null = .text j.key := by
  unfold ofRow at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨_, _, _, _, rfl⟩ := h
    rfl
  · cases h

theorem keyOf_of_ofRow {x : Row} {j : Job W} (h : q.ofRow x = some j) :
    q.table.keyOf x = [.int j.id] := by
  obtain ⟨rest, rfl⟩ := ofRow_some h
  simp [Table.keyOf, table]

theorem keyOf_toRow (j : Job W) : q.table.keyOf (q.toRow j) = [.int j.id] :=
  keyOf_of_ofRow (q.ofRow_toRow j)

theorem hasKey_iff {x : Row} {id : Int64} {j₀ : Job W} (h : q.ofRow x = some j₀) :
    q.table.hasKey [.int id] x = true ↔ j₀.id = id := by
  simp [Table.hasKey, keyOf_of_ofRow h]

theorem keeps_of_eq {db db' : Db} (h : q.jobs db' = q.jobs db) (hF : q.Functional db) :
    q.Functional db' ∧ ∀ id w, q.Has db id w → q.Has db' id w := by
  unfold Functional Has at *
  rw [h]
  exact ⟨hF, fun _ _ hh => hh⟩

theorem rows_empty (schema : Schema) (name : String) : (Db.empty schema).rows name = [] := by
  unfold Db.empty Db.rows
  induction schema with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.map_cons, List.lookup_cons]
    split <;> simp_all

/-- An empty table has no id twice. -/
theorem functional_empty (schema : Schema) : q.Functional (Db.empty schema) := by
  intro j hj
  simp [jobs, rows_empty] at hj

/-! ## Keeping the table -/

theorem Keeps.pure {α : Type} (a : α) : q.Keeps (Txn.pure a) := by
  intro db a' db' hf h
  simp only [Txn.run_pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  exact ⟨hf, fun _ _ h => h⟩

theorem Keeps.abort {α : Type} (why : String) : q.Keeps (Txn.abort why : Txn α) := by
  intro db a db' _ h
  simp at h

theorem Keeps.bind {α β : Type} {t : Txn α} {f : α → Txn β} (ht : q.Keeps t) (hf : ∀ a, q.Keeps (f a)) :
    q.Keeps (t.bind f) := by
  intro db b db' hF h
  obtain ⟨a, db₁, h₁, h₂⟩ := Txn.run_bind_ok_inv h
  obtain ⟨hF₁, hk₁⟩ := ht db a db₁ hF h₁
  obtain ⟨hF₂, hk₂⟩ := hf a db₁ b db' hF₁ h₂
  exact ⟨hF₂, fun id w hh => hk₂ id w (hk₁ id w hh)⟩

theorem Keeps.of_reads {α : Type} {t : Txn α} (ht : t.Reads) : q.Keeps t := by
  intro db a db' hF h
  obtain rfl := ht.run h
  exact ⟨hF, fun _ _ h => h⟩

theorem Keeps.map {α β : Type} {t : Txn α} (f : α → β) (ht : q.Keeps t) : q.Keeps (f <$> t) :=
  Keeps.bind ht fun a => Keeps.pure (f a)

theorem rows_other {o : Op} {db : Db} {r : o.Ret} {db' : Db} (h : o.apply db = .ok (r, db'))
    (ho : o.table.name = q.name) : db'.rows q.name = if o.writes then (o.onRows (db.rows q.name)).2 else db.rows q.name := by
  rw [Op.rows_apply o h, ho]
  by_cases hw : o.writes <;> simp [hw]

theorem insert_keeps (j : Job W) : q.Keeps (q.rows.insert j) := by
  intro db b db' hF h
  have ha := Txn.run_single h
  have hrows := rows_other ha rfl
  simp only [Op.writes, ↓reduceIte] at hrows
  change db'.rows q.name = ((Op.insert q.table (q.toRow j)).onRows (db.rows q.name)).2 at hrows
  rcases Op.insert_rows q.table (q.toRow j) (db.rows q.name) with hsame | ⟨hperm, hfresh⟩
  · have : q.jobs db' = q.jobs db := by
      unfold jobs; rw [hrows]; exact congrArg _ hsame
    exact keeps_of_eq this hF
  · have hmem : ∀ j', j' ∈ q.jobs db' ↔ j' = j ∨ j' ∈ q.jobs db := by
      intro j'
      rw [mem_jobs, mem_jobs]
      constructor
      · rintro ⟨x, hx, hj⟩
        rw [hrows] at hx
        rcases List.mem_cons.mp (hperm.mem_iff.mp hx) with rfl | hx
        · exact .inl (Option.some.inj ((q.ofRow_toRow j).symm.trans hj)).symm
        · exact .inr ⟨x, hx, hj⟩
      · rintro (rfl | ⟨x, hx, hj⟩)
        · exact ⟨q.toRow j', by rw [hrows]; exact hperm.mem_iff.mpr List.mem_cons_self, q.ofRow_toRow j'⟩
        · exact ⟨x, by rw [hrows]; exact hperm.mem_iff.mpr (List.mem_cons_of_mem _ hx), hj⟩
    have hnew : ∀ j₀ ∈ q.jobs db, j₀.id ≠ j.id := by
      intro j₀ hj₀ heq
      obtain ⟨x, hx, hj⟩ := mem_jobs.mp hj₀
      apply hfresh x hx
      rw [keyOf_of_ofRow hj, keyOf_toRow, heq]
    refine ⟨fun a ha b hb hab => ?_, fun id w ⟨j₀, hj₀, hid, hw⟩ => ⟨j₀, (hmem j₀).mpr (.inr hj₀), hid, hw⟩⟩
    rcases (hmem a).mp ha with rfl | ha' <;> rcases (hmem b).mp hb with rfl | hb'
    · rfl
    · exact absurd hab.symm (hnew b hb')
    · exact absurd hab (hnew a ha')
    · exact hF a ha' b hb' hab

/-- An update of a job to one with the id and work of a job the table has keeps it. -/
theorem update_keeps (j : Job W) {db : Db} {b : Bool} {db' : Db} (hF : q.Functional db)
    (hhas : q.Has db j.id j.work) (h : (q.rows.update j).run db = .ok (b, db')) :
    q.Functional db' ∧ ∀ id w, q.Has db id w → q.Has db' id w := by
  have ha := Txn.run_single h
  have hrows := rows_other ha rfl
  simp only [Op.writes, ↓reduceIte] at hrows
  change db'.rows q.name = ((Op.update q.table (q.toRow j)).onRows (db.rows q.name)).2 at hrows
  have hkey := keyOf_toRow (q := q) j
  rcases Op.update_rows q.table (q.toRow j) (db.rows q.name) with hsame | hmap
  · have : q.jobs db' = q.jobs db := by
      unfold jobs; rw [hrows]; exact congrArg _ hsame
    exact keeps_of_eq this hF
  · rw [hkey] at hmap
    obtain ⟨j₁, hj₁, hid₁, hw₁⟩ := hhas
    -- Every job the table holds with `j`'s id has its work.
    have hwork : ∀ j₀ ∈ q.jobs db, j₀.id = j.id → j₀.work = j.work := fun j₀ hj₀ hid =>
      (hF j₀ hj₀ j₁ hj₁ (hid.trans hid₁.symm)).trans hw₁
    have hmem : ∀ j', j' ∈ q.jobs db' ↔ (j' = j ∧ ∃ j₀ ∈ q.jobs db, j₀.id = j.id) ∨
        (j' ∈ q.jobs db ∧ j'.id ≠ j.id) := by
      intro j'
      rw [mem_jobs, hrows, hmap]
      constructor
      · rintro ⟨y, hy, hj⟩
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
        by_cases hk : q.table.hasKey [.int j.id] x = true
        · simp only [hk, ↓reduceIte] at hj
          obtain rfl := Option.some.inj ((q.ofRow_toRow j).symm.trans hj)
          cases hx' : q.ofRow x with
          | none =>
            obtain ⟨rest, rfl⟩ : ∃ rest, x = .int j.id :: rest := by
              simp [Table.hasKey, Table.keyOf, table] at hk
              match x, hk with
              | v :: rest, hk => exact ⟨rest, by simp_all⟩
            exact .inl ⟨rfl, j₁, hj₁, hid₁⟩
          | some j₀ => exact .inl ⟨rfl, j₀, mem_jobs.mpr ⟨x, hx, hx'⟩, (hasKey_iff hx').mp hk⟩
        · simp only [hk, Bool.false_eq_true, ↓reduceIte] at hj
          exact .inr ⟨mem_jobs.mpr ⟨x, hx, hj⟩, fun heq => hk ((hasKey_iff hj).mpr heq)⟩
      · rintro (⟨rfl, j₀, hj₀, hid⟩ | ⟨hj, hne⟩)
        · obtain ⟨x, hx, hx'⟩ := mem_jobs.mp hj₀
          exact ⟨q.toRow j', List.mem_map.mpr ⟨x, hx, by simp [(hasKey_iff hx').mpr hid]⟩, q.ofRow_toRow j'⟩
        · obtain ⟨x, hx, hx'⟩ := mem_jobs.mp hj
          refine ⟨x, List.mem_map.mpr ⟨x, hx, ?_⟩, hx'⟩
          have : ¬ q.table.hasKey [.int j.id] x = true := fun hk => hne ((hasKey_iff hx').mp hk)
          simp [this]
    refine ⟨fun a ha c hc hac => ?_, fun id w ⟨j₀, hj₀, hid, hw⟩ => ?_⟩
    · rcases (hmem a).mp ha with ⟨rfl, -⟩ | ⟨ha, hna⟩ <;> rcases (hmem c).mp hc with ⟨rfl, -⟩ | ⟨hc, hnc⟩
      · rfl
      · exact absurd hac.symm hnc
      · exact absurd hac hna
      · exact hF a ha c hc hac
    · by_cases hj : j₀.id = j.id
      · exact ⟨j, (hmem j).mpr (.inl ⟨rfl, j₀, hj₀, hj⟩), hj ▸ hid, (hwork j₀ hj₀ hj).symm.trans hw⟩
      · exact ⟨j₀, (hmem j₀).mpr (.inr ⟨hj₀, hj⟩), hid, hw⟩

/-! ## What a read gives -/

theorem mapM_decode_mem {rows : List Row} {db : Db} {js : List (Job W)} {db' : Db}
    (h : (rows.mapM q.rows.decode).run db = .ok (js, db')) : ∀ j ∈ js, ∃ x ∈ rows, q.ofRow x = some j := by
  induction rows generalizing db js db' with
  | nil => simp [List.mapM_nil] at h; obtain ⟨rfl, -⟩ := h; simp
  | cons x rest ih =>
    simp only [List.mapM_cons, Txn.bind_eq] at h
    obtain ⟨j₀, db₁, h₀, h⟩ := Txn.run_bind_ok_inv h
    obtain ⟨js', db₂, h₁, h⟩ := Txn.run_bind_ok_inv h
    simp only [Txn.pure_eq, Txn.run_pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · exact ⟨x, List.mem_cons_self, q.rows.run_decode h₀⟩
    · obtain ⟨y, hy, hy'⟩ := ih h₁ j hj
      exact ⟨y, List.mem_cons_of_mem _ hy, hy'⟩

theorem Scan.run_sub (s : Scan) (rows : List Row) : ∀ x ∈ s.run rows, x ∈ rows ∧ s.matches x = true := by
  intro x hx
  unfold Scan.run at hx
  have := (List.mergeSort_perm _ s.before).mem_iff.mp (List.mem_of_mem_take hx)
  exact List.mem_filter.mp this

theorem scan_mem {s : Scan} {db : Db} {js : List (Job W)} {db' : Db}
    (h : (q.rows.scan s).run db = .ok (js, db')) :
    db' = db ∧ ∀ j ∈ js, j ∈ q.jobs db ∧ ∃ x, q.ofRow x = some j ∧ ({ s with table := q.table } : Scan).matches x := by
  refine ⟨(TableOf.scan_reads _ _).run h, ?_⟩
  obtain ⟨rows, db₁, h₁, h₂⟩ := Txn.run_bind_ok_inv h
  obtain ⟨hr, rfl⟩ : rows = ({ s with table := q.table } : Scan).run (db.rows q.name) ∧ db₁ = db := by
    have := Txn.run_single h₁
    obtain ⟨-, hr⟩ := Op.apply_ok _ this
    exact ⟨hr, Op.apply_read _ rfl this⟩
  intro j hj
  obtain ⟨x, hx, hj'⟩ := mapM_decode_mem h₂ j hj
  rw [hr] at hx
  obtain ⟨hx, hm⟩ := Scan.run_sub _ _ x hx
  exact ⟨mem_jobs.mpr ⟨x, hx, hj'⟩, x, hj', hm⟩

theorem lookup_mem {i : Index} {vals : Row} {limit : Nat} {db : Db} {js : List (Job W)} {db' : Db}
    (h : (q.rows.lookup i vals limit).run db = .ok (js, db')) : db' = db ∧ ∀ j ∈ js, j ∈ q.jobs db := by
  refine ⟨(TableOf.lookup_reads _ _ _ _).run h, ?_⟩
  obtain ⟨rows, db₁, h₁, h₂⟩ := Txn.run_bind_ok_inv h
  have ha := Txn.run_single h₁
  obtain ⟨-, hr⟩ := Op.apply_ok _ ha
  obtain rfl := Op.apply_read _ rfl ha
  intro j hj
  obtain ⟨x, hx, hj'⟩ := mapM_decode_mem h₂ j hj
  rw [hr] at hx
  exact mem_jobs.mpr ⟨x, (Scan.run_sub _ _ x hx).1, hj'⟩

theorem get_mem {id : Int64} {db : Db} {r : Option (Job W)} {db' : Db}
    (h : (q.rows.get [.int id]).run db = .ok (r, db')) :
    db' = db ∧ ∀ j, r = some j → j ∈ q.jobs db ∧ j.id = id := by
  refine ⟨(TableOf.get_reads _ _).run h, ?_⟩
  intro j hj
  subst hj
  obtain ⟨row, db₁, h₁, h₂⟩ := Txn.run_bind_ok_inv h
  have ha := Txn.run_single h₁
  obtain ⟨-, hr⟩ := Op.apply_ok _ ha
  obtain rfl := Op.apply_read _ rfl ha
  cases row with
  | none => simp at h₂
  | some x =>
    obtain ⟨j', db₂, h₃, h₄⟩ := Txn.run_bind_ok_inv h₂
    simp at h₄
    obtain ⟨rfl, -⟩ := h₄
    have hx := q.rows.run_decode h₃
    simp only [Op.onRows] at hr
    have hfind := List.find?_some hr.symm
    have hmem := List.mem_of_find?_eq_some hr.symm
    exact ⟨mem_jobs.mpr ⟨x, hmem, hx⟩, (hasKey_iff hx).mp hfind⟩

/-! ## The worker's transactions keep the table -/

theorem claimed_id (cfg : Config) (now : Int64) (j : Job W) : (cfg.claimed now j).id = j.id := by
  unfold Config.claimed; split <;> rfl

theorem claimed_work (cfg : Config) (now : Int64) (j : Job W) : (cfg.claimed now j).work = j.work := by
  unfold Config.claimed; split <;> rfl

theorem finished_id (cfg : Config) (now : Int64) (j : Job W) (v : Verdict) :
    (cfg.finished now j v).id = j.id := by
  unfold Config.finished; split <;> (try split) <;> rfl

theorem finished_work (cfg : Config) (now : Int64) (j : Job W) (v : Verdict) :
    (cfg.finished now j v).work = j.work := by
  unfold Config.finished; split <;> (try split) <;> rfl

theorem has_of_mem {db : Db} {j : Job W} (h : j ∈ q.jobs db) : q.Has db j.id j.work := ⟨j, h, rfl, rfl⟩

/-- Claiming jobs the table has keeps it, and answers jobs it has after, each a job claimed. -/
theorem claimAll_keeps (cfg : Config) (now : Int64) :
    ∀ (js : List (Job W)) {db : Db} {out : List (Job W)} {db' : Db}, q.Functional db →
      (∀ j ∈ js, q.Has db j.id j.work) → (q.claimAll cfg now js).run db = .ok (out, db') →
      q.Functional db' ∧ (∀ id w, q.Has db id w → q.Has db' id w) ∧
        ∀ j' ∈ out, q.Has db' j'.id j'.work ∧ ∃ j ∈ js, j' = cfg.claimed now j ∧ j'.status = .pending := by
  intro js
  induction js with
  | nil =>
    intro db out db' hF _ h
    simp only [claimAll, Txn.pure_eq, Txn.run_pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hF, fun _ _ h => h, by simp⟩
  | cons j js ih =>
    intro db out db' hF hhas h
    simp only [claimAll, Txn.bind_eq] at h
    obtain ⟨b, db₁, h₁, h⟩ := Txn.run_bind_ok_inv h
    obtain ⟨rest, db₂, h₂, h⟩ := Txn.run_bind_ok_inv h
    simp only [Txn.pure_eq, Txn.run_pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hj : q.Has db (cfg.claimed now j).id (cfg.claimed now j).work := by
      rw [claimed_id, claimed_work]; exact hhas j List.mem_cons_self
    obtain ⟨hF₁, hk₁⟩ := update_keeps _ hF hj h₁
    obtain ⟨hF₂, hk₂, hout⟩ := ih hF₁ (fun j' hj' => hk₁ _ _ (hhas j' (List.mem_cons_of_mem _ hj'))) h₂
    refine ⟨hF₂, fun id w hh => hk₂ id w (hk₁ id w hh), fun j' hj' => ?_⟩
    split at hj'
    · next hp =>
      rcases List.mem_cons.mp hj' with rfl | hj'
      · exact ⟨hk₂ _ _ (hk₁ _ _ hj), j, List.mem_cons_self, rfl, hp⟩
      · obtain ⟨hh, j₀, hj₀, heq, hst⟩ := hout j' hj'
        exact ⟨hh, j₀, List.mem_cons_of_mem _ hj₀, heq, hst⟩
    · obtain ⟨hh, j₀, hj₀, heq, hst⟩ := hout j' hj'
      exact ⟨hh, j₀, List.mem_cons_of_mem _ hj₀, heq, hst⟩

theorem claim_keeps (cfg : Config) (now : Int64) (limit : Nat) {db : Db} {out : List (Job W)} {db' : Db}
    (hF : q.Functional db) (h : (q.claim cfg now limit).run db = .ok (out, db')) :
    q.Functional db' ∧ (∀ id w, q.Has db id w → q.Has db' id w) ∧
      ∀ j' ∈ out, q.Has db' j'.id j'.work ∧ ∃ j ∈ q.jobs db, j' = cfg.claimed now j ∧ j'.status = .pending := by
  simp only [claim, Txn.bind_eq] at h
  obtain ⟨js, db₁, h₁, h₂⟩ := Txn.run_bind_ok_inv h
  obtain ⟨rfl, hjs⟩ := scan_mem h₁
  obtain ⟨hF', hk, hout⟩ := claimAll_keeps cfg now js hF (fun j hj => has_of_mem (hjs j hj).1) h₂
  refine ⟨hF', hk, fun j' hj' => ?_⟩
  obtain ⟨hh, j, hj, heq, hst⟩ := hout j' hj'
  exact ⟨hh, j, (hjs j hj).1, heq, hst⟩

theorem keeps_pure_run {α : Type} {a b : α} {db db' : Db} (hF : q.Functional db)
    (h : (Txn.pure a).run db = .ok (b, db')) : q.Functional db' ∧ ∀ id w, q.Has db id w → q.Has db' id w :=
  Keeps.pure a db b db' hF h

theorem finish_keeps (cfg : Config) (id lease now : Int64) (v : Verdict) :
    q.Keeps (q.finish cfg id lease now v) := by
  intro db b db' hF h
  simp only [finish, Txn.bind_eq] at h
  obtain ⟨r, db₁, h₁, h₂⟩ := Txn.run_bind_ok_inv h
  obtain ⟨rfl, hr⟩ := get_mem h₁
  cases r with
  | none => exact keeps_pure_run hF h₂
  | some j =>
    obtain ⟨hj, -⟩ := hr j rfl
    simp only at h₂
    split at h₂
    · refine update_keeps _ hF ?_ h₂
      rw [finished_id, finished_work]; exact has_of_mem hj
    · exact keeps_pure_run hF h₂

theorem cancel_keeps (key : String) : q.Keeps (q.cancel key) := by
  intro db b db' hF h
  simp only [cancel, Txn.bind_eq] at h
  obtain ⟨js, db₁, h₁, h₂⟩ := Txn.run_bind_ok_inv h
  obtain ⟨rfl, hjs⟩ := lookup_mem h₁
  cases js with
  | nil => exact keeps_pure_run hF h₂
  | cons j _ =>
    simp only at h₂
    split at h₂
    · exact update_keeps { j with status := .cancelled, lease := j.lease + 1 } hF
        (⟨j, hjs j List.mem_cons_self, rfl, rfl⟩) h₂
    · exact keeps_pure_run hF h₂

theorem nextId_reads : q.nextId.Reads :=
  Txn.Reads.bind (TableOf.scan_reads _ _) fun js => by cases js <;> exact .pure _

theorem enqueue_keeps (key : String) (work : W) (due every : Int64) :
    q.Keeps (q.enqueue key work due every) := by
  refine Keeps.bind (Keeps.of_reads (TableOf.lookup_reads _ _ _ _)) fun js => ?_
  cases js with
  | cons j _ => exact Keeps.pure _
  | nil =>
    refine Keeps.bind (Keeps.of_reads nextId_reads) fun id => ?_
    refine Keeps.bind (insert_keeps _) fun b => ?_
    cases b
    · exact Keeps.abort _
    · exact Keeps.pure _

/-- Every transaction of the worker keeps the table. -/
theorem handler_keeps (cfg : Config) (r : Req) : q.Keeps (q.handler cfg r) := by
  cases r with
  | claim now limit =>
    refine Keeps.map _ fun db a db' hF h => ?_
    obtain ⟨hF', hk, -⟩ := claim_keeps cfg now limit hF h
    exact ⟨hF', hk⟩
  | finish id lease now v => exact Keeps.map _ (finish_keeps cfg id lease now v)

/-- An application whose transactions keep the table, and the worker's, keep it. -/
theorem keeps_beside {Q A : Type} {app : Handler Q A} (happ : ∀ x, q.Keeps (app x)) (cfg : Config) :
    ∀ x, q.Keeps (beside app (q.handler cfg) x)
  | .inl x => Keeps.map _ (happ x)
  | .inr r => Keeps.map _ (handler_keeps cfg r)

theorem run_map {α β : Type} (f : α → β) (t : Txn α) {db : Db} {b : β} {db' : Db}
    (h : (f <$> t).run db = .ok (b, db')) : ∃ a, t.run db = .ok (a, db') ∧ b = f a := by
  obtain ⟨a, db₁, h₁, h₂⟩ := Txn.run_bind_ok_inv (t := t) (f := fun a => Txn.pure (f a)) h
  simp only [Txn.run_pure, Except.ok.injEq, Prod.mk.injEq] at h₂
  obtain ⟨rfl, rfl⟩ := h₂
  exact ⟨a, h₁, rfl⟩

/-- **A claim answers jobs of the table.** A transaction beside the worker's that answers jobs
claimed is a claim, and every job it answers is a job of the table after it, with its id and
work. -/
theorem claimed_has {Q A : Type} (app : Handler Q A) (cfg : Config) (x : Q ⊕ Req) {db : Db}
    {js : List (Job W)} {db' : Db} (hF : q.Functional db)
    (h : (beside app (q.handler cfg) x).run db = .ok (.inr (.claimed js), db')) :
    ∀ j ∈ js, q.Has db' j.id j.work := by
  cases x with
  | inl x =>
    obtain ⟨a, -, ha⟩ := run_map _ _ h
    cases ha
  | inr r =>
    obtain ⟨a, h, ha⟩ := run_map _ _ h
    cases ha
    cases r with
    | claim now limit =>
      simp only [Queue.handler] at h
      obtain ⟨out, h, hout⟩ := run_map _ _ h
      cases hout
      exact fun j hj => ((claim_keeps cfg now limit hF h).2.2 j hj).1
    | finish id lease now v =>
      simp only [Queue.handler] at h
      obtain ⟨out, -, hout⟩ := run_map _ _ h
      cases hout


/-! ## Bounds, and every job due taken -/

theorem claimAll_length (cfg : Config) (now : Int64) :
    ∀ (js : List (Job W)) {db : Db} {out : List (Job W)} {db' : Db},
      (q.claimAll cfg now js).run db = .ok (out, db') → out.length ≤ js.length := by
  intro js
  induction js with
  | nil =>
    intro db out db' h
    simp only [claimAll, Txn.pure_eq, Txn.run_pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp
  | cons j js ih =>
    intro db out db' h
    simp only [claimAll, Txn.bind_eq] at h
    obtain ⟨b, db₁, -, h⟩ := Txn.run_bind_ok_inv h
    obtain ⟨rest, db₂, h₂, h⟩ := Txn.run_bind_ok_inv h
    simp only [Txn.pure_eq, Txn.run_pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have := ih h₂
    split <;> simp <;> omega

/-- Every job claimed for an attempt is answered. -/
theorem claimAll_answers (cfg : Config) (now : Int64) :
    ∀ (js : List (Job W)) {db : Db} {out : List (Job W)} {db' : Db},
      (q.claimAll cfg now js).run db = .ok (out, db') →
        ∀ j ∈ js, (cfg.claimed now j).status = .pending → cfg.claimed now j ∈ out := by
  intro js
  induction js with
  | nil => intro _ _ _ _ j hj; cases hj
  | cons j js ih =>
    intro db out db' h j' hj' hp
    simp only [claimAll, Txn.bind_eq] at h
    obtain ⟨b, db₁, -, h⟩ := Txn.run_bind_ok_inv h
    obtain ⟨rest, db₂, h₂, h⟩ := Txn.run_bind_ok_inv h
    simp only [Txn.pure_eq, Txn.run_pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    rcases List.mem_cons.mp hj' with rfl | hj'
    · simp [hp]
    · have := ih h₂ j' hj' hp
      split
      · exact List.mem_cons_of_mem _ this
      · exact this

theorem scan_length {s : Scan} {db : Db} {js : List (Job W)} {db' : Db}
    (h : (q.rows.scan s).run db = .ok (js, db')) : js.length ≤ s.limit := by
  obtain ⟨rows, db₁, h₁, h₂⟩ := Txn.run_bind_ok_inv h
  obtain ⟨-, hr⟩ := Op.apply_ok _ (Txn.run_single h₁)
  have hr' : rows = Scan.run { s with table := q.table } (db.rows q.name) := hr
  rw [Txn.run_mapM_length _ _ h₂, hr']
  exact List.length_take_le _ _

/-- **A claim is bounded.** It answers at most `batch_max` jobs, and at most its limit. -/
theorem claim_length (cfg : Config) (now : Int64) (limit : Nat) {db : Db} {out : List (Job W)}
    {db' : Db} (h : (q.claim cfg now limit).run db = .ok (out, db')) :
    out.length ≤ cfg.batch_max ∧ out.length ≤ limit := by
  simp only [claim, Txn.bind_eq] at h
  obtain ⟨js, db₁, h₁, h₂⟩ := Txn.run_bind_ok_inv h
  have h1 := scan_length h₁
  have h2 := claimAll_length cfg now js h₂
  simp only [due] at h1
  omega

theorem claimed_pending {cfg : Config} {now : Int64} {j : Job W}
    (h : (cfg.claimed now j).status = .pending) :
    cfg.spent j = false ∧ (cfg.claimed now j).attempts = j.attempts + 1 ∧
      (cfg.claimed now j).due_ms = now + Int64.ofNat cfg.lease_ms := by
  unfold Config.claimed at h ⊢
  split at h
  · simp at h
  · next hs => simp [hs]

/-- **Attempts are bounded.** Each job a claim answers is leased for one more attempt of a job
whose attempts were not spent: the attempts of a run never pass `attempts_max`. -/
theorem claim_attempts (cfg : Config) (now : Int64) (limit : Nat) {db : Db} {out : List (Job W)}
    {db' : Db} (hF : q.Functional db) (h : (q.claim cfg now limit).run db = .ok (out, db')) :
    ∀ j' ∈ out, ∃ j ∈ q.jobs db, j.attempts.toInt.toNat < cfg.attempts_max ∧
      j'.attempts = j.attempts + 1 ∧ j'.id = j.id ∧ j'.lease = j.lease + 1 := by
  intro j' hj'
  obtain ⟨j, hj, heq, hst⟩ := ((claim_keeps cfg now limit hF h).2.2 j' hj').2
  subst heq
  obtain ⟨hs, ha, -⟩ := claimed_pending hst
  refine ⟨j, hj, ?_, ha, claimed_id cfg now j, ?_⟩
  · simpa [Config.spent] using hs
  · unfold Config.claimed; split <;> rfl

theorem Scan.run_all (s : Scan) (rows : List Row) (h : (rows.filter s.matches).length ≤ s.limit) :
    ∀ x ∈ rows, s.matches x = true → x ∈ s.run rows := by
  intro x hx hm
  unfold Scan.run
  rw [List.take_of_length_le (by simpa using h)]
  exact List.mem_mergeSort.mpr (List.mem_filter.mpr ⟨hx, hm⟩)

theorem mapM_decode_all {rows : List Row} {db : Db} {js : List (Job W)} {db' : Db}
    (h : (rows.mapM q.rows.decode).run db = .ok (js, db')) : ∀ x ∈ rows, ∀ j, q.ofRow x = some j → j ∈ js := by
  induction rows generalizing db js db' with
  | nil => intro x hx; cases hx
  | cons x rest ih =>
    simp only [List.mapM_cons, Txn.bind_eq] at h
    obtain ⟨j₀, db₁, h₀, h⟩ := Txn.run_bind_ok_inv h
    obtain ⟨js', db₂, h₁, h⟩ := Txn.run_bind_ok_inv h
    simp only [Txn.pure_eq, Txn.run_pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    intro y hy j hj
    rcases List.mem_cons.mp hy with rfl | hy
    · have h₀' : q.ofRow y = some j₀ := q.rows.run_decode h₀
      rw [h₀'] at hj
      obtain rfl := Option.some.inj hj
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h₁ y hy j hj)

/-- A pending job due by `now_ms` is one the claim's scan looks for. -/
theorem due_matches {now : Int64} {limit : Nat} {x : Row} {j : Job W} (hx : q.ofRow x = some j)
    (hp : j.status = .pending) (hdue : j.due_ms.toInt ≤ now.toInt) :
    ({ q.due now limit with table := q.table } : Scan).matches x = true := by
  unfold ofRow at hx
  split at hx
  · next id key work dueV status attempts lease every note =>
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hx
    obtain ⟨w, -, st, hst, rfl⟩ := hx
    simp only at hp hdue
    subst hp
    have : status = 0 := by
      unfold Status.ofCode at hst
      split at hst
      · assumption
      · split at hst <;> (try split at hst) <;> (try split at hst) <;> simp at hst
    subst this
    simp [Scan.matches, Scan.conds, Scan.columns, due, byDue, Cond.holds, Value.compare, Status.code,
      Int.compare_eq_gt]
    omega
  · cases hx

/-- **Every job due is taken.** A claim whose scan finds no more pending jobs due by its time
than its limit leases every one whose attempts are not spent, and answers it, for an attempt. -/
theorem claim_takes (cfg : Config) (now : Int64) (limit : Nat) {db : Db} {out : List (Job W)}
    {db' : Db} (h : (q.claim cfg now limit).run db = .ok (out, db'))
    (hroom : ((db.rows q.name).filter
      ({ q.due now (min limit (min cfg.batch_max Scan.limit_max)) with table := q.table } : Scan).matches).length
        ≤ min limit (min cfg.batch_max Scan.limit_max)) :
    ∀ j ∈ q.jobs db, j.status = .pending → j.due_ms.toInt ≤ now.toInt → cfg.spent j = false →
      cfg.claimed now j ∈ out := by
  intro j hj hp hdue hs
  simp only [claim, Txn.bind_eq] at h
  obtain ⟨js, db₁, h₁, h₂⟩ := Txn.run_bind_ok_inv h
  obtain ⟨rows, db₂, h₃, h₄⟩ := Txn.run_bind_ok_inv h₁
  have ha := Txn.run_single h₃
  obtain ⟨-, hr⟩ := Op.apply_ok _ ha
  obtain rfl := Op.apply_read _ rfl ha
  obtain ⟨x, hx, hx'⟩ := mem_jobs.mp hj
  have hm := due_matches (limit := min limit (min cfg.batch_max Scan.limit_max)) hx' hp hdue
  have hin : x ∈ rows := by
    rw [hr]; exact Scan.run_all _ _ hroom x hx hm
  have hjs := mapM_decode_all h₄ x hin j hx'
  refine claimAll_answers cfg now js h₂ j hjs ?_
  unfold Config.claimed; simp [hs, hp]

/-- **Only the current attempt counts.** A finish whose lease is not the job's changes nothing
and answers that it was not counted. -/
theorem finish_stale (cfg : Config) {id lease now : Int64} {v : Verdict} {db : Db} {b : Bool}
    {db' : Db} (hstale : ∀ j ∈ q.jobs db, j.id = id → j.lease ≠ lease)
    (h : (q.finish cfg id lease now v).run db = .ok (b, db')) : db' = db ∧ b = false := by
  simp only [finish, Txn.bind_eq] at h
  obtain ⟨r, db₁, h₁, h₂⟩ := Txn.run_bind_ok_inv h
  obtain ⟨rfl, hr⟩ := get_mem h₁
  cases r with
  | none => simp at h₂; exact ⟨h₂.2.symm, h₂.1⟩
  | some j =>
    obtain ⟨hj, hid⟩ := hr j rfl
    simp only at h₂
    split at h₂
    · next hc => exact absurd hc.2 (hstale j hj hid)
    · simp at h₂; exact ⟨h₂.2.symm, h₂.1⟩


/-! ## One job per key -/

/-- No two jobs of distinct ids hold one key. -/
def KeyUnique (db : Db) : Prop := q.table.Unique byKey (db.rows q.name)

/-- An operation on a table named as the jobs table is on the jobs table. -/
def OnTable (o : Op) : Prop := o.table.name = q.name → o.table = q.table

theorem keyUnique_jobs {db : Db} (h : q.KeyUnique db) :
    ∀ j ∈ q.jobs db, ∀ j' ∈ q.jobs db, j.key = j'.key → j.id = j'.id := by
  intro j hj j' hj' hk
  obtain ⟨x, hx, hxj⟩ := mem_jobs.mp hj
  obtain ⟨y, hy, hyj⟩ := mem_jobs.mp hj'
  have hp : byKey.project x = byKey.project y := by
    simp only [Index.project, byKey, List.map_cons, List.map_nil, ofRow_key hxj, ofRow_key hyj, hk]
  have := h x hx y hy hp
  rw [keyOf_of_ofRow hxj, keyOf_of_ofRow hyj] at this
  simpa using this

variable (q)

theorem decode_all (r : Row) : (q.rows.decode r).All q.OnTable := by
  unfold TableOf.decode; split
  · exact .pure _
  · exact .abort _

theorem get_all (key : Row) : (q.rows.get key).All q.OnTable :=
  Txn.All.bind (Txn.All.single fun _ => rfl) fun r => by
    cases r with
    | some x => exact Txn.All.bind (decode_all q x) fun _ => .pure _
    | none => exact .pure _

theorem scan_all (s : Scan) : (q.rows.scan s).All q.OnTable :=
  Txn.All.bind (Txn.All.single fun _ => rfl) fun rows => Txn.All.mapM _ (decode_all q) rows

theorem lookup_all (i : Index) (vals : Row) (limit : Nat) : (q.rows.lookup i vals limit).All q.OnTable :=
  Txn.All.bind (Txn.All.single fun _ => rfl) fun rows => Txn.All.mapM _ (decode_all q) rows

theorem insert_all (j : Job W) : (q.rows.insert j).All q.OnTable := Txn.All.single fun _ => rfl

theorem update_all (j : Job W) : (q.rows.update j).All q.OnTable := Txn.All.single fun _ => rfl

theorem nextId_all : q.nextId.All q.OnTable :=
  Txn.All.bind (scan_all q _) fun js => by cases js <;> exact .pure _

theorem enqueue_all (key : String) (work : W) (due every : Int64) :
    (q.enqueue key work due every).All q.OnTable := by
  refine Txn.All.bind (lookup_all q _ _ _) fun js => ?_
  cases js with
  | cons j _ => exact .pure _
  | nil =>
    refine Txn.All.bind (nextId_all q) fun id => Txn.All.bind (insert_all q _) fun b => ?_
    cases b
    · exact .abort _
    · exact .pure _

theorem cancel_all (key : String) : (q.cancel key).All q.OnTable := by
  refine Txn.All.bind (lookup_all q _ _ _) fun js => ?_
  cases js with
  | nil => exact .pure _
  | cons j _ =>
    simp only
    split
    · exact update_all q _
    · exact .pure _

theorem claimAll_all (cfg : Config) (now : Int64) : ∀ js, (q.claimAll cfg now js).All q.OnTable
  | [] => .pure _
  | _ :: js => Txn.All.bind (update_all q _) fun _ =>
      Txn.All.bind (claimAll_all cfg now js) fun _ => .pure _

theorem finish_all (cfg : Config) (id lease now : Int64) (v : Verdict) :
    (q.finish cfg id lease now v).All q.OnTable := by
  refine Txn.All.bind (get_all q _) fun r => ?_
  cases r with
  | none => exact .pure _
  | some j =>
    simp only
    split
    · exact update_all q _
    · exact .pure _

theorem handler_all (cfg : Config) (r : Req) : (q.handler cfg r).All q.OnTable := by
  cases r with
  | claim now limit => exact Txn.All.map _ (Txn.All.bind (scan_all q _) fun js => claimAll_all q cfg now js)
  | finish id lease now v => exact Txn.All.map _ (finish_all q cfg id lease now v)

variable {q}

/-- **One job per key.** Beside an application whose operations on a table of the jobs table's
name are on that table, every database the store may hold, after every run and once any call
still outstanding or lost takes effect, has no two jobs of distinct ids under one key: at most
one job, and so at most one current attempt (`finish_stale`), per key. -/
theorem one_per_key [DecidableEq W] {Q A : Type} [DecidableEq Q] [DecidableEq A] {app : Handler Q A}
    (happ : ∀ x, (app x).All q.OnTable) (cfg : Config) {σ : Signature} (dbcfg : Db.Config)
    (port : Db.Port σ (Q ⊕ Req) (A ⊕ Ans W)) {start : Db} (hstart : q.KeyUnique start)
    {events : List (Event σ)} {s : Db.State (Q ⊕ Req) (A ⊕ Ans W)}
    (hrun : (Db.outside dbcfg (beside app (q.handler cfg)) start port).after events = some s) :
    ∀ w ∈ s.worlds, ∀ w' ∈ w.expand (beside app (q.handler cfg)) w.fuel,
      ∀ j ∈ q.jobs w'.db, ∀ j' ∈ q.jobs w'.db, j.key = j'.key → j.id = j'.id := by
  have hP : Preserves (beside app (q.handler cfg)) q.KeyUnique := by
    intro x db a db' hU hrun
    have hall : (beside app (q.handler cfg) x).All q.OnTable := by
      cases x with
      | inl x => exact Txn.All.map _ (happ x)
      | inr r => exact Txn.All.map _ (handler_all q cfg r)
    exact Txn.All.unique q.table (i := byKey) (by simp [table]) rfl hall db a db' hU hrun
  intro w hw w' hw'
  exact keyUnique_jobs (Db.invariant dbcfg port hstart hP hrun w hw w' hw')

theorem keyUnique_empty (schema : Schema) : q.KeyUnique (Db.empty schema) := by
  intro x hx
  simp [rows_empty] at hx


/-! ## Transactions that only add jobs

An application's transaction usually touches the jobs table in one way: it adds jobs, through
`enqueue`. `Adds enq` says so of an operation: it is on another table, reads the jobs table, or
inserts a job `enq` admits. A transaction all of whose operations add (`Txn.All (q.Adds enq)`)
keeps the table (`keeps_of_adds`), is on the table when it touches its name (`onTable_of_adds`),
and keeps every property of each job that `enq` gives (`fixed_of_adds`). -/

variable (q)

/-- The operation is on another table, reads the jobs table, or inserts a job `enq` admits. -/
def Adds (enq : Job W → Prop) (o : Op) : Prop :=
  o.table.name ≠ q.name ∨ (o.table = q.table ∧ o.writes = false) ∨ ∃ j, enq j ∧ o = .insert q.table (q.toRow j)

/-- Every job of the table has the property `P`. -/
def Fixed (P : Job W → Prop) (db : Db) : Prop := ∀ j ∈ q.jobs db, P j

variable {q}

theorem adds_rows {enq : Job W → Prop} {o : Op} (ho : q.Adds enq o) {db : Db} {r : o.Ret} {db' : Db}
    (h : o.apply db = .ok (r, db')) :
    db'.rows q.name = db.rows q.name ∨ ∃ j, enq j ∧ o = .insert q.table (q.toRow j) := by
  rcases ho with hn | ⟨-, hw⟩ | hins
  · left
    rw [Op.rows_apply o h]
    split
    · next hc => exact absurd hc.2.symm hn
    · rfl
  · left
    rw [Op.rows_apply o h]
    simp [hw]
  · exact .inr hins

theorem insert_run {j : Job W} {db : Db} {r : (Op.insert q.table (q.toRow j)).Ret} {db' : Db}
    (h : (Op.insert q.table (q.toRow j)).apply db = .ok (r, db')) : (q.rows.insert j).run db = .ok (r, db') :=
  (Txn.run_op_ok _ h).trans rfl

theorem keeps_of_adds {enq : Job W → Prop} {α : Type} {t : Txn α} (ht : t.All (q.Adds enq)) : q.Keeps t := by
  intro db₀ a db' hF h
  refine ht.keeps (I := fun db => q.Functional db ∧ ∀ id w, q.Has db₀ id w → q.Has db id w)
    (fun o ho db r db' ⟨hF, hk⟩ ha => ?_) db₀ a db' ⟨hF, fun _ _ h => h⟩ h
  rcases adds_rows ho ha with hsame | ⟨j, -, rfl⟩
  · have : q.jobs db' = q.jobs db := by unfold jobs; rw [hsame]
    obtain ⟨hF', hk'⟩ := keeps_of_eq this hF
    exact ⟨hF', fun id w hh => hk' id w (hk id w hh)⟩
  · obtain ⟨hF', hk'⟩ := insert_keeps j db r db' hF (insert_run ha)
    exact ⟨hF', fun id w hh => hk' id w (hk id w hh)⟩

theorem onTable_of_adds {enq : Job W → Prop} {α : Type} {t : Txn α} (ht : t.All (q.Adds enq)) :
    t.All q.OnTable :=
  ht.mono fun o ho hn => by
    rcases ho with hn' | ⟨ht, -⟩ | ⟨j, -, rfl⟩
    · exact absurd hn hn'
    · exact ht
    · rfl

theorem fixed_insert {P : Job W → Prop} {j : Job W} (hj : P j) {db : Db} {b : Bool} {db' : Db}
    (hP : q.Fixed P db) (h : (q.rows.insert j).run db = .ok (b, db')) : q.Fixed P db' := by
  have ha := Txn.run_single h
  have hrows := rows_other ha rfl
  simp only [Op.writes, ↓reduceIte] at hrows
  change db'.rows q.name = ((Op.insert q.table (q.toRow j)).onRows (db.rows q.name)).2 at hrows
  intro j' hj'
  obtain ⟨x, hx, hxj⟩ := mem_jobs.mp hj'
  rw [hrows] at hx
  rcases Op.insert_rows q.table (q.toRow j) (db.rows q.name) with hsame | ⟨hperm, -⟩
  · rw [hsame] at hx; exact hP j' (mem_jobs.mpr ⟨x, hx, hxj⟩)
  · rcases List.mem_cons.mp (hperm.mem_iff.mp hx) with rfl | hx
    · obtain rfl := Option.some.inj ((q.ofRow_toRow j).symm.trans hxj); exact hj
    · exact hP j' (mem_jobs.mpr ⟨x, hx, hxj⟩)

theorem fixed_of_adds {enq P : Job W → Prop} (henq : ∀ j, enq j → P j) {α : Type} {t : Txn α}
    (ht : t.All (q.Adds enq)) : ∀ db a db', q.Fixed P db → t.run db = .ok (a, db') → q.Fixed P db' :=
  ht.keeps fun o ho db r db' hP ha => by
    rcases adds_rows ho ha with hsame | ⟨j, hj, rfl⟩
    · intro j' hj'; unfold jobs at hj'; rw [hsame] at hj'; exact hP j' hj'
    · exact fixed_insert (henq j hj) hP (insert_run ha)

/-- A property of a job's id, key and work, which no claim, finish or cancel changes. -/
def Stable (P : Job W → Prop) : Prop :=
  ∀ j j' : Job W, j.id = j'.id → j.key = j'.key → j.work = j'.work → P j → P j'

theorem fixed_update {P : Job W → Prop} (j : Job W) {db : Db} {b : Bool} {db' : Db}
    (hP : q.Fixed P db) (hj : P j) (h : (q.rows.update j).run db = .ok (b, db')) : q.Fixed P db' := by
  have ha := Txn.run_single h
  have hrows := rows_other ha rfl
  simp only [Op.writes, ↓reduceIte] at hrows
  change db'.rows q.name = ((Op.update q.table (q.toRow j)).onRows (db.rows q.name)).2 at hrows
  intro j' hj'
  obtain ⟨x, hx, hxj⟩ := mem_jobs.mp hj'
  rw [hrows] at hx
  rcases Op.update_rows q.table (q.toRow j) (db.rows q.name) with hsame | hmap
  · rw [hsame] at hx; exact hP j' (mem_jobs.mpr ⟨x, hx, hxj⟩)
  · rw [hmap] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    split at hxj
    · obtain rfl := Option.some.inj ((q.ofRow_toRow j).symm.trans hxj); exact hj
    · exact hP j' (mem_jobs.mpr ⟨y, hy, hxj⟩)

theorem stable_claimed {P : Job W → Prop} (hs : Stable P) (cfg : Config) (now : Int64) {j : Job W}
    (hj : P j) : P (cfg.claimed now j) :=
  hs j _ (claimed_id cfg now j).symm (by unfold Config.claimed; split <;> rfl) (claimed_work cfg now j).symm hj

theorem claimAll_fixed {P : Job W → Prop} (hs : Stable P) (cfg : Config) (now : Int64) :
    ∀ (js : List (Job W)) {db : Db} {out : List (Job W)} {db' : Db}, q.Fixed P db → (∀ j ∈ js, P j) →
      (q.claimAll cfg now js).run db = .ok (out, db') → q.Fixed P db' := by
  intro js
  induction js with
  | nil =>
    intro db out db' hP _ h
    simp only [claimAll, Txn.pure_eq, Txn.run_pure, Except.ok.injEq, Prod.mk.injEq] at h
    exact h.2 ▸ hP
  | cons j js ih =>
    intro db out db' hP hin h
    simp only [claimAll, Txn.bind_eq] at h
    obtain ⟨b, db₁, h₁, h⟩ := Txn.run_bind_ok_inv h
    obtain ⟨rest, db₂, h₂, h⟩ := Txn.run_bind_ok_inv h
    simp only [Txn.pure_eq, Txn.run_pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ih (fixed_update _ hP (stable_claimed hs cfg now (hin j List.mem_cons_self)) h₁)
      (fun j' hj' => hin j' (List.mem_cons_of_mem _ hj')) h₂

/-- Every transaction of the worker keeps every stable property of each job. -/
theorem handler_fixed {P : Job W → Prop} (hs : Stable P) (cfg : Config) (r : Req) :
    ∀ db a db', q.Fixed P db → (q.handler cfg r).run db = .ok (a, db') → q.Fixed P db' := by
  intro db a db' hP h
  cases r with
  | claim now limit =>
    obtain ⟨out, h, -⟩ := run_map _ _ h
    simp only [claim, Txn.bind_eq] at h
    obtain ⟨js, db₁, h₁, h₂⟩ := Txn.run_bind_ok_inv h
    obtain ⟨rfl, hjs⟩ := scan_mem h₁
    exact claimAll_fixed hs cfg now js hP (fun j hj => hP j (hjs j hj).1) h₂
  | finish id lease now v =>
    obtain ⟨out, h, -⟩ := run_map _ _ h
    simp only [finish, Txn.bind_eq] at h
    obtain ⟨r, db₁, h₁, h₂⟩ := Txn.run_bind_ok_inv h
    obtain ⟨rfl, hr⟩ := get_mem h₁
    cases r with
    | none => simp at h₂; exact h₂.2 ▸ hP
    | some j =>
      obtain ⟨hj, -⟩ := hr j rfl
      simp only at h₂
      split at h₂
      · refine fixed_update _ hP ?_ h₂
        exact hs j _ (finished_id cfg now j v).symm (by unfold Config.finished; split <;> (try split) <;> rfl)
          (finished_work cfg now j v).symm (hP j hj)
      · simp at h₂; exact h₂.2 ▸ hP

/-- `enqueue` adds the job it builds, whatever id it takes. -/
theorem enqueue_adds {enq : Job W → Prop} (key : String) (work : W) (due every : Int64)
    (henq : ∀ id, enq { id, key, work, due_ms := due, status := .pending, attempts := 0, lease := 0, every_ms := every }) :
    (q.enqueue key work due every).All (q.Adds enq) := by
  have hdecode : ∀ r, (q.rows.decode r).All (q.Adds enq) := fun r => by
    unfold TableOf.decode; split
    · exact .pure _
    · exact .abort _
  refine Txn.All.bind (Txn.All.bind (Txn.All.single (.inr (.inl ⟨rfl, rfl⟩))) fun rows =>
    Txn.All.mapM _ hdecode rows) fun js => ?_
  cases js with
  | cons j _ => exact .pure _
  | nil =>
    refine Txn.All.bind (Txn.All.bind (Txn.All.bind (Txn.All.single (.inr (.inl ⟨rfl, rfl⟩))) fun rows =>
      Txn.All.mapM _ hdecode rows) fun js => ?_) fun id => ?_
    · cases js <;> exact .pure _
    · refine Txn.All.bind (Txn.All.single (.inr (.inr ⟨_, henq id, rfl⟩))) fun b => ?_
      cases b
      · exact .abort _
      · exact .pure _

end Queue

end Lanes.Db.Jobs
