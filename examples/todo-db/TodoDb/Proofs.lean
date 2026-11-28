/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TodoDb
import Lanes.Proofs

/-!
The invariant of the to-do list, proved per transaction: a user's to-dos are unique by title, and
to-dos by id (`Unique`). Each transaction of the checked handler keeps it (`preserves`): `add`
inserts only after a lookup by `by_title` found nothing, `complete` replaces a to-do by one with
its owner and title, `remove` deletes, `list` only reads. So every database the store model allows
after every run satisfies it (`unique_always`, through `Db.invariant`): with lost `COMMIT`s, calls
taking effect late, and the actor's retries.
-/

namespace TodoDb

open Lanes.Db

/-- A user's to-dos are unique by title, and to-dos by id. -/
def Unique (db : Db) : Prop :=
  ((db.rows todos.table.name).map todos.byTitle.project).Nodup
    ∧ ((db.rows todos.table.name).map todos.table.keyOf).Nodup

theorem nodup_map_inj {α β : Type} {f : α → β} :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {x y : α}, x ∈ l → y ∈ l → f x = f y → x = y
  | [], _, _, _, hx, _, _ => by simp at hx
  | a :: l, h, x, y, hx, hy, hf => by
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.mp hx with hx | hx <;> rcases List.mem_cons.mp hy with hy | hy
    · rw [hx, hy]
    · exact absurd (List.mem_map.mpr ⟨y, hy, by rw [← hf, hx]⟩) h.1
    · exact absurd (List.mem_map.mpr ⟨x, hx, by rw [hf, hy]⟩) h.1
    · exact nodup_map_inj h.2 hx hy hf

theorem ofRow_eq {r : Row} {t : Todo} (h : todos.ofRow r = some t) : r = todos.toRow t :=
  Columns.toRow_of_ofRow _ h

theorem unique_of_reads {α : Type} {t : Txn α} (hr : t.Reads) {db : Db} {a : α} {db' : Db}
    (h : t.run db = .ok (a, db')) (hu : Unique db) : Unique db' := by
  rw [hr.run h]
  exact hu

/-- The rows of the table after a write to it. -/
theorem rows_after {o : Op} {db : Db} {r : o.Ret} {db' : Db} (h : o.apply db = .ok (r, db'))
    (hw : o.writes = true) (ht : o.table = todos.table) :
    db'.rows todos.table.name = (o.onRows (db.rows todos.table.name)).2 := by
  rw [Op.rows_apply o h, ht]
  simp [hw]

theorem insert_preserves (owner : Int64) (title : String) {db : Db}
    (hfree : ∀ r ∈ db.rows todos.table.name, todos.byTitle.project r ≠ [.int owner, .text title])
    (hu : Unique db) {a : Answer} {db' : Db} (h : (insertNew owner title).run db = .ok (a, db')) :
    Unique db' := by
  unfold insertNew at h
  simp only [Txn.bind_eq] at h
  obtain ⟨id, db₁, hid, h⟩ := Txn.run_bind_ok_inv h
  have hdb₁ : db₁ = db := (TableOf.scan_reads _ _ |>.bind fun _ => by split <;> exact .pure _).run hid
  rw [hdb₁] at h
  obtain ⟨b, db₂, hins, h⟩ := Txn.run_bind_ok_inv h
  have hdb' : db' = db₂ := by
    split at h
    · simp at h; exact h.2.symm
    · simp at h
  rw [hdb']
  have happ := Txn.run_single hins
  unfold Unique
  rw [rows_after happ rfl rfl]
  rcases Op.insert_rows todos.table (todos.toRow { id, owner, title }) (db.rows todos.table.name)
    with heq | ⟨hperm, hkeys⟩
  · rw [heq]; exact hu
  · refine ⟨(hperm.map _).nodup_iff.mpr ?_, (hperm.map _).nodup_iff.mpr ?_⟩
    · rw [List.map_cons, List.nodup_cons]
      refine ⟨fun hm => ?_, hu.1⟩
      obtain ⟨x, hx, hpx⟩ := List.mem_map.mp hm
      exact hfree x hx (hpx.trans rfl)
    · rw [List.map_cons, List.nodup_cons]
      refine ⟨fun hm => ?_, hu.2⟩
      obtain ⟨x, hx, hkx⟩ := List.mem_map.mp hm
      exact hkeys x hx hkx

theorem add_preserves (owner : Int64) (title : String) {db : Db} (hu : Unique db) {a : Answer}
    {db' : Db} (h : (add true owner title).run db = .ok (a, db')) : Unique db' := by
  simp only [add, ↓reduceIte, Txn.bind_eq] at h
  obtain ⟨ts, db₁, hl, h⟩ := Txn.run_bind_ok_inv h
  have hdb₁ : db₁ = db := (TableOf.lookup_reads _ _ _ _).run hl
  rw [hdb₁] at h
  cases ts with
  | cons t _ => simp at h; rw [← h.2]; exact hu
  | nil =>
    refine insert_preserves owner title (fun r hr hp => ?_) hu h
    simp only [TableOf.lookup, Txn.bind_eq] at hl
    obtain ⟨found, db₂, hscan, hmap⟩ := Txn.run_bind_ok_inv hl
    have hlen := Txn.run_mapM_length _ found hmap
    have happ := Txn.run_single hscan
    have hrun := (Op.apply_ok _ happ).2
    have hnil : found = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
    rw [hnil] at hrun
    have := Scan.run_eq_nil _ hrun.symm Nat.one_pos r hr
    rw [← Bool.not_eq_true, Scan.matches_lookup _ _ _ _ rfl] at this
    exact this hp

/-- What `todos.get` found: a row of the key, which decodes to the to-do. -/
theorem get_found {db : Db} {key : Row} {t : Todo} {db' : Db}
    (h : (todos.get key).run db = .ok (some t, db')) :
    db' = db ∧ ∃ r ∈ db.rows todos.table.name, todos.table.keyOf r = key ∧ r = todos.toRow t := by
  refine ⟨(TableOf.get_reads _ _).run h, ?_⟩
  simp only [TableOf.get, Txn.bind_eq] at h
  obtain ⟨found, db₁, hget, h⟩ := Txn.run_bind_ok_inv h
  have happ := Txn.run_single hget
  have hdb := Op.apply_read _ rfl happ
  have hfind := (Op.apply_ok _ happ).2
  rw [hdb] at h
  cases found with
  | none => simp at h
  | some r =>
    simp only [Functor.map] at h
    obtain ⟨t', db₃, hdec, h⟩ := Txn.run_bind_ok_inv h
    simp only [Function.comp, Txn.run_pure, Except.ok.injEq, Prod.mk.injEq,
      Option.some.injEq] at h
    rw [h.1] at hdec
    have hfind : (db.rows todos.table.name).find? (todos.table.hasKey key) = some r := hfind.symm
    refine ⟨r, List.mem_of_find?_eq_some hfind, ?_, ofRow_eq (TableOf.run_decode _ hdec)⟩
    simpa [Table.hasKey] using List.find?_some hfind

/-- A to-do replaced by one of the same id, owner and title keeps the invariant. -/
theorem update_preserves {db : Db} (hu : Unique db) {t t' : Todo} (hid : t'.id = t.id)
    (howner : t'.owner = t.owner) (htitle : t'.title = t.title)
    (hmem : todos.toRow t ∈ db.rows todos.table.name) {r : Bool} {db' : Db}
    (h : (todos.update t').run db = .ok (r, db')) : Unique db' := by
  have happ := Txn.run_single h
  unfold Unique
  rw [rows_after happ rfl rfl]
  rcases Op.update_rows todos.table (todos.toRow t') (db.rows todos.table.name) with heq | heq
  · rw [heq]; exact hu
  · rw [heq, List.map_map, List.map_map]
    have same : ∀ x ∈ db.rows todos.table.name,
        todos.table.hasKey (todos.table.keyOf (todos.toRow t')) x = true → x = todos.toRow t := by
      intro x hx hk
      refine nodup_map_inj hu.2 hx hmem ?_
      simpa [Table.hasKey, todos, Table.keyOf, hid] using hk
    constructor
    · rw [List.map_congr_left (l := db.rows todos.table.name) (g := todos.byTitle.project) fun x hx => by
        by_cases hk : todos.table.hasKey (todos.table.keyOf (todos.toRow t')) x = true
        · simp only [Function.comp_apply, hk, ↓reduceIte]
          rw [same x hx hk]
          simp [todos, Index.project, todos.byTitle, howner, htitle]
        · simp [hk]]
      exact hu.1
    · rw [List.map_congr_left (l := db.rows todos.table.name) (g := todos.table.keyOf) fun x hx => by
        by_cases hk : todos.table.hasKey (todos.table.keyOf (todos.toRow t')) x = true
        · simp only [Function.comp_apply, hk, ↓reduceIte]
          rw [same x hx hk]
          simp [todos, Table.keyOf, hid]
        · simp [hk]]
      exact hu.2

theorem complete_preserves (owner id : Int64) {db : Db} (hu : Unique db) {a : Answer} {db' : Db}
    (h : (complete owner id).run db = .ok (a, db')) : Unique db' := by
  simp only [complete, Txn.bind_eq] at h
  obtain ⟨found, db₁, hget, h⟩ := Txn.run_bind_ok_inv h
  cases found with
  | none => rw [(TableOf.get_reads _ _).run hget] at h; simp at h; rw [← h.2]; exact hu
  | some t =>
    obtain ⟨hdb, r₀, hr₀, -, hrt⟩ := get_found hget
    rw [hdb] at h
    rw [hrt] at hr₀
    simp only at h
    split at h
    · obtain ⟨b, db₂, hupd, h⟩ := Txn.run_bind_ok_inv h
      have hu₂ := update_preserves (t := t) (t' := { t with done := true }) hu rfl rfl rfl hr₀ hupd
      simp at h
      rw [← h.2]
      exact hu₂
    · simp at h; rw [← h.2]; exact hu

theorem remove_preserves (owner id : Int64) {db : Db} (hu : Unique db) {a : Answer} {db' : Db}
    (h : (remove owner id).run db = .ok (a, db')) : Unique db' := by
  simp only [remove, Txn.bind_eq] at h
  obtain ⟨found, db₁, hget, h⟩ := Txn.run_bind_ok_inv h
  rw [(TableOf.get_reads _ _).run hget] at h
  cases found with
  | none => simp at h; rw [← h.2]; exact hu
  | some t =>
    simp only at h
    split at h
    · obtain ⟨b, db₂, hdel, h⟩ := Txn.run_bind_ok_inv h
      have happ := Txn.run_single hdel
      simp at h
      rw [← h.2]
      unfold Unique
      rw [rows_after happ rfl rfl, Op.delete_rows]
      exact ⟨hu.1.sublist (List.filter_sublist.map _), hu.2.sublist (List.filter_sublist.map _)⟩
    · simp at h; rw [← h.2]; exact hu

/-- Every transaction of the checked handler keeps the invariant. -/
theorem preserves : Preserves (handler true) Unique := by
  intro q db a db' hu h
  cases q with
  | add owner title => exact add_preserves owner title hu h
  | complete owner id => exact complete_preserves owner id hu h
  | remove owner id => exact remove_preserves owner id hu h
  | list owner =>
    simp only [handler, Functor.map] at h
    obtain ⟨ts, db₁, hs, h⟩ := Txn.run_bind_ok_inv h
    simp at h
    rw [← h.2, (TableOf.scan_reads _ _).run hs]
    exact hu

theorem unique_empty : Unique (Db.empty schema) := by
  simp [Unique, Db.empty, Db.rows, schema]

/-- **A user's to-dos are unique by title in every database the store may hold**, after every
run the store model allows at `SERIALIZABLE` with the checked handler: lost `COMMIT`s, failures,
calls taking effect late, and every call still outstanding taking effect. -/
theorem unique_always {σ : Lanes.Signature} (cfg : Lanes.Db.Config) (port : Port σ Request Answer)
    {events : List (Lanes.Event σ)} {s : Lanes.Db.State Request Answer}
    (hrun : (outside cfg (handler true) (Db.empty schema) port).after events = some s) :
    ∀ w ∈ s.worlds, ∀ w' ∈ w.expand (handler true) w.fuel, Unique w'.db :=
  invariant cfg port unique_empty preserves hrun

end TodoDb
