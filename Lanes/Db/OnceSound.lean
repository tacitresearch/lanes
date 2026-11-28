/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Db.Sound
public import Lanes.Db.Once

/-!
A run under a key that committed makes every later run under it, of any body, a no-op that
answers the same (`Keys.once_again`): the key and the answer were stored in the run's own
transaction, so a database that has the run has the key.
-/

@[expose] public section

namespace Lanes.Db.Keys

variable {A : Type} (k : Keys A)

theorem get_apply {key : String} {db : Db} {r : Option Row} {db' : Db}
    (h : (Op.get k.rows.table [.text key]).apply db = .ok (r, db')) (db₂ : Db) :
    (Op.get k.rows.table [.text key]).apply db₂ =
      .ok ((db₂.rows k.name).find? (k.table.hasKey [.text key]), db₂) := by
  obtain ⟨hv, -⟩ := Op.apply_ok _ h
  unfold Op.apply
  simp only [hv, ↓reduceIte, Op.writes]
  rfl

theorem find_only {l : List Row} {p : Row → Bool} {r : Row} (hr : r ∈ l) (hp : p r = true)
    (honly : ∀ x ∈ l, p x = true → x = r) : l.find? p = some r := by
  cases h : l.find? p with
  | none => exact absurd hp (by simpa using List.find?_eq_none.mp h r hr)
  | some y => rw [honly y (List.mem_of_find?_eq_some h) (List.find?_some h)]

/-- **Once.** A run of `once key body` that committed leaves a database on which every run of
`once key body'`, whatever `body'`, answers the same and changes nothing. -/
theorem once_again (key : String) (body body' : Txn A) {db : Db} {a : A} {db' : Db}
    (h : (k.once key body).run db = .ok (a, db')) : (k.once key body').run db' = .ok (a, db') := by
  simp only [once, Txn.bind_eq] at h ⊢
  obtain ⟨found, db₁, h₁, h₂⟩ := Txn.run_bind_ok_inv h
  obtain rfl := (TableOf.get_reads _ _).run h₁
  obtain ⟨row, db₂, h₃, h₄⟩ := Txn.run_bind_ok_inv h₁
  have ha := Txn.run_single h₃
  obtain rfl := Op.apply_read _ rfl ha
  cases found with
  | some p =>
    obtain ⟨x, a₀⟩ := p
    simp only at h₂
    simp only [Txn.pure_eq, Txn.run_pure, Except.ok.injEq, Prod.mk.injEq] at h₂
    obtain ⟨rfl, rfl⟩ := h₂
    rw [Txn.run_bind, h₁]
    rfl
  | none =>
    simp only at h₂
    obtain ⟨a', db₃, h₅, h₆⟩ := Txn.run_bind_ok_inv h₂
    obtain ⟨ok, db₄, h₇, h₈⟩ := Txn.run_bind_ok_inv h₆
    cases ok with
    | false => simp at h₈
    | true =>
      simp only [↓reduceIte, Txn.pure_eq, Txn.run_pure, Except.ok.injEq, Prod.mk.injEq] at h₈
      obtain ⟨rfl, rfl⟩ := h₈
      have hi := Txn.run_single h₇
      obtain ⟨-, hret⟩ := Op.apply_ok _ hi
      obtain ⟨hnew', hfresh⟩ := Op.insert_onRows _ _ _ hret.symm
      have hrows := Op.rows_apply _ hi k.name
      have hnew : db₄.rows k.name = k.table.insertSorted (k.rows.toRow (key, a')) (db₃.rows k.name) := by
        rw [hrows]
        split
        · exact hnew'
        · next hc => exact absurd ⟨rfl, rfl⟩ hc
      have hkey : k.table.keyOf (k.rows.toRow (key, a')) = [.text key] := rfl
      have hget := get_apply k ha db₄
      have hfind : (db₄.rows k.name).find? (k.table.hasKey [.text key]) = some (k.rows.toRow (key, a')) := by
        rw [hnew]
        refine find_only ((k.table.mem_insertSorted _ _ _).mpr (.inl rfl)) ?_ fun x hx hk => ?_
        · simp [Table.hasKey, hkey]
        · rcases (k.table.mem_insertSorted _ _ x).mp hx with rfl | hx
          · rfl
          · exfalso
            apply hfresh x hx
            change k.table.keyOf x = k.table.keyOf (k.rows.toRow (key, a'))
            rw [hkey]
            simpa [Table.hasKey] using hk
      have hg : (k.rows.get [.text key]).run db₄ = .ok (some (key, a'), db₄) := by
        simp only [TableOf.get, Txn.bind_eq, Txn.get]
        rw [Txn.run_bind]
        erw [Txn.run_op_ok _ hget]
        change (match (db₄.rows k.name).find? (k.table.hasKey [.text key]) with
          | some r => some <$> k.rows.decode r
          | none => pure none).run db₄ = _
        rw [hfind]
        simp [TableOf.decode, rows, ofRow, k.payload.decode_encode]
        rfl
      rw [Txn.run_bind, hg]
      rfl

/-- A transaction under a key asks what its body asks, and reads and writes the keys' table. -/
theorem once_all {P : Op → Prop} (hP : ∀ o, o.table.name = k.name → P o) (key : String) {body : Txn A}
    (hbody : body.All P) : (k.once key body).All P := by
  refine Txn.All.bind (Txn.All.bind (Txn.All.single (hP _ rfl)) fun r => ?_) fun found => ?_
  · cases r with
    | some x =>
      refine Txn.All.bind ?_ fun _ => .pure _
      unfold TableOf.decode; split
      · exact .pure _
      · exact .abort _
    | none => exact .pure _
  · cases found with
    | some p => exact .pure _
    | none =>
      refine Txn.All.bind hbody fun a => Txn.All.bind (Txn.All.single (hP _ rfl)) fun b => ?_
      cases b
      · exact .abort _
      · exact .pure _

end Lanes.Db.Keys
