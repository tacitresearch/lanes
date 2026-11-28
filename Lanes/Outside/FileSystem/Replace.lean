/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Outside.FileSystem.Basic

/-!
# Replacing a file whole

A file written in place is lost or torn by a crash in the middle: ext4 may leave it empty after
a truncation that reached the disk before the new bytes did. `Replace.plan` writes the new bytes
beside the file, syncs them, renames them over it and syncs the directory. Proved, from a
directory with nothing a crash could lose (`Replace.Ready`): after a crash at any point, or an
`io` error at any step that stops the plan there, the file holds what it held before or the new
bytes, never anything else (`Replace.crash`, `Replace.failed`); once the plan has run, it holds
the new bytes, and so after any crash (`Replace.done`); and the plan may run again
(`Replace.ready_run`).

A file left at `tmp` by an earlier crash is unlinked first, so that the plan never writes into
an inode that another name may share.
-/

@[expose] public section

namespace Lanes.FileSystem

/-- Replace the file `name` in `dir` by `bytes`, through `tmp` beside it. -/
def Replace.plan {B : Type} (dir : Path) (name tmp : String) (bytes : B) : List (Op B) :=
  [.delete (dir ++ [tmp]), .create (dir ++ [tmp]), .write (dir ++ [tmp]) 0 bytes,
    .fsync (dir ++ [tmp]), .rename (dir ++ [tmp]) (dir ++ [name]), .fsync dir]

/-- The plan the binding runs, on a `ByteArray`, is the plan proved here. -/
theorem Replace.plan_map {B C : Type} (f : B → C) (dir : Path) (name tmp : String) (bytes : B) :
    (Replace.plan dir name tmp bytes).map (Op.map f) = Replace.plan dir name tmp (f bytes) := rfl

namespace Replace

/-- What the plan starts from: a directory with nothing a crash could lose, `tmp` and `name` two
names, `tmp` a file or nothing, and `name` a file with nothing a crash could lose, or nothing. -/
structure Ready (s : Fs) (dir : Path) (d : Nat) (D : Dir) (name tmp : String) : Prop where
  settled : s.SettledDir dir d D
  ne : tmp ≠ name
  tmp : ∀ j, D.synced.lookup tmp = some j → ∃ f, s.node j = some (.file f)
  target : ∀ t, D.synced.lookup name = some t → ∃ f, s.node t = some (.file f) ∧ f.pending = []

/-- A state of the plan: the directory is `E`, and every other inode that was there is as it
was. -/
structure Stage (s₀ s : Fs) (d : Nat) (E : Dir) : Prop where
  node : s.node d = some (.dir E)
  same : ∀ j, j ≠ d → s₀.node j ≠ none → s.node j = s₀.node j

/-- Batches that leave `name` alone. -/
def Avoids (name : String) (B : List Batch) : Prop := ∀ b ∈ B, ∀ e ∈ b, e.1 ≠ name

variable {s₀ s : Fs} {dir : Path} {d : Nat} {D : Dir} {name tmp : String} {bytes : Bytes}
  {B : List Batch} {E : Dir}

theorem Ready.dir_eq (h : Ready s₀ dir d D name tmp) :
    D = { synced := D.synced, pending := [] } := by
  obtain ⟨synced, pending⟩ := D
  have := h.settled.synced
  simp_all

theorem Stage.way (hs : Stage s₀ s d E) (h : Ready s₀ dir d D name tmp) :
    ∀ j ∈ s₀.way 0 dir, s.node j = s₀.node j := by
  intro j hj
  obtain ⟨E, hE, -⟩ := h.settled.way j hj
  exact hs.same j (fun heq => h.settled.once (heq ▸ hj)) (by simp [hE])

theorem Stage.resolve (hs : Stage s₀ s d E) (h : Ready s₀ dir d D name tmp) :
    s.resolve dir = some d :=
  h.settled.resolve_of_same (hs.way h)

theorem Stage.set {n : Nat} (hs : Stage s₀ s d E) (hn : s₀.node n = none) (hnd : n ≠ d)
    (node : Node) : Stage s₀ (s.set n node) d E where
  node := by rw [Fs.node_set_ne _ _ (Ne.symm hnd)]; exact hs.node
  same j hj hj0 := by
    rw [Fs.node_set_ne _ _ (by intro heq; subst heq; exact hj0 hn)]
    exact hs.same j hj hj0

theorem Stage.set_dir (hs : Stage s₀ s d E) (E' : Dir) : Stage s₀ (s.set d (.dir E')) d E' where
  node := by simp
  same j hj hj0 := by rw [Fs.node_set_ne _ _ hj]; exact hs.same j hj hj0

/-- Through a crash that leaves the target's entry as it was, the target holds what it did. -/
theorem Stage.read_crash_of_lookup (hs : Stage s₀ s d E) (h : Ready s₀ dir d D name tmp)
    (c : Nat → Nat × Nat)
    (hl : (E.survive (c d).1).lookup name = D.synced.lookup name) :
    (s.crash c).read (dir ++ [name]) = s₀.read (dir ++ [name]) := by
  rw [Fs.read_crash_child (h.settled.resolve_crash (hs.way h) c) hs.node,
    Fs.read_child h.settled.resolve h.settled.node, Dir.entries_of_synced h.settled.synced, hl]
  cases ht : D.synced.lookup name with
  | none => rfl
  | some t =>
    obtain ⟨f, hf, hp⟩ := h.target t ht
    have htd : t ≠ d := fun heq => by simp [heq, h.settled.node] at hf
    simp [hs.same t htd (by simp [hf]), hf, Node.crash_of_synced_file hp]

/-- Through a crash, the target holds what it did while the batches leave it alone. -/
theorem Stage.read_crash (hs : Stage s₀ s d { synced := D.synced, pending := B }) (h : Ready s₀ dir d D name tmp)
    (hB : Avoids name B) (c : Nat → Nat × Nat) :
    (s.crash c).read (dir ++ [name]) = s₀.read (dir ++ [name]) :=
  hs.read_crash_of_lookup h c (lookup_batches_of_ne fun b hb => hB b (List.mem_of_mem_take hb))

/-! The steps of the plan, one by one. -/

theorem step_delete (h : Ready s₀ dir d D name tmp) : ∃ B,
    Stage s₀ (s₀.step (.delete (dir ++ [tmp]))).1 d { synced := D.synced, pending := B } ∧ Avoids name B ∧
      ({ synced := D.synced, pending := B } : Dir).entries.lookup tmp = none := by
  have hfind := Fs.find_in h.settled.resolve h.settled.node tmp
  rw [Dir.entries_of_synced h.settled.synced] at hfind
  cases hj : D.synced.lookup tmp with
  | none =>
    refine ⟨[], ⟨?_, fun _ _ _ => ?_⟩, by simp [Avoids], by simp [Dir.entries, hj]⟩ <;>
    simp [Fs.step, Fs.apply, Fs.delete, parentOf_append, Fs.dirAt_dir h.settled.resolve
        h.settled.node, hfind, hj, bind, Except.bind, ← h.dir_eq, h.settled.node]
  | some j =>
    obtain ⟨f, hf⟩ := h.tmp j hj
    have hstep : (s₀.step (.delete (dir ++ [tmp]))).1 =
        s₀.set d (.dir { synced := D.synced, pending := [[(tmp, none)]] }) := by
      simp [Fs.step, Fs.apply, Fs.delete, parentOf_append, Fs.dirAt_dir h.settled.resolve
        h.settled.node, hfind, hj, hf, bind, Except.bind, pure, Except.pure, Dir.add,
        h.settled.synced]
    refine ⟨[[(tmp, none)]], ⟨by simp [hstep], fun k hk _ => ?_⟩, ?_, ?_⟩
    · rw [hstep, Fs.node_set_ne _ _ hk]
    · simp [Avoids, h.ne]
    · simp [Dir.entries, applyBatch]

/-- The state after `create`, `write` and `fsync` of `tmp`: `tmp` names `n`, a new inode
holding `F`. -/
structure Staged (s₀ s : Fs) (d : Nat) (D : Dir) (B : List Batch) (n : Nat) (F : File) : Prop
    extends Stage s₀ s d { synced := D.synced, pending := B } where
  fresh : s₀.node n = none
  ne : n ≠ d
  file : s.node n = some (.file F)
  named : ({ synced := D.synced, pending := B } : Dir).entries.lookup tmp = some n

theorem step_create (h : Ready s₀ dir d D name tmp) (hs : Stage s₀ s d { synced := D.synced, pending := B })
    (hB : Avoids name B) (htmp : ({ synced := D.synced, pending := B } : Dir).entries.lookup tmp = none) :
    Staged (tmp := tmp) s₀ (s.step (.create (dir ++ [tmp]))).1 d D (B ++ [[(tmp, some s.fresh)]])
        s.fresh {} ∧ Avoids name (B ++ [[(tmp, some s.fresh)]]) := by
  have hr := hs.resolve h
  have hfind := Fs.find_in hr hs.node tmp
  rw [htmp] at hfind
  have hnd : s.fresh ≠ d := Fs.fresh_ne hs.node
  have hstep : (s.step (.create (dir ++ [tmp]))).1 = (s.set s.fresh (.file {})).set d
      (.dir { synced := D.synced, pending := B ++ [[(tmp, some s.fresh)]] }) := by
    simp [Fs.step, Fs.apply, Fs.create, Fs.link, hfind, parentOf_append, Fs.dirAt_dir hr hs.node,
      bind, Except.bind, pure, Except.pure, Dir.add]
  have hfresh : s₀.node s.fresh = none := by
    cases h0 : s₀.node s.fresh with
    | none => rfl
    | some x =>
      have := hs.same s.fresh hnd (by simp [h0])
      simp [h0] at this
  refine ⟨⟨⟨by simp [hstep], fun j hj hj0 => ?_⟩, hfresh, hnd, ?_, ?_⟩, ?_⟩
  · have hjn : j ≠ s.fresh := fun heq => hj0 (heq ▸ hfresh)
    rw [hstep, Fs.node_set_ne _ _ hj, Fs.node_set_ne _ _ hjn]
    exact hs.same j hj hj0
  · rw [hstep, Fs.node_set_ne _ _ hnd]; simp
  · simp [Dir.entries, applyBatch]
  · intro b hb e he
    rcases List.mem_append.mp hb with hb | hb
    · exact hB b hb e he
    · simp at hb; subst hb; simp at he; subst he; exact h.ne

theorem Staged.step_change {n : Nat} {F : File} {op : Op} {c : Change}
    (hs : Staged (tmp := tmp) s₀ s d D B n F)
    (hop : s.apply op = .ok (s.set n (.file (F.change c)), .done)) :
    Staged (tmp := tmp) s₀ (s.step op).1 d D B n (F.change c) := by
  have hstep : (s.step op).1 = s.set n (.file (F.change c)) := by simp [Fs.step, hop]
  rw [hstep]
  exact { toStage := hs.toStage.set hs.fresh hs.ne _, fresh := hs.fresh, ne := hs.ne,
          file := (by simp), named := hs.named }

theorem Staged.fileAt {n : Nat} {F : File} (h : Ready s₀ dir d D name tmp)
    (hs : Staged (tmp := tmp) s₀ s d D B n F) : s.fileAt (dir ++ [tmp]) = .ok (n, F) := by
  simp [Fs.fileAt, Fs.find_in (hs.resolve h) hs.node, hs.named, hs.file]

theorem step_write {n : Nat} (h : Ready s₀ dir d D name tmp)
    (hs : Staged (tmp := tmp) s₀ s d D B n {}) :
    Staged (tmp := tmp) s₀ (s.step (.write (dir ++ [tmp]) 0 bytes)).1 d D B n
      ({ pending := [.write 0 bytes] }) :=
  hs.step_change (c := .write 0 bytes) (by
    simp [Fs.apply, Fs.changeFile, hs.fileAt h, bind, Except.bind, pure, Except.pure,
      File.change])

theorem step_fsync_tmp {n : Nat} (h : Ready s₀ dir d D name tmp)
    (hs : Staged (tmp := tmp) s₀ s d D B n { pending := [.write 0 bytes] }) :
    Staged (tmp := tmp) s₀ (s.step (.fsync (dir ++ [tmp]))).1 d D B n { synced := bytes } := by
  have hfind : s.find (dir ++ [tmp]) = some (n, .file { pending := [.write 0 bytes] }) := by
    simp [Fs.find_in (hs.resolve h) hs.node, hs.named, hs.file]
  have hstep : (s.step (.fsync (dir ++ [tmp]))).1 = s.set n (.file { synced := bytes }) := by
    simp [Fs.step, Fs.apply, Fs.sync, hfind, Node.sync, File.sync, File.data, applyAll,
      Change.apply_write_nil]
  rw [hstep]
  exact { toStage := hs.toStage.set hs.fresh hs.ne _, fresh := hs.fresh, ne := hs.ne,
          file := (by simp), named := hs.named }

/-- The rename's batch. -/
abbrev swap (name tmp : String) (n : Nat) : Batch := [(tmp, none), (name, some n)]

theorem step_rename {n : Nat} (h : Ready s₀ dir d D name tmp)
    (hs : Staged (tmp := tmp) s₀ s d D B n { synced := bytes }) (hB : Avoids name B) :
    Stage s₀ (s.step (.rename (dir ++ [tmp]) (dir ++ [name]))).1 d
        { synced := D.synced, pending := B ++ [swap name tmp n] } ∧
      (s.step (.rename (dir ++ [tmp]) (dir ++ [name]))).1.node n =
        some (.file { synced := bytes }) := by
  have hr := hs.resolve h
  have hsrc := Fs.find_in hr hs.node tmp
  rw [hs.named] at hsrc
  have hdst := Fs.find_in hr hs.node name
  rw [Dir.entries, lookup_batches_of_ne hB] at hdst
  have hne : dir ++ [tmp] ≠ dir ++ [name] := fun heq => h.ne (by simpa using heq)
  have hrep : Fs.replaces (.file { synced := bytes }) (s.find (dir ++ [name])) = .ok () := by
    rw [hdst]
    cases ht : D.synced.lookup name with
    | none => rfl
    | some t =>
      obtain ⟨f, hf, -⟩ := h.target t ht
      have htd : t ≠ d := fun heq => by simp [heq, h.settled.node] at hf
      simp [hs.same t htd (by simp [hf]), hf, Fs.replaces]
  have hstep : (s.step (.rename (dir ++ [tmp]) (dir ++ [name]))).1 =
      s.set d (.dir { synced := D.synced, pending := B ++ [swap name tmp n] }) := by
    simp only [Fs.step, Fs.apply, Fs.rename, parentOf_append, Fs.dirAt_dir hr hs.node, hsrc,
      hs.file, hne, hrep, bind, Except.bind, pure, Except.pure, Option.bind_some, Option.map_some]
    simp [Dir.add]
  rw [hstep]
  exact ⟨{ node := by simp, same := fun j hj hj0 => by
            rw [Fs.node_set_ne _ _ hj]; exact hs.same j hj hj0 },
    by rw [Fs.node_set_ne _ _ hs.ne, hs.file]⟩

/-- Through a crash that leaves the target's entry naming `n`, the target holds `n`'s bytes. -/
theorem Stage.read_crash_new {n : Nat} (hs : Stage s₀ s d E) (h : Ready s₀ dir d D name tmp)
    (hn : s.node n = some (.file { synced := bytes })) (c : Nat → Nat × Nat)
    (hl : (E.survive (c d).1).lookup name = some n) :
    (s.crash c).read (dir ++ [name]) = some bytes := by
  rw [Fs.read_crash_child (h.settled.resolve_crash (hs.way h) c) hs.node, hl]
  simp [hn, Node.crash_of_synced_file, Fs.fileData, File.data, applyAll]

theorem lookup_survive_swap {n : Nat} (hB : Avoids name B) (kept : Nat) :
    (({ synced := D.synced, pending := B ++ [swap name tmp n] } : Dir).survive kept).lookup name
      = D.synced.lookup name ∨
    (({ synced := D.synced, pending := B ++ [swap name tmp n] } : Dir).survive kept).lookup name
      = some n := by
  by_cases hk : kept ≤ B.length
  · refine .inl ?_
    simp only [Dir.survive, List.take_append_of_le_length hk]
    exact lookup_batches_of_ne fun b hb => hB b (List.mem_of_mem_take hb)
  · refine .inr ?_
    simp only [Dir.survive, List.take_of_length_le (by simp; omega :
        (B ++ [swap name tmp n]).length ≤ kept), List.foldl_append, List.foldl_cons,
      List.foldl_nil, swap]
    exact lookup_applyBatch_concat _ [(tmp, none)] name (some n)

/-- After the rename, a crash of the directory's entries, as far as `kept`, leaves the target as
it was or as `n`. -/
theorem read_crash_swapped {n : Nat} (h : Ready s₀ dir d D name tmp) (hs : Stage s₀ s d E)
    (hB : Avoids name B) (hn : s.node n = some (.file { synced := bytes })) (c : Nat → Nat × Nat)
    (hE : E.survive (c d).1 =
      ({ synced := D.synced, pending := B ++ [swap name tmp n] } : Dir).survive (c d).1 ∨
      ∃ kept, E.survive (c d).1 =
        ({ synced := D.synced, pending := B ++ [swap name tmp n] } : Dir).survive kept) :
    (s.crash c).read (dir ++ [name]) ∈ [s₀.read (dir ++ [name]), some bytes] := by
  obtain ⟨kept, hk⟩ : ∃ kept, E.survive (c d).1 =
      ({ synced := D.synced, pending := B ++ [swap name tmp n] } : Dir).survive kept := by
    rcases hE with hE | hE
    · exact ⟨_, hE⟩
    · exact hE
  rcases lookup_survive_swap (tmp := tmp) (n := n) (D := D) hB kept with hl | hl
  · exact List.mem_cons.mpr (.inl (hs.read_crash_of_lookup h c (hk ▸ hl)))
  · exact List.mem_cons.mpr (.inr (List.mem_singleton.mpr (hs.read_crash_new h hn c (hk ▸ hl))))

theorem step_fsync_dir {n : Nat} (h : Ready s₀ dir d D name tmp)
    (hs : Stage s₀ s d { synced := D.synced, pending := B ++ [swap name tmp n] })
    (hB : Avoids name B) (hn : s.node n = some (.file { synced := bytes })) (hnd : n ≠ d) :
    Stage s₀ (s.step (.fsync dir)).1 d
        ({ synced := D.synced, pending := B ++ [swap name tmp n] } : Dir).sync ∧
      (s.step (.fsync dir)).1.node n = some (.file { synced := bytes }) ∧
      (({ synced := D.synced, pending := B ++ [swap name tmp n] } : Dir).sync).entries.lookup name
        = some n := by
  have hstep : (s.step (.fsync dir)).1 = s.set d
      (.dir ({ synced := D.synced, pending := B ++ [swap name tmp n] } : Dir).sync) := by
    simp [Fs.step, Fs.apply, Fs.sync, Fs.find_dir (hs.resolve h) hs.node, Node.sync]
  rw [hstep]
  refine ⟨⟨by simp, fun j hj hj0 => by rw [Fs.node_set_ne _ _ hj]; exact hs.same j hj hj0⟩,
    by rw [Fs.node_set_ne _ _ hnd, hn], ?_⟩
  have := lookup_survive_swap (tmp := tmp) (n := n) (D := D) hB (B.length + 1)
  simp only [Dir.survive, List.take_of_length_le (by simp :
    (B ++ [swap name tmp n]).length ≤ B.length + 1)] at this
  simp only [Dir.sync, Dir.entries, List.foldl_nil]
  rcases this with hl | hl
  · simp [List.foldl_append, swap, applyBatch] at hl ⊢
  · exact hl

theorem Ready.stage (h : Ready s₀ dir d D name tmp) :
    Stage s₀ s₀ d { synced := D.synced, pending := [] } :=
  ⟨by rw [← h.dir_eq]; exact h.settled.node, fun _ _ _ => rfl⟩

/-! What the plan guarantees. -/

/-- A crash at any point of the plan leaves the file as it was or holding the new bytes. -/
theorem crash (h : Ready s₀ dir d D name tmp) (k : Nat) (c : Nat → Nat × Nat) :
    ((s₀.run ((plan dir name tmp bytes).take k)).crash c).read (dir ++ [name]) ∈
      [s₀.read (dir ++ [name]), some bytes] := by
  obtain ⟨B, hs₁, hB, htmp⟩ := step_delete h
  obtain ⟨hs₂, hB₂⟩ := step_create h hs₁ hB htmp
  have hs₃ := step_write (bytes := bytes) h hs₂
  have hs₄ := step_fsync_tmp h hs₃
  obtain ⟨hs₅, hn⟩ := step_rename h hs₄ hB₂
  obtain ⟨hs₆, hn₆, -⟩ := step_fsync_dir h hs₅ hB₂ hn hs₄.ne
  have old : ∀ {s : Fs} {B : List Batch}, Stage s₀ s d { synced := D.synced, pending := B } →
      Avoids name B → (s.crash c).read (dir ++ [name]) ∈ [s₀.read (dir ++ [name]), some bytes] :=
    fun hs hB => List.mem_cons.mpr (.inl (hs.read_crash h hB c))
  match k with
  | 0 => simpa [Fs.run] using old h.stage (by simp [Avoids])
  | 1 => simpa [Fs.run, plan] using old hs₁ hB
  | 2 => simpa [Fs.run, plan] using old hs₂.toStage hB₂
  | 3 => simpa [Fs.run, plan] using old hs₃.toStage hB₂
  | 4 => simpa [Fs.run, plan] using old hs₄.toStage hB₂
  | 5 => simpa [Fs.run, plan] using read_crash_swapped h hs₅ hB₂ hn c (.inl rfl)
  | k + 6 =>
    simpa [Fs.run, plan] using read_crash_swapped h hs₆ hB₂ hn₆ c
      (.inr ⟨_, by rw [Dir.survive_sync, ← Dir.survive_all]⟩)

/-- An `io` error at any step, after which the plan stops, leaves the file, through any crash
after it, as it was or holding the new bytes. -/
theorem failed (h : Ready s₀ dir d D name tmp) {k : Nat} {op : Op}
    (hop : (plan dir name tmp bytes)[k]? = some op) {s : Fs}
    (hs : s ∈ (s₀.run ((plan dir name tmp bytes).take k)).failures op) (c : Nat → Nat × Nat) :
    (s.crash c).read (dir ++ [name]) ∈ [s₀.read (dir ++ [name]), some bytes] := by
  obtain ⟨B, hs₁, hB, htmp⟩ := step_delete h
  obtain ⟨hs₂, hB₂⟩ := step_create h hs₁ hB htmp
  have hs₃ := step_write (bytes := bytes) h hs₂
  have hs₄ := step_fsync_tmp h hs₃
  obtain ⟨hs₅, hn⟩ := step_rename h hs₄ hB₂
  have old : ∀ {s : Fs} {B : List Batch}, Stage s₀ s d { synced := D.synced, pending := B } →
      Avoids name B → (s.crash c).read (dir ++ [name]) ∈ [s₀.read (dir ++ [name]), some bytes] :=
    fun hs hB => List.mem_cons.mpr (.inl (hs.read_crash h hB c))
  have hcr := crash (bytes := bytes) h
  match k with
  | 0 =>
    simp only [plan, List.getElem?_cons_zero, Option.some.injEq] at hop
    subst hop
    simp only [Fs.run, List.take_zero, List.foldl_nil, Fs.failures, List.mem_cons,
      List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · simpa [Fs.run] using hcr 0 c
    · simpa [Fs.run, plan] using hcr 1 c
  | 1 =>
    simp only [plan, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hop
    subst hop
    simp only [Fs.run, plan, List.take_succ_cons, List.take_zero, List.foldl_cons, List.foldl_nil,
      Fs.failures, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · simpa [Fs.run, plan] using hcr 1 c
    · simpa [Fs.run, plan] using hcr 2 c
  | 2 =>
    simp only [plan, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hop
    subst hop
    simp only [Fs.run, plan, List.take_succ_cons, List.take_zero, List.foldl_cons, List.foldl_nil,
      Fs.failures, hs₂.fileAt h, List.mem_cons, List.mem_map, List.mem_range] at hs
    rcases hs with rfl | ⟨part, -, rfl⟩
    · exact old hs₂.toStage hB₂
    · exact old (hs₂.toStage.set hs₂.fresh hs₂.ne _) hB₂
  | 3 =>
    simp only [plan, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hop
    subst hop
    have hfind := Fs.find_in (hs₃.resolve h) hs₃.node tmp
    rw [hs₃.named] at hfind
    simp only [Fs.run, plan, List.take_succ_cons, List.take_zero, List.foldl_cons, List.foldl_nil,
      Fs.failures, hfind, hs₃.file, Option.bind_some, Option.map_some, List.mem_cons,
      List.mem_map] at hs
    rcases hs with rfl | ⟨ch, -, rfl⟩
    · exact old hs₃.toStage hB₂
    · exact old (hs₃.toStage.set hs₃.fresh hs₃.ne _) hB₂
  | 4 =>
    simp only [plan, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hop
    subst hop
    simp only [Fs.run, plan, List.take_succ_cons, List.take_zero, List.foldl_cons, List.foldl_nil,
      Fs.failures, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · simpa [Fs.run, plan] using hcr 4 c
    · simpa [Fs.run, plan] using hcr 5 c
  | 5 =>
    simp only [plan, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hop
    subst hop
    simp only [Fs.run, plan, List.take_succ_cons, List.take_zero, List.foldl_cons, List.foldl_nil,
      Fs.failures, Fs.find_dir (hs₅.resolve h) hs₅.node, List.mem_cons, List.mem_map] at hs
    rcases hs with rfl | ⟨ch, -, rfl⟩
    · exact read_crash_swapped h hs₅ hB₂ hn c (.inl rfl)
    · obtain ⟨kept, part⟩ := ch
      simp only [Node.crash]
      exact read_crash_swapped h (hs₅.set_dir _) hB₂ (by rw [Fs.node_set_ne _ _ hs₄.ne, hn]) c
        (.inr ⟨kept, by simp [Dir.survive]⟩)
  | k + 6 => simp [plan] at hop

/-- Once the plan has run, the file holds the new bytes, and holds them after any crash; and
the plan may run again. -/
theorem done (h : Ready s₀ dir d D name tmp) :
    (s₀.run (plan dir name tmp bytes)).read (dir ++ [name]) = some bytes ∧
      (∀ c, ((s₀.run (plan dir name tmp bytes)).crash c).read (dir ++ [name]) = some bytes) ∧
      ∃ D', Ready (s₀.run (plan dir name tmp bytes)) dir d D' name tmp := by
  obtain ⟨B, hs₁, hB, htmp⟩ := step_delete h
  obtain ⟨hs₂, hB₂⟩ := step_create h hs₁ hB htmp
  have hs₃ := step_write (bytes := bytes) h hs₂
  have hs₄ := step_fsync_tmp h hs₃
  obtain ⟨hs₅, hn⟩ := step_rename h hs₄ hB₂
  obtain ⟨hs₆, hn₆, hl₆⟩ := step_fsync_dir h hs₅ hB₂ hn hs₄.ne
  simp only [Fs.run, plan, List.foldl_cons, List.foldl_nil]
  refine ⟨?_, fun c => hs₆.read_crash_new h hn₆ c (by rw [Dir.survive_sync]; exact hl₆), _,
    ⟨h.settled.of_same (hs₆.way h) hs₆.node rfl, h.ne, fun j hj => ?_, fun t ht => ?_⟩⟩
  · rw [Fs.read_child (hs₆.resolve h) hs₆.node, hl₆]
    simp [hn₆, Fs.fileData, File.data, applyAll]
  · simp only [Dir.sync, Dir.entries, List.foldl_append, List.foldl_cons, List.foldl_nil, swap,
      applyBatch, lookup_put_ne _ _ h.ne, lookup_put_self] at hj
    cases hj
  · simp only [Dir.sync, List.append_assoc, List.singleton_append] at ht hl₆
    rw [show ∀ X : Entries, ({ synced := X } : Dir).entries = X from fun _ => rfl] at hl₆
    rw [hl₆] at ht
    cases ht
    exact ⟨_, hn₆, rfl⟩

end Replace

end Lanes.FileSystem
