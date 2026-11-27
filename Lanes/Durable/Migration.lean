/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Durable.Journal

/-!
A migration takes the kernel that an old version of a system left to a kernel of the new
version: every actor's state, every message queued or waiting on a timer, every output not yet
handed over. A deploy that changes a state or a message type runs one once, at its first start
(`Lanes.Journal.Upgrade`).

The proofs of the new system are about its runs, and after a migration its run starts from the
migrated kernel, not from boot. What carries over is what each new actor keeps by its own steps
and restarts (`Actor.Inductive`) and the migration lands in: a `Migration` cannot be built
without that proof, and `Migration.inv_exec` says it then holds of every actor in every state
the new shard reaches.
-/

@[expose] public section

namespace Lanes

variable {σ₀ σ : Signature}

/-- How a kernel of `old` becomes one of `new`, with the proof that what the new actors keep
holds of it. -/
structure Migration (old : System σ₀) (new : System σ) where
  id : σ₀.Id → σ.Id
  /-- Two actors never become one. -/
  injective : ∀ i j, id i = id j → i = j
  state : ∀ i, old.State i → new.State (id i)
  msg : ∀ i, σ₀.Msg i → σ.Msg (id i)
  output : σ₀.Out → σ.Out
  /-- What each new actor keeps. -/
  inv : ∀ j, new.State j → Prop
  keeps : ∀ j, (new.actor j).Inductive (inv j)
  /-- Every state an old actor can reach migrates to one where `inv` holds. -/
  lands : ∀ i s, (old.actor i).Reachable s → inv (id i) (state i s)

namespace Migration

variable {old : System σ₀} {new : System σ} (m : Migration old new)

def cell (i : σ₀.Id) (c : Kernel.Cell old i) : Kernel.Cell new (m.id i) where
  state := m.state i c.state
  up := c.up
  timers := c.timers.map fun t => (m.msg i t.1, t.2)

def envelope (e : Envelope σ₀) : Envelope σ :=
  ⟨e.src.map m.id, m.id e.dst, m.msg e.dst e.msg⟩

def image (img : Kernel.Image old) : Kernel.Image new where
  cells := img.cells.map fun p => ⟨m.id p.1, m.cell p.1 p.2⟩
  queue := img.queue.map m.envelope
  agenda := img.agenda.map fun p => (p.1, ⟨m.id p.2.1, m.msg p.2.1 p.2.2⟩)
  nextToken := img.nextToken
  clock_ms := img.clock_ms
  timerTurn := img.timerTurn

variable [Hashable σ₀.Id] [Hashable σ.Id]

def kernel (k : Kernel old) : Kernel new :=
  (m.image k.image).kernel

omit [Hashable σ.Id] in
private theorem distinct (k : Kernel old) :
    ((k.cells.toList.map fun p => (⟨m.id p.1, m.cell p.1 p.2⟩ : (j : σ.Id) × Kernel.Cell new j))
      ).Pairwise (fun a b => (a.1 == b.1) = false) := by
  refine List.Pairwise.map _ ?_ Std.DHashMap.distinct_keys_toList
  intro a b hab
  simp only [beq_eq_false_iff_ne, ne_eq] at hab ⊢
  exact fun h => hab (m.injective _ _ h)

private theorem get?_kernel (k : Kernel old) {i : σ₀.Id} {c : Kernel.Cell old i}
    (h : k.cells.get? i = some c) : (m.kernel k).cells.get? (m.id i) = some (m.cell i c) := by
  have hmem := Std.DHashMap.mem_toList_iff_get?_eq_some.mpr h
  exact Std.DHashMap.get?_ofList_of_mem (k := m.id i) (beq_self_eq_true _) (m.distinct k)
    (List.mem_map_of_mem (f := fun p => (⟨m.id p.1, m.cell p.1 p.2⟩ :
      (j : σ.Id) × Kernel.Cell new j)) hmem)

omit [Hashable σ.Id] in
private theorem contains_image (k : Kernel old) {j : σ.Id}
    (h : ((m.image k.image).cells.map Sigma.fst).contains j = true) :
    ∃ i, m.id i = j ∧ (k.cells.get? i).isSome := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (List.contains_iff_mem.mp h)
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  exact ⟨q.1, rfl, by simp [Std.DHashMap.mem_toList_iff_get?_eq_some.mp hq]⟩

private theorem get?_kernel_none (k : Kernel old) {j : σ.Id}
    (h : ¬∃ i, m.id i = j ∧ (k.cells.get? i).isSome) : (m.kernel k).cells.get? j = none :=
  Std.DHashMap.get?_ofList_of_contains_eq_false
    (Bool.eq_false_iff.mpr fun hc => h (m.contains_image k hc))

/-- The migrated kernel holds each old actor migrated, provided an actor that was never written
to migrates to one that was never written to. So the new run starts from the old state,
migrated. -/
theorem cell_kernel (hinit : ∀ i, m.state i (old.actor i).init = (new.actor (m.id i)).init)
    (k : Kernel old) (i : σ₀.Id) : (m.kernel k).cell (m.id i) = m.cell i (k.cell i) := by
  cases h : k.cells.get? i with
  | some c => simp [Kernel.cell, h, m.get?_kernel k h]
  | none =>
    have hnone := m.get?_kernel_none k (j := m.id i) fun ⟨i', heq, hsome⟩ => by
      obtain rfl := m.injective _ _ heq
      simp [h] at hsome
    simp [Kernel.cell, h, hnone, Migration.cell, hinit]

/-- Every actor of a kernel migrated from one whose actors are in states they reach on their
own satisfies `inv`. -/
theorem inv_kernel (k : Kernel old) (hk : ∀ i, (old.actor i).Reachable (k.cell i).state)
    (j : σ.Id) : m.inv j ((m.kernel k).cell j).state := by
  by_cases hj : ∃ i, m.id i = j ∧ (k.cells.get? i).isSome
  · obtain ⟨i, rfl, hsome⟩ := hj
    obtain ⟨c, h⟩ := Option.isSome_iff_exists.mp hsome
    have hc : k.cell i = c := by simp [Kernel.cell, h]
    simp only [Kernel.cell, m.get?_kernel k h, Option.getD_some, Migration.cell]
    exact m.lands i _ (hc ▸ hk i)
  · simp only [Kernel.cell, m.get?_kernel_none k hj, Option.getD_none]
    exact (m.keeps j).init

/-- Every actor of a kernel migrated from one that the old shard can have satisfies `inv`. -/
theorem inv_migrated (ops : List (Kernel.Op σ₀)) (j : σ.Id) :
    m.inv j ((m.kernel ((Kernel.boot old).1.exec ops).kernel).cell j).state :=
  m.inv_kernel _ (Kernel.exec_cell_reachable old ops) j

/-- The guarantee across a migration. The old shard's kernel is the one its journal describes,
`recover old history`. The new shard starts from that kernel migrated, as its snapshot restores
it, and whatever it is then asked, every one of its actors satisfies `inv` in every state it
reaches. -/
theorem inv_exec (history : List (Journal.Entry σ₀)) (later : List (Kernel.Op σ)) (j : σ.Id) :
    m.inv j ((((m.kernel (Journal.recover old history).1).image.kernel).exec later).kernel.cell
      j).state := by
  refine Kernel.exec_inductive _ later m.keeps (fun j => ?_) j
  rw [Kernel.cell_image_kernel, Journal.recover_kernel]
  exact m.inv_migrated _ j

end Migration

end Lanes
