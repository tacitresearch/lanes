/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Runtime.Kernel

/-!
A read of some actors' states, which writes nothing (`docs/decisions/D108-reads-from-state.md`).
The runtime reads each actor between two of its steps (`Runtime.tryPeek`); `Peek.of` reads a
kernel's, as `Http.Loopback` does.
-/

@[expose] public section

namespace Lanes

variable {σ : Signature}

/-- The states of the actors `ids`, and those of every actor started that `every` holds of
(`others`): an actor not started has its initial state. -/
structure Peek (sys : System σ) (ids : List σ.Id) where
  states : List ((i : σ.Id) × sys.State i)
  ids_eq : states.map (·.1) = ids
  every : σ.Id → Bool := fun _ => false
  others : List ((i : σ.Id) × sys.State i) := []

namespace Peek

variable {sys : System σ}

/-- The state of `i` among `states`. -/
def find : (states : List ((i : σ.Id) × sys.State i)) → (i : σ.Id) →
    i ∈ states.map (·.1) → sys.State i
  | [], _, h => absurd h List.not_mem_nil
  | ⟨j, s⟩ :: rest, i, h =>
    if e : j = i then e ▸ s
    else find rest i (by
      rw [List.map_cons, List.mem_cons] at h
      exact h.resolve_left fun h' => e h'.symm)

def get {ids : List σ.Id} (p : Peek sys ids) (i : σ.Id) (h : i ∈ ids) : sys.State i :=
  find p.states i (by rw [p.ids_eq]; exact h)

theorem find_map (f : (i : σ.Id) → sys.State i) (ids : List σ.Id) (i : σ.Id)
    (h : i ∈ (ids.map fun j => (⟨j, f j⟩ : (i : σ.Id) × sys.State i)).map (·.1)) :
    find (ids.map fun j => ⟨j, f j⟩) i h = f i := by
  induction ids with
  | nil => simp at h
  | cons j rest ih =>
    simp only [List.map_cons, find]
    split
    · next e => subst e; rfl
    · exact ih _

/-- The states `f` gives, read as a peek. -/
def ofStates (ids : List σ.Id) (f : (i : σ.Id) → sys.State i) (every : σ.Id → Bool := fun _ => false)
    (others : List ((i : σ.Id) × sys.State i) := []) : Peek sys ids where
  states := ids.map fun i => ⟨i, f i⟩
  ids_eq := by simp [List.map_map, Function.comp_def]
  every := every
  others := others

theorem get_ofStates (ids : List σ.Id) (f : (i : σ.Id) → sys.State i) (every : σ.Id → Bool)
    (others : List ((i : σ.Id) × sys.State i)) (i : σ.Id) (h : i ∈ ids) :
    (ofStates ids f every others).get i h = f i :=
  find_map f ids i _

instance {ids : List σ.Id} : Nonempty (Peek sys ids) :=
  ⟨ofStates ids fun i => (sys.actor i).init⟩

variable [Hashable σ.Id]

/-- The states of `ids` in kernel `k`, and of every actor of `k` started that `every` holds of. -/
def of (k : Kernel sys) (ids : List σ.Id) (every : σ.Id → Bool := fun _ => false) :
    Peek sys ids :=
  ofStates ids (fun i => (k.cell i).state) every
    (k.cells.toList.filterMap fun x => if every x.1 then some ⟨x.1, x.2.state⟩ else none)

/-- A peek gives each actor's state in the kernel it was read from. -/
theorem get_of (k : Kernel sys) (ids : List σ.Id) (every : σ.Id → Bool) (i : σ.Id)
    (h : i ∈ ids) : (of k ids every).get i h = (k.cell i).state :=
  get_ofStates ids _ every _ i h

/-- Every state among a peek's others is that actor's state in the kernel it was read from, of
an actor `every` holds of. -/
theorem others_of {k : Kernel sys} {ids : List σ.Id} {every : σ.Id → Bool}
    {x : (i : σ.Id) × sys.State i} (h : x ∈ (of k ids every).others) :
    every x.1 = true ∧ x.2 = (k.cell x.1).state := by
  simp only [of, ofStates, List.mem_filterMap] at h
  obtain ⟨⟨i, cell⟩, hmem, hx⟩ := h
  split at hx
  · next hp =>
    cases hx
    have hget : k.cells.get? i = some cell := Std.DHashMap.mem_toList_iff_get?_eq_some.mp hmem
    exact ⟨hp, by simp [Kernel.cell, hget]⟩
  · cases hx

/-- An actor `every` holds of that is not among a peek's others has its initial state in the
kernel it was read from: it was never started. -/
theorem init_of_not_others {k : Kernel sys} {ids : List σ.Id} {every : σ.Id → Bool}
    {i : σ.Id} (hp : every i = true) (h : i ∉ (of k ids every).others.map (·.1)) :
    (k.cell i).state = (sys.actor i).init := by
  cases hget : k.cells.get? i with
  | none => simp [Kernel.cell, hget]
  | some cell =>
    exfalso
    refine h (List.mem_map.mpr ⟨⟨i, cell.state⟩, ?_, rfl⟩)
    simp only [of, ofStates, List.mem_filterMap]
    exact ⟨⟨i, cell⟩, Std.DHashMap.mem_toList_iff_get?_eq_some.mpr hget, by simp [hp]⟩

end Peek

end Lanes
