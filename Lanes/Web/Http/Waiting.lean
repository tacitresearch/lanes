/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std.Data.HashMap

/-!
The HTTP server's table of requests waiting for their response, as data: the id the next
request gets, and who waits on which id. The server (`Lanes.Http.serveOn`) keeps one in a mutex
and resolves the waiters it is handed. `R` is whatever a waiter is: a promise in the server.

Of every sequence of operations from a start (`exec`): ids are handed out in order from the
start, so never twice, and the id of a request the runtime refused goes to the next request
(`exec_handed`); a waiter waits on an id handed out to it, until it is answered (`exec_waiting`);
each id is answered at most once, and to the waiter it was handed out to (`exec_answered`); after
a drain nobody waits and everyone handed an id has been answered (`exec_drain`).
-/

@[expose] public section

namespace Lanes.Http

structure Waiting (R : Type) where
  next : Nat
  waiters : Std.HashMap Nat R := {}

namespace Waiting

variable {R : Type}

def start (next : Nat) : Waiting R := { next }

/-- The next id, with `waiter` waiting on it. -/
def wait (waiter : R) : Waiting R → Nat × Waiting R
  | { next, waiters } => (next, { next := next + 1, waiters := waiters.insert next waiter })

/-- Whether `id` is the id just handed out and still waited on. -/
def releases (id : Nat) (w : Waiting R) : Bool :=
  id + 1 == w.next && w.waiters.contains id

/-- The request just given an id was refused by the runtime: its id goes to the next request. -/
def release (id : Nat) (w : Waiting R) : Waiting R :=
  if w.releases id then
    match w with
    | { waiters, .. } => { next := id, waiters := waiters.erase id }
  else w

def answer (id : Nat) : Waiting R → Option R × Waiting R
  | { next, waiters } => (waiters[id]?, { next, waiters := waiters.erase id })

def drain : Waiting R → List (Nat × R) × Waiting R
  | { next, waiters } => (waiters.toList, { next })

inductive Op (R : Type) where
  | wait (waiter : R)
  | release (id : Nat)
  | answer (id : Nat)
  | drain

/-- A table with what it has done so far: the ids it has handed out and to whom, in order, and
the answers it has given. -/
structure Trace (R : Type) where
  table : Waiting R
  handed : List (Nat × R) := []
  answered : List (Nat × R) := []

def Trace.apply (t : Trace R) : Op R → Trace R
  | .wait waiter =>
    { t with table := (t.table.wait waiter).2
             handed := t.handed ++ [((t.table.wait waiter).1, waiter)] }
  | .release id =>
    { t with table := t.table.release id
             handed := if t.table.releases id then t.handed.dropLast else t.handed }
  | .answer id =>
    { t with table := (t.table.answer id).2
             answered := t.answered ++ ((t.table.answer id).1.map (id, ·)).toList }
  | .drain => { t with table := t.table.drain.2, answered := t.answered ++ t.table.drain.1 }

def exec (start : Nat) (ops : List (Op R)) : Trace R :=
  ops.foldl Trace.apply { table := Waiting.start start }

private structure Inv (n : Nat) (t : Trace R) : Prop where
  start : n ≤ t.table.next
  handed : t.handed.map (·.1) = List.range' n (t.table.next - n)
  waiting : ∀ id r, t.table.waiters[id]? = some r ↔ (id, r) ∈ t.handed ∧ id ∉ t.answered.map (·.1)
  nodup : (t.answered.map (·.1)).Nodup
  answered : ∀ p ∈ t.answered, p ∈ t.handed

private theorem Inv.bound {n : Nat} {t : Trace R} (h : Inv n t) {id : Nat} {r : R}
    (hp : (id, r) ∈ t.handed) : n ≤ id ∧ id < t.table.next := by
  have := List.mem_map_of_mem (f := (·.1)) hp
  rw [h.handed, List.mem_range'_1] at this
  have hs := h.start
  exact ⟨by omega, by omega⟩

private theorem inv_wait {n : Nat} {t : Trace R} (h : Inv n t) (waiter : R) :
    Inv n (t.apply (.wait waiter)) := by
  obtain ⟨⟨next, waiters⟩, handed, answered⟩ := t
  have hb : ∀ {id : Nat} {r : R}, (id, r) ∈ handed → n ≤ id ∧ id < next :=
    fun hp => h.bound hp
  obtain ⟨hstart, hhanded, hwaiting, hnodup, hanswered⟩ := h
  simp only at hstart hhanded hwaiting hnodup hanswered hb
  have fresh : ∀ r, (next, r) ∉ handed := fun r hr => by have := hb hr; omega
  refine ⟨?_, ?_, ?_, hnodup, ?_⟩ <;> simp only [Trace.apply, wait]
  · omega
  · rw [List.map_append, hhanded, show next + 1 - n = next - n + 1 by omega, List.range'_1_concat,
      show n + (next - n) = next by omega]
    rfl
  · intro id r
    rw [Std.HashMap.getElem?_insert]
    by_cases hid : next = id
    · subst hid
      have : next ∉ answered.map (·.1) := fun hm => by
        obtain ⟨⟨j, r'⟩, hp, rfl⟩ := List.mem_map.mp hm
        exact fresh r' (hanswered _ hp)
      simp [fresh, this, eq_comm]
    · have hne : (next == id) = false := by simpa using hid
      simp only [hne, Bool.false_eq_true, ↓reduceIte, hwaiting, List.mem_append, List.mem_singleton,
        Prod.mk.injEq, Ne.symm hid, false_and, or_false]
  · exact fun p hp => List.mem_append_left _ (hanswered p hp)

private theorem below_of_mem_dropLast {n id : Nat} {handed : List (Nat × R)}
    (hhanded : handed.map (·.1) = List.range' n (id + 1 - n)) (hn : n ≤ id) :
    ∀ q ∈ handed.dropLast, q.1 < id := fun q hq => by
  have := List.mem_map_of_mem (f := (·.1)) hq
  rw [List.map_dropLast, hhanded, show id + 1 - n = (id - n) + 1 by omega,
    List.range'_1_concat, List.dropLast_concat, List.mem_range'_1] at this
  omega

private theorem inv_release {n : Nat} {t : Trace R} (h : Inv n t) (id : Nat) :
    Inv n (t.apply (.release id)) := by
  obtain ⟨⟨next, waiters⟩, handed, answered⟩ := t
  have hb : ∀ {id : Nat} {r : R}, (id, r) ∈ handed → n ≤ id ∧ id < next :=
    fun hp => h.bound hp
  obtain ⟨hstart, hhanded, hwaiting, hnodup, hanswered⟩ := h
  simp only at hstart hhanded hwaiting hnodup hanswered hb
  simp only [Trace.apply, release]
  by_cases hr : (⟨next, waiters⟩ : Waiting R).releases id
  · simp only [hr, ↓reduceIte]
    simp only [releases, Bool.and_eq_true, beq_iff_eq, Std.HashMap.contains_eq_isSome_getElem?,
      Option.isSome_iff_exists] at hr
    obtain ⟨rfl, r, hidr⟩ := hr
    have hheld := (hwaiting id r).mp hidr
    obtain ⟨hn, -⟩ := hb hheld.1
    have hfst := below_of_mem_dropLast hhanded hn
    have hne : handed ≠ [] := by rintro rfl; simp at hheld
    have hsplit := (List.dropLast_concat_getLast hne).symm
    have hlast : handed = handed.dropLast ++ [(id, r)] := by
      have hm := hheld.1
      rw [hsplit] at hm
      rcases List.mem_append.mp hm with hm | hm
      · exact absurd (hfst _ hm) (Nat.lt_irrefl _)
      · rw [← List.mem_singleton.mp hm] at hsplit; exact hsplit
    refine ⟨hn, ?_, ?_, hnodup, ?_⟩ <;> simp only
    · rw [List.map_dropLast, hhanded, show id + 1 - n = (id - n) + 1 by omega,
        List.range'_1_concat, List.dropLast_concat]
    · intro j q
      rw [Std.HashMap.getElem?_erase]
      by_cases hj : id = j
      · subst hj
        simp only [beq_self_eq_true, ↓reduceIte, reduceCtorEq, false_iff, not_and]
        exact fun hm => absurd (hfst _ hm) (Nat.lt_irrefl _)
      · have hne : (id == j) = false := by simpa using hj
        simp only [hne, Bool.false_eq_true, ↓reduceIte, hwaiting]
        rw [hlast]
        simp [Ne.symm hj]
    · intro p hp
      have hp' := hanswered p hp
      rw [hlast] at hp'
      rcases List.mem_append.mp hp' with hm | hm
      · exact hm
      · rw [List.mem_singleton] at hm
        subst hm
        exact absurd (List.mem_map_of_mem (f := (·.1)) hp) hheld.2
  · simp only [hr, Bool.false_eq_true, ↓reduceIte]
    exact ⟨hstart, hhanded, hwaiting, hnodup, hanswered⟩

private theorem inv_answer {n : Nat} {t : Trace R} (h : Inv n t) (id : Nat) :
    Inv n (t.apply (.answer id)) := by
  obtain ⟨⟨next, waiters⟩, handed, answered⟩ := t
  obtain ⟨hstart, hhanded, hwaiting, hnodup, hanswered⟩ := h
  simp only at hstart hhanded hwaiting hnodup hanswered
  refine ⟨hstart, hhanded, ?_, ?_, ?_⟩ <;> simp only [Trace.apply, answer]
  · intro j q
    rw [Std.HashMap.getElem?_erase]
    by_cases hj : id = j
    · subst hj
      simp only [beq_self_eq_true, ↓reduceIte, reduceCtorEq, false_iff, not_and]
      intro hm
      cases hw : waiters[id]? with
      | none =>
        refine Classical.byContradiction fun hn => ?_
        have := (hwaiting id q).mpr ⟨hm, by simpa [hw] using hn⟩
        simp [hw] at this
      | some r => simp
    · have hne : (id == j) = false := by simpa using hj
      simp only [hne, Bool.false_eq_true, ↓reduceIte, hwaiting]
      cases waiters[id]? <;> simp [Ne.symm hj]
  · cases hw : waiters[id]? with
    | none => simpa using hnodup
    | some r =>
      simp only [Option.map_some, Option.toList_some, List.map_append, List.map_cons, List.map_nil]
      refine List.nodup_append.mpr ⟨hnodup, by simp, fun a ha b hb => ?_⟩
      rw [List.mem_singleton] at hb
      subst hb
      rintro rfl
      exact ((hwaiting a r).mp hw).2 ha
  · intro p hp
    rcases List.mem_append.mp hp with hm | hm
    · exact hanswered p hm
    · cases hw : waiters[id]? with
      | none => simp [hw] at hm
      | some r =>
        simp only [hw, Option.map_some, Option.toList_some, List.mem_singleton] at hm
        subst hm
        exact ((hwaiting id r).mp hw).1

private theorem inv_drain {n : Nat} {t : Trace R} (h : Inv n t) :
    Inv n (t.apply .drain) ∧ ∀ id : Nat, ((t.apply .drain).table.waiters[id]? : Option R) = none := by
  obtain ⟨⟨next, waiters⟩, handed, answered⟩ := t
  obtain ⟨hstart, hhanded, hwaiting, hnodup, hanswered⟩ := h
  simp only at hstart hhanded hwaiting hnodup hanswered
  have hmem : ∀ {p : Nat × R}, p ∈ waiters.toList ↔ (waiters[p.1]? : Option R) = some p.2 := fun {p} =>
    Std.HashMap.mem_toList_iff_getElem?_eq_some
  refine ⟨⟨hstart, hhanded, ?_, ?_, ?_⟩, ?_⟩ <;> simp only [Trace.apply, drain]
  · intro id r
    simp only [Std.HashMap.getElem?_empty, reduceCtorEq, false_iff, not_and, List.map_append]
    intro hp hm
    apply hm
    by_cases ha : id ∈ answered.map (·.1)
    · exact List.mem_append_left _ ha
    · exact List.mem_append_right _
        (List.mem_map_of_mem (f := (·.1)) ((hmem (p := (id, r))).mpr ((hwaiting id r).mpr ⟨hp, ha⟩)))
  · rw [List.map_append, Std.HashMap.map_fst_toList_eq_keys]
    refine List.nodup_append.mpr ⟨hnodup, Std.HashMap.nodup_keys, fun a ha b hb => ?_⟩
    rintro rfl
    rw [← Std.HashMap.map_fst_toList_eq_keys] at hb
    obtain ⟨⟨j, r⟩, hp, rfl⟩ := List.mem_map.mp hb
    exact ((hwaiting j r).mp (hmem.mp hp)).2 ha
  · intro p hp
    rcases List.mem_append.mp hp with hm | hm
    · exact hanswered p hm
    · exact ((hwaiting p.1 p.2).mp (hmem.mp hm)).1
  · exact fun _ => Std.HashMap.getElem?_empty

private theorem inv_exec (n : Nat) (ops : List (Op R)) : Inv n (exec n ops) := by
  unfold exec
  suffices ∀ (t : Trace R), Inv n t → Inv n (ops.foldl Trace.apply t) from
    this _ ⟨Nat.le_refl n, by simp [Waiting.start], by simp [Waiting.start], List.nodup_nil,
      fun _ h => by simp at h⟩
  induction ops with
  | nil => exact fun _ h => h
  | cons op ops ih =>
    intro t h
    apply ih
    cases op with
    | wait waiter => exact inv_wait h waiter
    | release id => exact inv_release h id
    | answer id => exact inv_answer h id
    | drain => exact (inv_drain h).1

/-- Ids are handed out in order from the start, each once: the ids held are `start`, `start + 1`
and so on, up to the one the next request gets. An id freed by `release` is handed out again;
it was never in the system. -/
theorem exec_handed (start : Nat) (ops : List (Op R)) :
    (exec start ops).handed.map (·.1) = List.range' start ((exec start ops).table.next - start)
      ∧ start ≤ (exec start ops).table.next :=
  ⟨(inv_exec start ops).handed, (inv_exec start ops).start⟩

theorem exec_handed_nodup (start : Nat) (ops : List (Op R)) :
    ((exec start ops).handed.map (·.1)).Nodup ∧ ∀ p ∈ (exec start ops).handed, start ≤ p.1 := by
  refine ⟨?_, fun p hp => ((inv_exec start ops).bound hp).1⟩
  rw [(exec_handed start ops).1]
  exact List.nodup_range'

/-- A waiter waits on an id exactly while that id is handed out to it and not yet answered. A
table holds one waiter for an id, and an id is handed out once, so it is waited on once. -/
theorem exec_waiting (start : Nat) (ops : List (Op R)) (id : Nat) (r : R) :
    (exec start ops).table.waiters[id]? = some r
      ↔ (id, r) ∈ (exec start ops).handed ∧ id ∉ (exec start ops).answered.map (·.1) :=
  (inv_exec start ops).waiting id r

/-- An answer goes to the waiter its id was handed out to and to no other, and no id is
answered twice. -/
theorem exec_answered (start : Nat) (ops : List (Op R)) :
    ((exec start ops).answered.map (·.1)).Nodup
      ∧ ∀ p ∈ (exec start ops).answered, p ∈ (exec start ops).handed :=
  ⟨(inv_exec start ops).nodup, (inv_exec start ops).answered⟩

/-- After a drain nobody waits, and everyone holding an id has been answered. -/
theorem exec_drain (start : Nat) (ops : List (Op R)) :
    (∀ id : Nat, ((exec start (ops ++ [.drain])).table.waiters[id]? : Option R) = none)
      ∧ ∀ p ∈ (exec start (ops ++ [.drain])).handed,
          p.1 ∈ (exec start (ops ++ [.drain])).answered.map (·.1) := by
  have hd : exec start (ops ++ [.drain]) = (exec start ops).apply .drain := by
    simp [exec, List.foldl_append]
  have hnone := (inv_drain (inv_exec start ops)).2
  rw [← hd] at hnone
  refine ⟨hnone, fun p hp => Classical.byContradiction fun hn => ?_⟩
  have := ((inv_exec start (ops ++ [.drain])).waiting p.1 p.2).mpr ⟨hp, hn⟩
  rw [hnone] at this
  exact absurd this (by simp)

end Waiting

end Lanes.Http
