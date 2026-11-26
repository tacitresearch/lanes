/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
A first-in first-out queue with constant-time `push` and amortised constant-time `pop?`. Every
operation is specified by what it does to `toList`, so proofs never look inside.
-/

@[expose] public section

namespace Lanes

/-- `toList` is `front ++ back.reverse`. -/
structure Fifo (α : Type) where
  front : List α := []
  back : List α := []

namespace Fifo

variable {α : Type}

def toList (q : Fifo α) : List α :=
  q.front ++ q.back.reverse

def push (q : Fifo α) (a : α) : Fifo α :=
  { q with back := a :: q.back }

def pop? (q : Fifo α) : Option (α × Fifo α) :=
  match q.front with
  | a :: front => some (a, { q with front })
  | [] =>
    match q.back.reverse with
    | a :: front => some (a, { front, back := [] })
    | [] => none

def filter (p : α → Bool) (q : Fifo α) : Fifo α :=
  { front := q.front.filter p, back := q.back.filter p }

def length (q : Fifo α) : Nat :=
  q.front.length + q.back.length

def isEmpty (q : Fifo α) : Bool :=
  q.front.isEmpty && q.back.isEmpty

@[simp] theorem toList_empty : ({} : Fifo α).toList = [] := rfl

@[simp] theorem toList_push (q : Fifo α) (a : α) : (q.push a).toList = q.toList ++ [a] := by
  simp [toList, push]

@[simp] theorem toList_filter (p : α → Bool) (q : Fifo α) :
    (q.filter p).toList = q.toList.filter p := by
  simp [toList, filter, List.filter_reverse]

@[simp] theorem length_toList (q : Fifo α) : q.toList.length = q.length := by
  simp [toList, length]

theorem isEmpty_iff (q : Fifo α) : q.isEmpty = true ↔ q.toList = [] := by
  simp [isEmpty, toList]

theorem pop?_eq_none {q : Fifo α} : q.pop? = none ↔ q.toList = [] := by
  unfold pop? toList
  split
  · simp_all
  · split <;> simp_all

theorem toList_of_pop? {q rest : Fifo α} {a : α} (h : q.pop? = some (a, rest)) :
    q.toList = a :: rest.toList := by
  unfold pop? at h
  split at h
  · next front hfront =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [toList, hfront]
  · next hfront =>
    split at h
    · next front hback =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [toList, hfront, hback]
    · exact absurd h (by simp)

end Fifo

end Lanes
