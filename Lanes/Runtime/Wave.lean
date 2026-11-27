/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Runtime.KernelSound
public import Lanes.Proof.Lift

/-!
A shard's actors step in parallel, and the kernel is still the one sequential run.

A wave is the messages queued when it begins. The step of an actor is a pure function of its own
state and the message, so the steps of different actors on the wave's messages can be worked out
at once, each actor's in the order its messages are queued (`Kernel.plan`, on Lean's task pool).
The kernel then does the wave's units of work exactly as `runBatch` does them, oldest message
first, timers in their turn, effects performed one actor after another, but takes each step's
effects from the plan instead of calling `step` (`Kernel.runBatchAhead`).

A plan keeps of each actor its last state only, so that each step updates the state in place.
The kernel leaves the state the wave began with in the actor's cell until the last of the
actor's steps, and writes the last state then. If the actor's steps stop being taken before
that, because a timer of its goes off, another message comes first, the wave ends, or an actor is
started that has no cell yet, the kernel works out the state the steps taken leave, from the
state in the cell, and writes it (`Plan.fixAt`, `Plan.real`). That costs the steps again, and is
rare. A state a task has seen is shared, so its first write still copies it: once a wave for
each actor worked out on the pool.

So the work done is `runBatch`'s, value for value (`Kernel.runWaves_eq`): the journal, replay,
snapshots and every theorem about the kernel are unchanged, and which thread worked out a step
cannot be told. What makes it so is that handling a message for one actor neither reads nor
writes another actor's cell, and that writes to two cells already in the table, or a write to
one and the removal of another, can be made in either order (`DHashMap.insert_comm_of_contains`).
-/

@[expose] public section

namespace Lanes

variable {σ : Signature}

namespace Kernel

variable {sys : System σ} [Hashable σ.Id]

/-- The state `ms` leave, from `s`. -/
def replay (sys : System σ) (i : σ.Id) (s : sys.State i) : List (σ.Msg i) → sys.State i
  | [] => s
  | m :: ms =>
    match (sys.actor i).step s m with
    | (s, _) => replay sys i s ms

/-- An actor's steps worked out ahead: each message with the effects of its step, and whether
the state the step leaves is one starting gives (`Actor.fresh`). -/
abbrev Steps (σ : Signature) (i : σ.Id) := List (σ.Msg i × List (Effect σ i) × Bool)

/-- The steps of `ms` from `s`, and the state they leave. They end at the first that stops the
actor: the kernel starts it again on its next message. Each step updates the state in place,
since nothing else holds it. -/
def ahead (sys : System σ) (i : σ.Id) : sys.State i → List (σ.Msg i) → Steps σ i × sys.State i
  | s, [] => ([], s)
  | s, m :: ms =>
    match (sys.actor i).step s m with
    | (s, effs) =>
      let fresh := (sys.actor i).fresh s
      if effs.any Effect.isStop then ([(m, effs, fresh)], s)
      else
        match ahead sys i s ms with
        | (steps, last) => ((m, effs, fresh) :: steps, last)

/-- Each step is `step`'s from the state the step before it leaves, the first from `s`, and the
last leaves `last`. -/
def Fits (sys : System σ) (i : σ.Id) : sys.State i → Steps σ i → sys.State i → Prop
  | s, [], last => last = s
  | s, (m, effs, fresh) :: rest, last =>
    effs = ((sys.actor i).step s m).2 ∧ fresh = (sys.actor i).fresh ((sys.actor i).step s m).1 ∧
      Fits sys i ((sys.actor i).step s m).1 rest last

/-- What a plan holds of an actor: the messages whose steps the kernel took, the last first, the
steps still to take, and the state the last step leaves. -/
structure Ahead (sys : System σ) (i : σ.Id) where
  taken : List (σ.Msg i) := []
  steps : Steps σ i
  last : sys.State i

/-- The steps worked out ahead for some of the actors, and a list of every actor they were
worked out for. -/
structure Plan (sys : System σ) [Hashable σ.Id] where
  steps : Std.DHashMap σ.Id (Ahead sys) := ∅
  actors : List σ.Id := []

/-- `k` with the state `s` in the cell of `i`, if `i` has a cell. -/
def setState (k : Kernel sys) (i : σ.Id) (s : sys.State i) : Kernel sys :=
  { k with cells := match k.cells.get? i with
    | some c => k.cells.insert i { c with state := s }
    | none => k.cells }

/-- `rest`, with whether the state is one starting gives known. -/
def restAs (k : Kernel sys) (i : σ.Id) (fresh : Bool) : Kernel sys :=
  let c := k.cell i
  if fresh && c.up && c.timers.isEmpty then { k with cells := k.cells.erase i } else k

namespace Plan

def set (p : Plan sys) (i : σ.Id) (a : Ahead sys i) : Plan sys :=
  { p with steps := p.steps.insert i a }

def drop (p : Plan sys) (i : σ.Id) : Plan sys :=
  { p with steps := p.steps.erase i }

/-- Every actor's steps still to take, none taken. -/
def reset (p : Plan sys) : Plan sys :=
  { p with steps := p.steps.map fun _ a => { a with taken := [] } }

/-- `k` with the state the steps taken of `i` leave written in the cell of `i`. -/
def fixAt (p : Plan sys) (i : σ.Id) (k : Kernel sys) : Kernel sys :=
  match p.steps.get? i with
  | some { taken := m :: ms, .. } => k.setState i (replay sys i (k.cell i).state (m :: ms).reverse)
  | _ => k

/-- `fixAt` of each of `actors`, each actor once. -/
def fixAll : List σ.Id → Plan sys → Kernel sys → Kernel sys
  | [], _, k => k
  | i :: is, p, k => fixAll is (p.drop i) (p.fixAt i k)

/-- The kernel that `runBatch` would have: the state the steps taken leave written in the cell
of every actor whose last step is still to take. -/
def real (p : Plan sys) (k : Kernel sys) : Kernel sys :=
  fixAll p.actors p k

/-- What the plan holds of each actor fits it as the kernel has it: it is up, and its steps start
from the state the steps taken leave. -/
def Good (p : Plan sys) (k : Kernel sys) : Prop :=
  ∀ i a, p.steps.get? i = some a → i ∈ p.actors ∧ (k.cell i).up = true ∧
    Fits sys i (replay sys i (k.cell i).state a.taken.reverse) a.steps a.last

end Plan

/-! What the kernel does with a plan: `handle`, `run1`, `step` and `runBatch`, with steps from the
plan. -/

/-- Handle `msg` for `i` as `handle` does, with the plan's step if it is the plan's next
message. The cell keeps its state until the last step. -/
def handleAhead (k : Kernel sys) (p : Plan sys) (i : σ.Id) (msg : σ.Msg i) :
    Kernel sys × Plan sys × List σ.Out :=
  match p.steps.get? i with
  | none =>
    match k.handle i msg with
    | (k, outs) => (k, p, outs)
  | some a =>
    match a.steps with
    | (m, effs, fresh) :: rest =>
      if m = msg then
        match rest with
        | [] =>
          match k.settle i (a.last, effs) with
          | (k, outs) => (k.rest i, p.drop i, outs)
        | _ :: _ =>
          match k.settle i ((k.cell i).state, effs) with
          | (k, outs) =>
            let k := k.restAs i fresh
            let p := p.set i { a with taken := m :: a.taken, steps := rest }
            if (k.cell i).up then (k, p, outs) else (p.fixAt i k, p.drop i, outs)
      else
        match (p.fixAt i k).handle i msg with
        | (k, outs) => (k, p.drop i, outs)
    | [] =>
      match (p.fixAt i k).handle i msg with
      | (k, outs) => (k, p.drop i, outs)

def run1Ahead (k : Kernel sys) (p : Plan sys) : Step sys × Plan sys :=
  match k.queue.pop? with
  | none => ({ kernel := k }, p)
  | some (e, rest) =>
    if (k.cell e.dst).up then
      match ({ k with queue := rest }).handleAhead p e.dst e.msg with
      | (k, p, outs) =>
        ({ kernel := k, events := .deliver e :: outs.map .output, outputs := outs }, p)
    else if k.cells.contains e.dst then
      match k.startActor e.dst with
      | (k, outs) => ({ kernel := k, events := .start e.dst :: outs.map .output, outputs := outs }, p)
    else
      match (p.real k).startActor e.dst with
      | (k, outs) =>
        ({ kernel := k, events := .start e.dst :: outs.map .output, outputs := outs }, p.reset)

def stepAhead (k : Kernel sys) (p : Plan sys) : Step sys × Plan sys :=
  match k.timerNext with
  | some (due, ⟨i, msg⟩) => (({ p.fixAt i k with timerTurn := false }).fire i msg due, p.drop i)
  | none => ({ k with timerTurn := true }).run1Ahead p

def runBatchAhead (k : Kernel sys) (p : Plan sys) : (fuel : Nat) → Step sys × Plan sys
  | 0 => ({ kernel := k }, p)
  | fuel + 1 =>
    if k.wait = .none then
      match k.stepAhead p with
      | ({ kernel, events, outputs }, p) =>
        match kernel.runBatchAhead p fuel with
        | ({ kernel, events := later, outputs := more }, p) =>
          ({ kernel, events := events ++ later, outputs := outputs ++ more }, p)
    else ({ kernel := k }, p)

/-! Working out a wave's steps. -/

/-- The messages of `wave` by receiver, each receiver's in the order they are queued. -/
def mail (wave : List (Envelope σ)) : Std.DHashMap σ.Id (fun i => List (σ.Msg i)) :=
  wave.reverse.foldl (fun m e => m.insert e.dst (e.msg :: (m.get? e.dst).getD [])) ∅

/-- An actor of `actors` that is up, its state, and its messages in the wave in order. -/
abbrev Job (k : Kernel sys) (actors : List σ.Id) :=
  { x : (i : σ.Id) × sys.State i × List (σ.Msg i) //
    x.1 ∈ actors ∧ (k.cell x.1).up = true ∧ x.2.1 = (k.cell x.1).state }

/-- An actor's steps worked out, with why they fit it. -/
abbrev Done (k : Kernel sys) (actors : List σ.Id) :=
  { y : (i : σ.Id) × Ahead sys i // y.1 ∈ actors ∧ (k.cell y.1).up = true ∧ y.2.taken = [] ∧
    Fits sys y.1 (k.cell y.1).state y.2.steps y.2.last }

omit [Hashable σ.Id] in
theorem fits_ahead (i : σ.Id) (s : sys.State i) (ms : List (σ.Msg i)) :
    Fits sys i s (ahead sys i s ms).1 (ahead sys i s ms).2 := by
  induction ms generalizing s with
  | nil => rfl
  | cons m ms ih =>
    simp only [ahead]
    split
    · exact ⟨rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, ih _⟩

def Job.run {k : Kernel sys} {actors : List σ.Id} (x : Job k actors) : Done k actors :=
  let r := ahead sys x.1.1 x.1.2.1 x.1.2.2
  ⟨⟨x.1.1, { steps := r.1, last := r.2 }⟩, x.2.1, x.2.2.1, rfl,
    by rw [← x.2.2.2]; exact fits_ahead ..⟩

/-- The actors of `wave` that are up, with their state and their messages. A task working on a
job holds the state and not the kernel. -/
def jobs (k : Kernel sys) (wave : List (Envelope σ)) :
    List (Job k ((mail wave).toList.map Sigma.fst)) :=
  (mail wave).toList.attach.filterMap fun ⟨⟨i, ms⟩, h⟩ =>
    let c := k.cell i
    if hup : c.up = true then some ⟨⟨i, c.state, ms⟩, List.mem_map_of_mem h, hup, rfl⟩ else none

/-- `xs` in pieces of `size`, in order. -/
def chunks {α : Type} (size : Nat) : List α → List (List α)
  | [] => []
  | x :: xs => (x :: xs).take (max 1 size) :: chunks size ((x :: xs).drop (max 1 size))
termination_by xs => xs.length
decreasing_by simp only [List.length_drop, List.length_cons]; omega

def Plan.add {k : Kernel sys} {actors : List σ.Id} (p : Plan sys) (done : List (Done k actors)) :
    Plan sys :=
  done.foldl (fun p d => p.set d.1.1 d.1.2) p

/-- How a wave's steps are spread over threads. It decides only where they are worked out, not
what they are (`runWaves_eq`). -/
structure Spread where
  /-- Threads to work out a wave's steps on. With one, a batch is `runBatch` itself. -/
  workers : Nat := 1
  /-- The fewest actors in a piece, so that a piece is worth a task: a wave whose actors fit in
  one piece is left to the kernel. -/
  minPiece : Nat := 1

/-- The steps of a wave worked out on up to `workers` threads: the actors are cut into as many
pieces, of at least `minPiece` actors each, each piece a task of Lean's task pool, the first done
on this thread. A wave whose actors fit in one piece, one actor's mail among them, is left to the
kernel, which gains nothing from it. -/
def plan (k : Kernel sys) (spread : Spread) (wave : List (Envelope σ)) : Plan sys :=
  let js := jobs k wave
  let size := max (max 1 spread.minPiece) ((js.length + spread.workers - 1) / max 1 spread.workers)
  if js.length ≤ size then {}
  else
    match chunks size js with
    | [] => {}
    | first :: others =>
      let tasks := others.map fun piece => Task.spawn fun _ => piece.map Job.run
      let p := Plan.add { actors := (mail wave).toList.map Sigma.fst } (first.map Job.run)
      tasks.foldl (fun p t => p.add t.get) p

/-! `setState` -/

theorem get?_of_contains {k : Kernel sys} {i : σ.Id} (h : k.cells.contains i = true) :
    k.cells.get? i = some (k.cell i) := by
  rw [Std.DHashMap.contains_eq_isSome_get?] at h
  unfold cell
  cases hg : k.cells.get? i with
  | none => simp [hg] at h
  | some c => rfl

theorem contains_of_up {k : Kernel sys} {i : σ.Id} (h : (k.cell i).up = true) :
    k.cells.contains i = true := by
  unfold cell at h
  rw [Std.DHashMap.contains_eq_isSome_get?]
  cases hg : k.cells.get? i with
  | none => simp [hg] at h
  | some c => rfl

theorem setState_of_contains {k : Kernel sys} {i : σ.Id} (h : k.cells.contains i = true)
    (s : sys.State i) : k.setState i s = k.setCell i { k.cell i with state := s } := by
  unfold setState setCell
  rw [get?_of_contains h]

theorem setState_of_not_contains {k : Kernel sys} {i : σ.Id} (h : k.cells.contains i = false)
    (s : sys.State i) : k.setState i s = k := by
  unfold setState
  have : k.cells.get? i = none := by
    rw [Std.DHashMap.contains_eq_isSome_get?] at h
    cases hg : k.cells.get? i with
    | none => rfl
    | some c => simp [hg] at h
  rw [this]

theorem cell_setState_ne (k : Kernel sys) {i j : σ.Id} (s : sys.State i) (h : j ≠ i) :
    (k.setState i s).cell j = k.cell j := by
  cases hc : k.cells.contains i
  · rw [setState_of_not_contains hc]
  · rw [setState_of_contains hc, cell_setCell, update_of_ne _ _ h]

theorem cell_setState_self {k : Kernel sys} {i : σ.Id} (h : k.cells.contains i = true)
    (s : sys.State i) : (k.setState i s).cell i = { k.cell i with state := s } := by
  rw [setState_of_contains h, cell_setCell, update_self]

theorem contains_setState (k : Kernel sys) (i j : σ.Id) (s : sys.State i) :
    (k.setState i s).cells.contains j = k.cells.contains j := by
  cases hc : k.cells.contains i
  · rw [setState_of_not_contains hc]
  · rw [setState_of_contains hc]
    simp only [setCell, Std.DHashMap.contains_insert]
    by_cases h : i = j
    · subst h; simp [hc]
    · simp [h]

theorem setState_setCell_comm {k : Kernel sys} {i b : σ.Id} (hi : k.cells.contains i = true)
    (hb : k.cells.contains b = true) (h : i ≠ b) (s : sys.State i) (c : Cell sys b) :
    (k.setState i s).setCell b c = (k.setCell b c).setState i s := by
  have hi' : (k.setCell b c).cells.contains i = true := by
    simp [setCell, Std.DHashMap.contains_insert, hi]
  rw [setState_of_contains hi, setState_of_contains hi', cell_setCell, update_of_ne _ _ h]
  simp only [setCell, DHashMap.insert_comm_of_contains hi hb h]

theorem setState_erase_comm {k : Kernel sys} {i b : σ.Id} (hi : k.cells.contains i = true)
    (h : i ≠ b) (s : sys.State i) :
    { k.setState i s with cells := (k.setState i s).cells.erase b } =
      ({ k with cells := k.cells.erase b } : Kernel sys).setState i s := by
  have hi' : (k.cells.erase b).contains i = true := by
    simp [Std.DHashMap.contains_erase, hi, Ne.symm h]
  rw [setState_of_contains (k := { k with cells := k.cells.erase b }) hi', setState_of_contains hi]
  have hcell : ({ k with cells := k.cells.erase b } : Kernel sys).cell i = k.cell i := by
    have hb : ¬ (b == i) = true := by simpa using Ne.symm h
    simp [cell, Std.DHashMap.get?_erase, hb]
  rw [hcell]
  simp only [setCell, DHashMap.erase_insert_comm_of_contains hi h]

theorem setState_comm {k : Kernel sys} {i j : σ.Id} (hi : k.cells.contains i = true)
    (hj : k.cells.contains j = true) (h : i ≠ j) (s : sys.State i) (t : sys.State j) :
    (k.setState i s).setState j t = (k.setState j t).setState i s := by
  rw [setState_of_contains (k := k.setState i s) (by rwa [contains_setState]),
    cell_setState_ne _ _ (Ne.symm h), setState_setCell_comm hi hj h, ← setState_of_contains hj]

/-! Handling a message for `b` commutes with writing a state into another actor's cell. -/

section other

variable {k : Kernel sys} {i b : σ.Id}

theorem contains_setCell (k : Kernel sys) (b j : σ.Id) (c : Cell sys b)
    (h : k.cells.contains j = true) : (k.setCell b c).cells.contains j = true := by
  simp [setCell, Std.DHashMap.contains_insert, h]

theorem perform_contains (k : Kernel sys) (b j : σ.Id) (eff : Effect σ b)
    (h : k.cells.contains j = true) : (k.perform b eff).1.cells.contains j = true := by
  cases eff <;> simp only [perform] <;> first | exact h | exact contains_setCell _ _ _ _ h

theorem perform_cell (k : Kernel sys) (b j : σ.Id) (eff : Effect σ b) (h : j ≠ b) :
    (k.perform b eff).1.cell j = k.cell j := by
  cases eff <;> simp only [perform] <;> first | rfl | (rw [cell_setCell, update_of_ne _ _ h]; rfl)

theorem perform_setState (hi : k.cells.contains i = true) (hb : k.cells.contains b = true)
    (h : i ≠ b) (s : sys.State i) (eff : Effect σ b) :
    (k.setState i s).perform b eff = ((k.perform b eff).1.setState i s, (k.perform b eff).2) := by
  cases eff with
  | send to msg => rfl
  | emit out => rfl
  | stop => rfl
  | after d msg =>
    simp only [perform, cell_setState_ne _ _ (Ne.symm h)]
    exact congrArg (·, []) (setState_setCell_comm (k := { k.unschedule _ with
      nextToken := k.nextToken + 1, agenda := (k.unschedule _).agenda.insert _ _ }) hi hb h s _)
  | cancel msg =>
    simp only [perform, cell_setState_ne _ _ (Ne.symm h)]
    exact congrArg (·, []) (setState_setCell_comm (k := k.unschedule _) hi hb h s _)

private theorem foldl_perform_setState (b : σ.Id) (hi_ne : i ≠ b) (s : sys.State i)
    (effs : List (Effect σ b)) : ∀ (k : Kernel sys) (outs : List σ.Out),
    k.cells.contains i = true → k.cells.contains b = true →
    effs.foldl (fun acc eff => ((acc.1.perform b eff).1, acc.2 ++ (acc.1.perform b eff).2))
        (k.setState i s, outs) =
      ((effs.foldl (fun acc eff => ((acc.1.perform b eff).1, acc.2 ++ (acc.1.perform b eff).2))
        (k, outs)).1.setState i s,
       (effs.foldl (fun acc eff => ((acc.1.perform b eff).1, acc.2 ++ (acc.1.perform b eff).2))
        (k, outs)).2) := by
  induction effs with
  | nil => intro k outs _ _; rfl
  | cons e es ih =>
    intro k outs hi hb
    simp only [List.foldl_cons]
    rw [perform_setState hi hb hi_ne s e]
    exact ih _ _ (perform_contains _ _ _ _ hi) (perform_contains _ _ _ _ hb)

theorem performAll_setState (hi : k.cells.contains i = true) (hb : k.cells.contains b = true)
    (h : i ≠ b) (s : sys.State i) (effs : List (Effect σ b)) :
    (k.setState i s).performAll b effs =
      ((k.performAll b effs).1.setState i s, (k.performAll b effs).2) := by
  simp only [performAll_eq]
  exact foldl_perform_setState b h s effs k [] hi hb

theorem performAll_contains (k : Kernel sys) (b j : σ.Id) (effs : List (Effect σ b))
    (h : k.cells.contains j = true) : (k.performAll b effs).1.cells.contains j = true := by
  simp only [performAll_eq]
  suffices ∀ (k : Kernel sys) (outs : List σ.Out), k.cells.contains j = true →
      (effs.foldl (fun acc eff => ((acc.1.perform b eff).1, acc.2 ++ (acc.1.perform b eff).2))
        (k, outs)).1.cells.contains j = true from this k [] h
  induction effs with
  | nil => intro k outs h; exact h
  | cons e es ih => intro k outs h; exact ih _ _ (perform_contains _ _ _ _ h)

theorem down_setState (hi : k.cells.contains i = true) (hb : k.cells.contains b = true)
    (h : i ≠ b) (s : sys.State i) : (k.setState i s).down b = (k.down b).setState i s := by
  simp only [down, cell_setState_ne _ _ (Ne.symm h)]
  exact setState_setCell_comm (k := ({ k with queue := k.queue.filter _ } : Kernel sys).unschedule _)
    hi hb h s _

theorem settle_setState (hi : k.cells.contains i = true) (hb : k.cells.contains b = true)
    (h : i ≠ b) (s : sys.State i) (r : sys.State b × List (Effect σ b)) :
    (k.setState i s).settle b r = ((k.settle b r).1.setState i s, (k.settle b r).2) := by
  have hb' := contains_setCell k b b { k.cell b with state := r.1 } hb
  have hi' := contains_setCell k b i { k.cell b with state := r.1 } hi
  rw [settle_eq, settle_eq, cell_setState_ne _ _ (Ne.symm h), setState_setCell_comm hi hb h,
    performAll_setState hi' hb' h]
  split
  · rw [down_setState (performAll_contains _ _ _ _ hi') (performAll_contains _ _ _ _ hb') h]
  · rfl

theorem rest_setState (hi : k.cells.contains i = true) (h : i ≠ b) (s : sys.State i) :
    (k.setState i s).rest b = (k.rest b).setState i s := by
  simp only [rest, cell_setState_ne _ _ (Ne.symm h)]
  split
  · exact setState_erase_comm hi h s
  · rfl

theorem handle_setState (hi : k.cells.contains i = true) (hb : k.cells.contains b = true)
    (h : i ≠ b) (s : sys.State i) (msg : σ.Msg b) :
    (k.setState i s).handle b msg = ((k.handle b msg).1.setState i s, (k.handle b msg).2) := by
  rw [handle_eq, handle_eq, cell_setState_ne _ _ (Ne.symm h), settle_setState hi hb h,
    rest_setState (by
      rw [settle_eq]; split <;> first
        | exact performAll_contains _ _ _ _ (contains_setCell _ _ _ _ hi)
        | simp only [down]; exact contains_setCell _ _ _ _
            (performAll_contains _ _ _ _ (contains_setCell _ _ _ _ hi))) h]

theorem startActor_setState (hi : k.cells.contains i = true) (hb : k.cells.contains b = true)
    (h : i ≠ b) (s : sys.State i) :
    (k.setState i s).startActor b = ((k.startActor b).1.setState i s, (k.startActor b).2) := by
  simp only [startActor, cell_setState_ne _ _ (Ne.symm h)]
  rw [setState_setCell_comm hi hb h,
    settle_setState (contains_setCell _ _ _ _ hi) (contains_setCell _ _ _ _ hb) h]

theorem fire_setState (hi : k.cells.contains i = true) (h : i ≠ b) (s : sys.State i)
    (msg : σ.Msg b) (due : Due) :
    (k.setState i s).fire b msg due =
      { k.fire b msg due with kernel := (k.fire b msg due).kernel.setState i s } := by
  rw [fire_eq, fire_eq, cell_setState_ne _ _ (Ne.symm h)]
  split
  · next hc =>
    have hb : k.cells.contains b = true := contains_of_up (by simp at hc; exact hc.1)
    have := setState_setCell_comm (k := k.unschedule [due]) hi hb h s
      { (k.cell b) with timers := (k.cell b).timers.eraseP (·.1 = msg) }
    simp only at this
    have hiK : ((k.unschedule [due]).setCell b
        { (k.cell b) with timers := (k.cell b).timers.eraseP (·.1 = msg) }).cells.contains i =
        true := contains_setCell (k.unschedule [due]) _ _ _ hi
    have hbK : ((k.unschedule [due]).setCell b
        { (k.cell b) with timers := (k.cell b).timers.eraseP (·.1 = msg) }).cells.contains b =
        true := contains_setCell (k.unschedule [due]) _ _ _ hb
    rw [show ((k.setState i s).unschedule [due]) = (k.unschedule [due]).setState i s from rfl, this,
      handle_setState hiK hbK h]
  · rfl

end other

/-! Writing a state into the cell of `i` before handling a message for `i`, or after. -/

section self

variable {k : Kernel sys} {i : σ.Id}

theorem setCell_setState {k : Kernel sys} {i : σ.Id} (hi : k.cells.contains i = true)
    (s : sys.State i) (c : Cell sys i) : (k.setState i s).setCell i c = k.setCell i c := by
  rw [setState_of_contains hi, setCell_setCell hi]

theorem setState_setCell {k : Kernel sys} {i : σ.Id} (hi : k.cells.contains i = true)
    (c : Cell sys i) (s : sys.State i) :
    (k.setCell i c).setState i s = k.setCell i { c with state := s } := by
  rw [setState_of_contains (contains_setCell _ _ _ _ hi), cell_setCell, update_self,
    setCell_setCell hi]

theorem perform_setState_self (hi : k.cells.contains i = true) (s : sys.State i)
    (eff : Effect σ i) :
    (k.setState i s).perform i eff = ((k.perform i eff).1.setState i s, (k.perform i eff).2) := by
  cases eff with
  | send to msg => rfl
  | emit out => rfl
  | stop => rfl
  | after d msg =>
    simp only [perform, cell_setState_self hi]
    rw [setState_setCell]
    · simp only [setCell, setState_of_contains hi, unschedule]
      rw [DHashMap.insert_insert_of_contains hi]
    · exact hi
  | cancel msg =>
    simp only [perform, cell_setState_self hi]
    rw [setState_setCell]
    · simp only [setCell, setState_of_contains hi, unschedule]
      rw [DHashMap.insert_insert_of_contains hi]
    · exact hi

private theorem foldl_perform_setState_self (s : sys.State i) (effs : List (Effect σ i)) :
    ∀ (k : Kernel sys) (outs : List σ.Out), k.cells.contains i = true →
    effs.foldl (fun acc eff => ((acc.1.perform i eff).1, acc.2 ++ (acc.1.perform i eff).2))
        (k.setState i s, outs) =
      ((effs.foldl (fun acc eff => ((acc.1.perform i eff).1, acc.2 ++ (acc.1.perform i eff).2))
        (k, outs)).1.setState i s,
       (effs.foldl (fun acc eff => ((acc.1.perform i eff).1, acc.2 ++ (acc.1.perform i eff).2))
        (k, outs)).2) := by
  induction effs with
  | nil => intro k outs _; rfl
  | cons e es ih =>
    intro k outs hi
    simp only [List.foldl_cons]
    rw [perform_setState_self hi s e]
    exact ih _ _ (perform_contains _ _ _ _ hi)

theorem performAll_setState_self (hi : k.cells.contains i = true) (s : sys.State i)
    (effs : List (Effect σ i)) :
    (k.setState i s).performAll i effs =
      ((k.performAll i effs).1.setState i s, (k.performAll i effs).2) := by
  simp only [performAll_eq]
  exact foldl_perform_setState_self s effs k [] hi

theorem down_setState_self (hi : k.cells.contains i = true) (s : sys.State i) :
    (k.setState i s).down i = (k.down i).setState i s := by
  simp only [down, cell_setState_self hi]
  rw [setState_setCell]
  · simp only [setCell, setState_of_contains hi, unschedule]
    rw [DHashMap.insert_insert_of_contains hi]
  · exact hi

/-- Settling a step and then writing a state in the cell is settling the step with that state:
the effects never read the state. -/
theorem setState_settle (hi : k.cells.contains i = true) (x y : sys.State i)
    (effs : List (Effect σ i)) :
    ((k.settle i (x, effs)).1.setState i y, (k.settle i (x, effs)).2) = k.settle i (y, effs) := by
  have hc := contains_setCell k i i { k.cell i with state := x } hi
  rw [settle_eq, settle_eq]
  simp only
  rw [← setState_setCell hi { k.cell i with state := x } y, performAll_setState_self hc]
  split
  · rw [down_setState_self (performAll_contains _ _ _ _ hc)]
  · rfl

theorem settle_setState_self (hi : k.cells.contains i = true) (s : sys.State i)
    (r : sys.State i × List (Effect σ i)) : (k.setState i s).settle i r = k.settle i r := by
  rw [setState_of_contains hi]
  exact settle_setCell (get?_of_contains hi) s r

theorem rest_eq_restAs (k : Kernel sys) (i : σ.Id) :
    k.rest i = k.restAs i ((sys.actor i).fresh (k.cell i).state) := rfl

theorem rest_setState_self (hi : k.cells.contains i = true) (s : sys.State i) :
    (k.setState i s).rest i = (k.restAs i ((sys.actor i).fresh s)).setState i s := by
  simp only [rest, restAs, cell_setState_self hi]
  split
  · have hcell : ({ k with cells := k.cells.erase i } : Kernel sys).cells.contains i = false := by
      simp [Std.DHashMap.contains_erase]
    rw [setState_of_not_contains hcell, setState_of_contains hi]
    simp only [setCell, DHashMap.erase_insert_of_contains hi]
  · rfl

end self

/-! What handling a message for `i` leaves of the other actors. -/

/-- Everyone but `i` has the state it had, and is up or down as it was. -/
def Frame (i : σ.Id) (k k' : Kernel sys) : Prop :=
  ∀ j, j ≠ i → (k'.cell j).state = (k.cell j).state ∧ (k'.cell j).up = (k.cell j).up

theorem Frame.trans {i : σ.Id} {a b c : Kernel sys} (h : Frame i a b) (h' : Frame i b c) :
    Frame i a c := fun j hj =>
  ⟨(h' j hj).1.trans (h j hj).1, (h' j hj).2.trans (h j hj).2⟩

theorem frame_setCell (k : Kernel sys) (i : σ.Id) (c : Cell sys i) : Frame i k (k.setCell i c) := by
  intro j hj
  simp [cell_setCell, hj]

private theorem frame_abs {i : σ.Id} {k k' : Kernel sys} {ob ob' : List σ.Out}
    (hstate : (k'.abs ob').state = update (k.abs ob).state i ((k'.abs ob').state i))
    (hup : ∀ j, j ≠ i → (k'.abs ob').up j = (k.abs ob).up j) : Frame i k k' := by
  intro j hj
  refine ⟨?_, hup j hj⟩
  have := congrFun hstate j
  simpa [hj] using this

omit [Hashable σ.Id] in
private theorem settle_up (env : EnvModel σ) (c : SysState sys) (i : σ.Id)
    (r : sys.State i × List (Effect σ i)) (j : σ.Id) (hj : j ≠ i) :
    (c.settle env i r).up j = c.up j := by
  unfold SysState.settle
  split
  · simp [SysState.down, hj]
  · simp

theorem frame_settle (k : Kernel sys) (i : σ.Id) (r : sys.State i × List (Effect σ i)) :
    Frame i k (k.settle i r).1 := by
  have h := abs_settle k [] i r
  refine frame_abs (ob := []) (ob' := (k.settle i r).2) ?_ ?_
  · rw [List.nil_append] at h
    rw [h, SysState.settle_state, update_self]
  · intro j hj
    rw [List.nil_append] at h
    rw [h, settle_up _ _ _ _ _ hj]

theorem settle_cell_state (k : Kernel sys) (i : σ.Id) (r : sys.State i × List (Effect σ i)) :
    ((k.settle i r).1.cell i).state = r.1 := by
  have h := congrArg (fun c => c.state i) (abs_settle k [] i r)
  simpa using h

theorem frame_rest (k : Kernel sys) (i : σ.Id) : Frame i k (k.rest i) := by
  intro j hj
  rcases cell_rest k i with h | ⟨-, -, -, h⟩ <;> simp [h, hj]

/-- If `i` is still up after `rest`, it was not released, and its state is as before. -/
theorem rest_up_state (k : Kernel sys) (i : σ.Id) (hup : ((k.rest i).cell i).up = true) :
    ((k.rest i).cell i).state = (k.cell i).state := by
  rcases cell_rest k i with h | ⟨-, -, -, h⟩
  · rw [h]
  · rw [h] at hup
    simp at hup

theorem frame_handle (k : Kernel sys) (i : σ.Id) (msg : σ.Msg i) :
    Frame i k (k.handle i msg).1 := by
  rw [handle_eq]
  exact (frame_settle k i _).trans (frame_rest _ i)

theorem frame_startActor (k : Kernel sys) (i : σ.Id) : Frame i k (k.startActor i).1 :=
  (frame_setCell k i _).trans (frame_settle _ i _)

theorem frame_fire (k : Kernel sys) (i : σ.Id) (msg : σ.Msg i) (due : Due) :
    Frame i k (k.fire i msg due).kernel := by
  rw [fire_eq]
  split
  · exact (frame_setCell (k.unschedule [due]) i _).trans (frame_handle _ i msg)
  · intro j _; exact ⟨rfl, rfl⟩

theorem frame_restAs (k : Kernel sys) (i : σ.Id) (fresh : Bool) : Frame i k (k.restAs i fresh) := by
  intro j hj
  simp only [restAs]
  split
  · have h' : ¬ (i == j) = true := by simpa using fun h' => hj h'.symm
    simp [cell, Std.DHashMap.get?_erase, h']
  · exact ⟨rfl, rfl⟩

/-! Writing the states a plan's steps leave. -/

theorem setState_comm' (k : Kernel sys) {i j : σ.Id} (h : i ≠ j) (s : sys.State i)
    (t : sys.State j) : (k.setState i s).setState j t = (k.setState j t).setState i s := by
  cases hi : k.cells.contains i
  · rw [setState_of_not_contains hi, setState_of_not_contains (k := k.setState j t)
      (by rw [contains_setState]; exact hi)]
  · cases hj : k.cells.contains j
    · rw [setState_of_not_contains hj, setState_of_not_contains (k := k.setState i s)
        (by rw [contains_setState]; exact hj)]
    · exact setState_comm hi hj h s t

@[simp] theorem setState_queue (k : Kernel sys) (i : σ.Id) (s : sys.State i) :
    (k.setState i s).queue = k.queue := rfl
@[simp] theorem setState_agenda (k : Kernel sys) (i : σ.Id) (s : sys.State i) :
    (k.setState i s).agenda = k.agenda := rfl
@[simp] theorem setState_clock (k : Kernel sys) (i : σ.Id) (s : sys.State i) :
    (k.setState i s).clock_ms = k.clock_ms := rfl
@[simp] theorem setState_timerTurn (k : Kernel sys) (i : σ.Id) (s : sys.State i) :
    (k.setState i s).timerTurn = k.timerTurn := rfl

theorem up_setState (k : Kernel sys) (i j : σ.Id) (s : sys.State i) :
    ((k.setState i s).cell j).up = (k.cell j).up := by
  by_cases h : j = i
  · subst h
    cases hc : k.cells.contains j
    · rw [setState_of_not_contains hc]
    · rw [cell_setState_self hc]
  · rw [cell_setState_ne _ _ h]

namespace Plan

variable {p q : Plan sys}

theorem get?_drop (p : Plan sys) (i j : σ.Id) :
    (p.drop i).steps.get? j = if i = j then none else p.steps.get? j := by
  simp [drop, Std.DHashMap.get?_erase]

theorem get?_set_ne (p : Plan sys) {i j : σ.Id} (a : Ahead sys i) (h : i ≠ j) :
    (p.set i a).steps.get? j = p.steps.get? j := by
  simp [set, Std.DHashMap.get?_insert, h]

theorem get?_set_self (p : Plan sys) (i : σ.Id) (a : Ahead sys i) :
    (p.set i a).steps.get? i = some a := by
  simp [set, Std.DHashMap.get?_insert_self]

theorem fixAt_congr {i : σ.Id} (h : p.steps.get? i = q.steps.get? i) : p.fixAt i = q.fixAt i := by
  funext k
  unfold fixAt
  rw [h]

theorem fixAt_none {i : σ.Id} (h : p.steps.get? i = none) (k : Kernel sys) : p.fixAt i k = k := by
  unfold fixAt
  rw [h]

theorem fixAll_congr (L : List σ.Id) : ∀ {p q : Plan sys} (k : Kernel sys),
    (∀ j, p.steps.get? j = q.steps.get? j) → fixAll L p k = fixAll L q k := by
  induction L with
  | nil => intro p q k _; rfl
  | cons i L ih =>
    intro p q k h
    simp only [fixAll]
    rw [fixAt_congr (h i)]
    exact ih _ fun j => by rw [get?_drop, get?_drop, h j]

theorem cell_fixAt_ne (p : Plan sys) {i j : σ.Id} (k : Kernel sys) (h : j ≠ i) :
    (p.fixAt i k).cell j = k.cell j := by
  unfold fixAt
  split
  · exact cell_setState_ne _ _ h
  · rfl

theorem up_fixAt (p : Plan sys) (i j : σ.Id) (k : Kernel sys) :
    ((p.fixAt i k).cell j).up = (k.cell j).up := by
  unfold fixAt
  split
  · exact up_setState _ _ _ _
  · rfl

theorem contains_fixAt (p : Plan sys) (i j : σ.Id) (k : Kernel sys) :
    (p.fixAt i k).cells.contains j = k.cells.contains j := by
  unfold fixAt
  split
  · exact contains_setState _ _ _ _
  · rfl

theorem fixAt_comm (p q : Plan sys) {i j : σ.Id} (h : i ≠ j) (k : Kernel sys) :
    p.fixAt i (q.fixAt j k) = q.fixAt j (p.fixAt i k) := by
  unfold fixAt
  split <;> split <;> (try simp only [cell_setState_ne _ _ h, cell_setState_ne _ _ (Ne.symm h)]) <;>
    first | rfl | exact setState_comm' _ (Ne.symm h) _ _

theorem fixAt_drop_self (p : Plan sys) (i : σ.Id) (k : Kernel sys) : (p.drop i).fixAt i k = k :=
  fixAt_none (by simp [get?_drop]) k

/-- An actor's state can be written first. -/
theorem fixAll_mem (L : List σ.Id) : ∀ {i : σ.Id} (p : Plan sys) (k : Kernel sys), i ∈ L →
    fixAll L p k = fixAll L (p.drop i) (p.fixAt i k) := by
  induction L with
  | nil => intro i p k h; cases h
  | cons j L ih =>
    intro i p k h
    by_cases hij : j = i
    · subst hij
      simp only [fixAll, fixAt_drop_self]
      exact fixAll_congr L _ fun x => by simp only [get?_drop]; split <;> rfl
    · have hL : i ∈ L := by
        cases h with
        | head => exact absurd rfl hij
        | tail _ h => exact h
      simp only [fixAll]
      rw [ih (p.drop j) (p.fixAt j k) hL,
        fixAt_congr (p := p.drop j) (q := p) (by simp [get?_drop, hij]),
        fixAt_congr (p := p.drop i) (q := p) (i := j) (by simp [get?_drop, Ne.symm hij]),
        fixAt_comm p p (Ne.symm hij)]
      exact fixAll_congr L _ fun x => by
        simp only [get?_drop]
        by_cases h1 : i = x <;> by_cases h2 : j = x <;> simp [h1, h2]

theorem fixAll_drop_fixAt {p : Plan sys} {i : σ.Id} (k : Kernel sys)
    (h : p.steps.get? i = none ∨ i ∈ p.actors) :
    p.real k = (p.drop i).real (p.fixAt i k) := by
  rcases h with h | h
  · rw [fixAt_none h]
    exact fixAll_congr _ _ fun x => by
      simp only [get?_drop]; split
      · next hx => subst hx; exact h
      · rfl
  · exact fixAll_mem _ _ _ h

/-- Writing states commutes with an operation on `b`, which has no steps in the plan, that reads
and writes no other cell. -/
theorem fixAll_local {X : Type} (b : σ.Id) (f : Kernel sys → Kernel sys × X)
    (P : Kernel sys → Prop) (hP : ∀ k j (s : sys.State j), P k → P (k.setState j s))
    (hcomm : ∀ k j (s : sys.State j), j ≠ b → k.cells.contains j = true → P k →
      f (k.setState j s) = ((f k).1.setState j s, (f k).2))
    (hstate : ∀ k j, j ≠ b → ((f k).1.cell j).state = (k.cell j).state)
    (L : List σ.Id) : ∀ (p : Plan sys) (k : Kernel sys), p.steps.get? b = none → P k →
      (∀ x a, p.steps.get? x = some a → k.cells.contains x = true) →
      fixAll L p (f k).1 = (f (fixAll L p k)).1 ∧ (f (fixAll L p k)).2 = (f k).2 := by
  induction L with
  | nil => intro p k _ _ _; exact ⟨rfl, rfl⟩
  | cons j L ih =>
    intro p k hb hk hpresent
    simp only [fixAll]
    have hj : p.fixAt j (f k).1 = (f (p.fixAt j k)).1 ∧ (f (p.fixAt j k)).2 = (f k).2 := by
      by_cases hjb : j = b
      · subst hjb; rw [fixAt_none hb, fixAt_none hb]; exact ⟨rfl, rfl⟩
      · unfold fixAt
        split
        · next heq =>
          rw [hstate k j hjb, hcomm k j _ hjb (hpresent _ _ heq) hk]
          exact ⟨rfl, rfl⟩
        · exact ⟨rfl, rfl⟩
    have hP' : P (p.fixAt j k) := by
      unfold fixAt; split
      · exact hP _ _ _ hk
      · exact hk
    have hb' : (p.drop j).steps.get? b = none := by
      rw [get?_drop]; split
      · rfl
      · exact hb
    have hpresent' : ∀ x a, (p.drop j).steps.get? x = some a →
        (p.fixAt j k).cells.contains x = true := by
      intro x a hx
      rw [get?_drop] at hx
      split at hx
      · cases hx
      · rw [contains_fixAt]; exact hpresent _ _ hx
    obtain ⟨h1, h2⟩ := ih (p.drop j) (p.fixAt j k) hb' hP' hpresent'
    rw [hj.1, h1]
    exact ⟨rfl, h2.trans hj.2⟩

/-- A plan of which no step is taken writes nothing. -/
theorem fixAll_untaken (L : List σ.Id) : ∀ (p : Plan sys) (k : Kernel sys),
    (∀ j a, p.steps.get? j = some a → a.taken = []) → fixAll L p k = k := by
  induction L with
  | nil => intro p k _; rfl
  | cons j L ih =>
    intro p k h
    simp only [fixAll]
    have : p.fixAt j k = k := by
      unfold fixAt
      split
      · next heq => cases h _ _ heq
      · rfl
    rw [this]
    exact ih _ _ fun x a hx => by
      rw [get?_drop] at hx
      split at hx
      · cases hx
      · exact h _ _ hx

theorem up_fixAll (L : List σ.Id) : ∀ (p : Plan sys) (k : Kernel sys) (j : σ.Id),
    ((fixAll L p k).cell j).up = (k.cell j).up := by
  induction L with
  | nil => intro p k j; rfl
  | cons i L ih => intro p k j; simp only [fixAll]; rw [ih, up_fixAt]

theorem cell_fixAll_none (L : List σ.Id) : ∀ (p : Plan sys) (k : Kernel sys) {j : σ.Id},
    p.steps.get? j = none → (fixAll L p k).cell j = k.cell j := by
  induction L with
  | nil => intro p k j _; rfl
  | cons i L ih =>
    intro p k j hj
    simp only [fixAll]
    rw [ih _ _ (by rw [get?_drop]; split <;> first | rfl | exact hj)]
    by_cases h : j = i
    · subst h; rw [fixAt_none hj]
    · exact cell_fixAt_ne _ _ h

theorem cell_fixAt_self {p : Plan sys} {i : σ.Id} {a : Ahead sys i} (h : p.steps.get? i = some a)
    {k : Kernel sys} (hi : k.cells.contains i = true) :
    (p.fixAt i k).cell i = { k.cell i with state := replay sys i (k.cell i).state a.taken.reverse } := by
  unfold fixAt
  rw [h]
  cases a with
  | mk taken steps last =>
    cases taken with
    | nil => rfl
    | cons m ms => exact cell_setState_self hi _

theorem cell_real {p : Plan sys} {i : σ.Id} {a : Ahead sys i} (h : p.steps.get? i = some a)
    (hm : i ∈ p.actors) {k : Kernel sys} (hi : k.cells.contains i = true) :
    (p.real k).cell i = { k.cell i with state := replay sys i (k.cell i).state a.taken.reverse } := by
  rw [fixAll_drop_fixAt k (.inr hm), real, cell_fixAll_none _ _ _ (by simp [get?_drop])]
  exact cell_fixAt_self h hi

theorem fixAll_with (L : List σ.Id) (g : Kernel sys → Kernel sys) (hg : ∀ k, (g k).cells = k.cells)
    (hs : ∀ k j (s : sys.State j), g (k.setState j s) = (g k).setState j s) :
    ∀ (p : Plan sys) (k : Kernel sys), fixAll L p (g k) = g (fixAll L p k) := by
  induction L with
  | nil => intro p k; rfl
  | cons i L ih =>
    intro p k
    simp only [fixAll]
    have : p.fixAt i (g k) = g (p.fixAt i k) := by
      unfold fixAt
      split
      · have hc : (g k).cell i = k.cell i := by simp only [cell, hg]
        rw [hc, hs]
      · rfl
    rw [this, ih]

end Plan

/-! With a plan, a batch is `runBatch`'s. -/

omit [Hashable σ.Id] in
theorem replay_snoc (i : σ.Id) (ms : List (σ.Msg i)) (m : σ.Msg i) : ∀ s : sys.State i,
    replay sys i s (ms ++ [m]) = ((sys.actor i).step (replay sys i s ms) m).1 := by
  induction ms with
  | nil => intro s; rfl
  | cons x ms ih => intro s; exact ih _

theorem settle_contains (k : Kernel sys) (i j : σ.Id) (r : sys.State i × List (Effect σ i))
    (h : k.cells.contains j = true) : (k.settle i r).1.cells.contains j = true := by
  rw [settle_eq]
  split
  · simp only [down]
    exact contains_setCell _ _ _ _ (performAll_contains _ _ _ _ (contains_setCell _ _ _ _ h))
  · exact performAll_contains _ _ _ _ (contains_setCell _ _ _ _ h)

theorem settle_contains_self (k : Kernel sys) (i : σ.Id) (r : sys.State i × List (Effect σ i)) :
    (k.settle i r).1.cells.contains i = true := by
  rw [settle_eq]
  have h : (k.setCell i { k.cell i with state := r.1 }).cells.contains i = true := by
    simp [setCell, Std.DHashMap.contains_insert]
  split
  · simp only [down]
    exact contains_setCell _ _ _ _ (performAll_contains _ _ _ _ h)
  · exact performAll_contains _ _ _ _ h

namespace Plan

variable {p : Plan sys} {k : Kernel sys}

theorem Good.present (hp : p.Good k) {x : σ.Id} {a : Ahead sys x} (h : p.steps.get? x = some a) :
    k.cells.contains x = true :=
  contains_of_up (hp x a h).2.1

/-- A plan stays good where only `i` moved, if what it now holds for `i` fits `i`. -/
theorem Good.frame {p' : Plan sys} {k' : Kernel sys} {i : σ.Id} (hp : p.Good k)
    (hf : Frame i k k') (hact : p'.actors = p.actors)
    (hget : ∀ j, j ≠ i → p'.steps.get? j = p.steps.get? j)
    (hi : ∀ a, p'.steps.get? i = some a → i ∈ p.actors ∧ (k'.cell i).up = true ∧
      Fits sys i (replay sys i (k'.cell i).state a.taken.reverse) a.steps a.last) :
    p'.Good k' := by
  intro j a hj
  rw [hact]
  by_cases hji : j = i
  · subst hji; exact hi a hj
  · rw [hget j hji] at hj
    rw [(hf j hji).1, (hf j hji).2]
    exact hp j a hj

theorem Good.drop (hp : p.Good k) {k' : Kernel sys} {i : σ.Id} (hf : Frame i k k') :
    (p.drop i).Good k' :=
  hp.frame hf rfl (fun j hj => by simp [get?_drop, Ne.symm hj]) (fun a h => by simp [get?_drop] at h)

theorem handle_real (hp : p.Good k) {i : σ.Id} (hi : p.steps.get? i = none)
    (hc : k.cells.contains i = true) (msg : σ.Msg i) :
    (p.real (k.handle i msg).1, (k.handle i msg).2) = (p.real k).handle i msg := by
  obtain ⟨h1, h2⟩ := fixAll_local i (fun k => k.handle i msg) (fun k => k.cells.contains i = true)
    (fun k j s h => by rw [contains_setState]; exact h)
    (fun k j s hj hjc hic => handle_setState hjc hic hj s msg)
    (fun k j hj => (frame_handle k i msg j hj).1) p.actors p k hi hc (fun _ _ h => hp.present h)
  exact Prod.ext h1 h2.symm

theorem startActor_real (hp : p.Good k) {i : σ.Id} (hi : p.steps.get? i = none)
    (hc : k.cells.contains i = true) :
    (p.real (k.startActor i).1, (k.startActor i).2) = (p.real k).startActor i := by
  obtain ⟨h1, h2⟩ := fixAll_local i (fun k => k.startActor i) (fun k => k.cells.contains i = true)
    (fun k j s h => by rw [contains_setState]; exact h)
    (fun k j s hj hjc hic => startActor_setState hjc hic hj s)
    (fun k j hj => (frame_startActor k i j hj).1) p.actors p k hi hc (fun _ _ h => hp.present h)
  exact Prod.ext h1 h2.symm

theorem fire_real (hp : p.Good k) {i : σ.Id} (hi : p.steps.get? i = none) (msg : σ.Msg i)
    (due : Due) :
    { k.fire i msg due with kernel := p.real (k.fire i msg due).kernel } =
      (p.real k).fire i msg due := by
  obtain ⟨h1, h2⟩ := fixAll_local i
    (fun k => ((k.fire i msg due).kernel, (k.fire i msg due).events, (k.fire i msg due).outputs))
    (fun _ => True) (fun _ _ _ _ => trivial)
    (fun k j s hj hjc _ => by rw [fire_setState hjc hj s msg due])
    (fun k j hj => (frame_fire k i msg due j hj).1) p.actors p k hi trivial
    (fun _ _ h => hp.present h)
  simp only [Prod.mk.injEq] at h2
  rw [real, h1]
  cases hf : (fixAll p.actors p k).fire i msg due
  rw [hf] at h2
  simp only at h2 ⊢
  rw [← h2.1, ← h2.2]
  exact hf.symm

theorem frame_fixAt (p : Plan sys) (i : σ.Id) (k : Kernel sys) : Frame i k (p.fixAt i k) :=
  fun j hj => by rw [cell_fixAt_ne _ _ hj]; exact ⟨rfl, rfl⟩

theorem fixAt_settle_self {i : σ.Id} (hi : k.cells.contains i = true)
    (r : sys.State i × List (Effect σ i)) : (p.fixAt i k).settle i r = k.settle i r := by
  unfold fixAt
  split
  · exact settle_setState_self hi _ r
  · rfl

/-- Writing the state of `i` and handling `msg` as `handle` does is handling `msg` in the kernel
`runBatch` has. -/
theorem fixAt_handle (hp : p.Good k) {i : σ.Id} {a : Ahead sys i} (h : p.steps.get? i = some a)
    (msg : σ.Msg i) :
    ((p.drop i).real ((p.fixAt i k).handle i msg).1, ((p.fixAt i k).handle i msg).2) =
        (p.real k).handle i msg ∧
      (p.drop i).Good ((p.fixAt i k).handle i msg).1 ∧ (p.drop i).actors = p.actors := by
  have hc := hp.present h
  have hgood : (p.drop i).Good (p.fixAt i k) := hp.drop (frame_fixAt p i k)
  refine ⟨?_, hp.drop ((frame_fixAt p i k).trans (frame_handle _ i msg)), rfl⟩
  rw [fixAll_drop_fixAt k (.inr (hp i a h).1)]
  exact handle_real hgood (by simp [get?_drop]) (by rw [contains_fixAt]; exact hc) msg

/-- The step the kernel takes from the plan for `i`, read as `runBatch`'s: from the state the
steps taken leave. -/
theorem handle_planned (hp : p.Good k) {i : σ.Id} {a : Ahead sys i} (h : p.steps.get? i = some a)
    (msg : σ.Msg i) :
    (p.real k).handle i msg =
      ((p.drop i).real ((k.settle i ((sys.actor i).step
          (replay sys i (k.cell i).state a.taken.reverse) msg)).1.rest i),
        (k.settle i ((sys.actor i).step
          (replay sys i (k.cell i).state a.taken.reverse) msg)).2) := by
  have hc := hp.present h
  rw [← (fixAt_handle hp h msg).1, handle_eq, cell_fixAt_self h hc, fixAt_settle_self hc]

theorem restAs_cases (k : Kernel sys) (i : σ.Id) (fresh : Bool) :
    k.restAs i fresh = k ∨ (k.restAs i fresh).cells.contains i = false := by
  simp only [restAs]
  split
  · exact .inr (by simp [Std.DHashMap.contains_erase])
  · exact .inl rfl

theorem fixAt_set_taken {i : σ.Id} (a : Ahead sys i) (m : σ.Msg i) (steps : Steps σ i)
    (k : Kernel sys) :
    (p.set i { a with taken := m :: a.taken, steps }).fixAt i k =
      k.setState i (replay sys i (k.cell i).state (a.taken.reverse ++ [m])) := by
  unfold fixAt
  rw [get?_set_self]
  simp

theorem real_set_drop {i : σ.Id} (a : Ahead sys i) (k : Kernel sys) :
    ((p.set i a).drop i).real k = (p.drop i).real k :=
  fixAll_congr _ _ fun j => by
    simp only [get?_drop]
    split
    · rfl
    · next h => exact get?_set_ne _ _ h

/-- A step of `i` that is not its last: the cell keeps its state, and the plan the steps taken. -/
theorem handle_mid (hp : p.Good k) {i : σ.Id} {a : Ahead sys i} (ha : p.steps.get? i = some a)
    {m : σ.Msg i} {effs : List (Effect σ i)} {fresh : Bool} {rest : Steps σ i}
    (heffs : effs = ((sys.actor i).step (replay sys i (k.cell i).state a.taken.reverse) m).2)
    (hfresh : fresh = (sys.actor i).fresh
      ((sys.actor i).step (replay sys i (k.cell i).state a.taken.reverse) m).1)
    (hrest : Fits sys i ((sys.actor i).step (replay sys i (k.cell i).state a.taken.reverse) m).1
      rest a.last) :
    let K := (k.settle i ((k.cell i).state, effs)).1.restAs i fresh
    let p' := p.set i { a with taken := m :: a.taken, steps := rest }
    let r : Kernel sys × Plan sys × List σ.Out :=
      if (K.cell i).up then (K, p', (k.settle i ((k.cell i).state, effs)).2)
      else (p'.fixAt i K, p'.drop i, (k.settle i ((k.cell i).state, effs)).2)
    (r.2.1.real r.1, r.2.2) = (p.real k).handle i m ∧ r.2.1.Good r.1 ∧ r.2.1.actors = p.actors := by
  intro K p' r
  have hc := hp.present ha
  have hm := (hp i a ha).1
  generalize hs : replay sys i (k.cell i).state a.taken.reverse = s at heffs hfresh hrest
  have hstep : (sys.actor i).step s m = (((sys.actor i).step s m).1, effs) := by rw [heffs]
  generalize hs' : ((sys.actor i).step s m).1 = s' at hstep hfresh hrest
  have hreplay : replay sys i (k.cell i).state (a.taken.reverse ++ [m]) = s' := by
    rw [replay_snoc, hs, hs']
  have hZc := settle_contains_self k i ((k.cell i).state, effs)
  have hZs := settle_cell_state k i ((k.cell i).state, effs)
  have hR : (p.real k).handle i m = ((p.drop i).real (K.setState i s'),
      (k.settle i ((k.cell i).state, effs)).2) := by
    rw [handle_planned hp ha, hs, hstep, ← setState_settle hc ((k.cell i).state) s' effs]
    simp only
    rw [rest_setState_self hZc, ← hfresh]
  have hfix : p'.fixAt i K = K.setState i s' := by
    rw [fixAt_set_taken]
    rcases restAs_cases (k.settle i ((k.cell i).state, effs)).1 i fresh with hK | hK
    · simp only [K, hK, hZs, hreplay]
    · rw [setState_of_not_contains hK, setState_of_not_contains hK]
  have hframe : Frame i k K := (frame_settle k i _).trans (frame_restAs _ i fresh)
  simp only [r]
  split
  · next hup =>
    have hK : K = (k.settle i ((k.cell i).state, effs)).1 := by
      rcases restAs_cases (k.settle i ((k.cell i).state, effs)).1 i fresh with hK | hK
      · exact hK
      · exact absurd (contains_of_up hup) (by simp only [K] at hK ⊢; rw [hK]; simp)
    refine ⟨?_, ?_, rfl⟩
    · dsimp only
      rw [hR, fixAll_drop_fixAt K (p := p') (.inr hm), hfix, real_set_drop]
    · refine hp.frame hframe rfl (fun j hj => get?_set_ne _ _ (Ne.symm hj)) (fun a' h => ?_)
      rw [get?_set_self] at h
      cases h
      refine ⟨hm, hup, ?_⟩
      simp only [List.reverse_cons]
      rw [hK, hZs, hreplay]
      exact hrest
  · refine ⟨?_, ?_, rfl⟩
    · dsimp only
      rw [hR, hfix, real_set_drop]
    · exact hp.frame ((hframe.trans (frame_fixAt p' i K))) rfl
        (fun j hj => by rw [get?_drop, get?_set_ne _ _ (Ne.symm hj)]; simp [Ne.symm hj])
        (fun a' h => by simp [get?_drop] at h)

end Plan

open Plan

/-- With a good plan, handling a message for an actor that is up is `handle` in the kernel
`runBatch` has, and the plan stays good. -/
theorem handleAhead_eq {k : Kernel sys} {p : Plan sys} (hp : p.Good k) {i : σ.Id}
    (hup : (k.cell i).up = true) (msg : σ.Msg i) :
    ((k.handleAhead p i msg).2.1.real (k.handleAhead p i msg).1, (k.handleAhead p i msg).2.2) =
        (p.real k).handle i msg ∧
      (k.handleAhead p i msg).2.1.Good (k.handleAhead p i msg).1 ∧
      (k.handleAhead p i msg).2.1.actors = p.actors := by
  unfold handleAhead
  split
  · next hnone =>
    exact ⟨handle_real hp hnone (contains_of_up hup) msg,
      hp.frame (frame_handle k i msg) rfl (fun _ _ => rfl)
        (fun a h => by rw [hnone] at h; cases h), rfl⟩
  · next a ha =>
    split
    · next m effs fresh rest hsteps =>
      have hfit := (hp i a ha).2.2
      rw [hsteps] at hfit
      obtain ⟨heffs, hfresh, hrest⟩ := hfit
      split
      · next hm =>
        subst hm
        split
        · have hm : (match k.settle i (a.last, effs) with
                | (k, outs) => (k.rest i, p.drop i, outs)) =
              ((k.settle i (a.last, effs)).1.rest i, p.drop i, (k.settle i (a.last, effs)).2) := rfl
          rw [hm]
          have hstep : (sys.actor i).step (replay sys i (k.cell i).state a.taken.reverse) m =
              (a.last, effs) := Prod.ext hrest.symm heffs.symm
          refine ⟨?_, hp.drop ((frame_settle k i _).trans (frame_rest _ i)), rfl⟩
          rw [handle_planned hp ha, hstep]
        · exact handle_mid hp ha heffs hfresh hrest
      · exact fixAt_handle hp ha msg
    · exact fixAt_handle hp ha msg

theorem real_queue (p : Plan sys) (k : Kernel sys) (q : Fifo (Envelope σ)) :
    p.real { k with queue := q } = { p.real k with queue := q } :=
  fixAll_with _ (fun k => { k with queue := q }) (fun _ => rfl) (fun _ _ _ => rfl) _ _

theorem real_timerTurn (p : Plan sys) (k : Kernel sys) (t : Bool) :
    p.real { k with timerTurn := t } = { p.real k with timerTurn := t } :=
  fixAll_with _ (fun k => { k with timerTurn := t }) (fun _ => rfl) (fun _ _ _ => rfl) _ _

theorem fixAll_fields (L : List σ.Id) : ∀ (p : Plan sys) (k : Kernel sys),
    (fixAll L p k).queue = k.queue ∧ (fixAll L p k).agenda = k.agenda ∧
      (fixAll L p k).clock_ms = k.clock_ms ∧ (fixAll L p k).timerTurn = k.timerTurn := by
  induction L with
  | nil => intro p k; exact ⟨rfl, rfl, rfl, rfl⟩
  | cons i L ih =>
    intro p k
    simp only [fixAll]
    obtain ⟨h1, h2, h3, h4⟩ := ih (p.drop i) (p.fixAt i k)
    rw [h1, h2, h3, h4]
    unfold fixAt
    split <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem timerNext_real (p : Plan sys) (k : Kernel sys) : (p.real k).timerNext = k.timerNext := by
  obtain ⟨h1, h2, h3, h4⟩ := fixAll_fields p.actors p k
  simp only [timerNext, real, h1, h2, h3, h4]

theorem wait_real (p : Plan sys) (k : Kernel sys) : (p.real k).wait = k.wait := by
  obtain ⟨h1, h2, h3, -⟩ := fixAll_fields p.actors p k
  simp only [wait, real, h1, h2, h3]

theorem Plan.Good.reset {p : Plan sys} {k : Kernel sys} (hp : p.Good k) :
    p.reset.Good (p.real k) := by
  intro j a hj
  simp only [Plan.reset, Std.DHashMap.get?_map] at hj
  cases hj' : p.steps.get? j with
  | none => rw [hj'] at hj; cases hj
  | some b =>
    rw [hj'] at hj
    cases hj
    obtain ⟨hm, hup, hfit⟩ := hp j b hj'
    refine ⟨hm, by rw [real, up_fixAll]; exact hup, ?_⟩
    rw [cell_real hj' hm (contains_of_up hup)]
    exact hfit

theorem Plan.real_reset (p : Plan sys) (k : Kernel sys) : p.reset.real k = k :=
  fixAll_untaken _ _ _ fun j a h => by
    simp only [reset, Std.DHashMap.get?_map] at h
    cases hj : p.steps.get? j with
    | none => rw [hj] at h; cases h
    | some b => rw [hj] at h; cases h; rfl

theorem run1Ahead_eq {k : Kernel sys} {p : Plan sys} (hp : p.Good k) :
    { (k.run1Ahead p).1 with kernel := (k.run1Ahead p).2.real (k.run1Ahead p).1.kernel } =
        (p.real k).run1 ∧
      (k.run1Ahead p).2.Good (k.run1Ahead p).1.kernel ∧ (k.run1Ahead p).2.actors = p.actors := by
  rw [run1_eq]
  unfold run1Ahead
  obtain ⟨hq, -, -, -⟩ := fixAll_fields p.actors p k
  simp only [real] at hq ⊢
  rw [hq]
  cases hpop : k.queue.pop? with
  | none => exact ⟨rfl, hp, rfl⟩
  | some v =>
    obtain ⟨e, rest⟩ := v
    simp only [up_fixAll]
    by_cases hup : (k.cell e.dst).up = true
    · simp only [hup, ite_true]
      have hp' : p.Good { k with queue := rest } := hp
      obtain ⟨heq, hgood, hact⟩ := handleAhead_eq hp' (k := { k with queue := rest }) hup e.msg
      have hrq := real_queue p k rest
      simp only [real] at hrq heq
      rw [hrq] at heq
      rw [← heq]
      exact ⟨rfl, hgood, hact⟩
    · simp only [hup, Bool.false_eq_true, ite_false]
      have hnone : p.steps.get? e.dst = none := by
        cases h : p.steps.get? e.dst with
        | none => rfl
        | some a => exact absurd (hp _ a h).2.1 hup
      split
      · next hc =>
        have := startActor_real hp hnone hc
        simp only [real] at this
        rw [← this]
        exact ⟨rfl, hp.frame (frame_startActor k e.dst) rfl (fun _ _ => rfl)
          (fun a h => by rw [hnone] at h; cases h), rfl⟩
      · refine ⟨?_, ?_, rfl⟩
        · rw [show fixAll p.reset.actors p.reset ((fixAll p.actors p k).startActor e.dst).1 =
            ((fixAll p.actors p k).startActor e.dst).1 from Plan.real_reset p _]
        · have hg := hp.reset
          refine hg.frame (frame_startActor (p.real k) e.dst) rfl (fun _ _ => rfl) (fun a h => ?_)
          simp only [reset, Std.DHashMap.get?_map, hnone] at h
          cases h

theorem stepAhead_eq {k : Kernel sys} {p : Plan sys} (hp : p.Good k) :
    { (k.stepAhead p).1 with kernel := (k.stepAhead p).2.real (k.stepAhead p).1.kernel } =
        (p.real k).step ∧
      (k.stepAhead p).2.Good (k.stepAhead p).1.kernel ∧ (k.stepAhead p).2.actors = p.actors := by
  unfold stepAhead step
  rw [timerNext_real]
  cases ht : k.timerNext with
  | some v =>
    obtain ⟨due, i, msg⟩ := v
    simp only
    have h1 : p.real k = (p.drop i).real (p.fixAt i k) := fixAll_drop_fixAt k (by
      cases h : p.steps.get? i with
      | none => exact .inl rfl
      | some a => exact .inr (hp _ _ h).1)
    have hgood : (p.drop i).Good { p.fixAt i k with timerTurn := false } :=
      hp.drop (frame_fixAt p i k)
    rw [h1, ← real_timerTurn]
    exact ⟨fire_real hgood (by simp [get?_drop]) msg due,
      hp.drop ((frame_fixAt p i k).trans (frame_fire _ i msg due)), rfl⟩
  | none =>
    simp only
    rw [← real_timerTurn]
    exact run1Ahead_eq (k := { k with timerTurn := true }) hp

/-- With a good plan, a batch is `runBatch`'s in the kernel `runBatch` has, value for value, once
the states the steps taken leave are written. -/
theorem runBatchAhead_eq {k : Kernel sys} {p : Plan sys} (hp : p.Good k) (fuel : Nat) :
    { (k.runBatchAhead p fuel).1 with
        kernel := (k.runBatchAhead p fuel).2.real (k.runBatchAhead p fuel).1.kernel } =
        (p.real k).runBatch fuel ∧
      (k.runBatchAhead p fuel).2.Good (k.runBatchAhead p fuel).1.kernel ∧
      (k.runBatchAhead p fuel).2.actors = p.actors := by
  induction fuel generalizing k p with
  | zero => exact ⟨rfl, hp, rfl⟩
  | succ fuel ih =>
    rw [runBatch_succ, wait_real]
    unfold runBatchAhead
    split
    · obtain ⟨h1, h2, h3⟩ := stepAhead_eq hp
      rw [← h1]
      generalize k.stepAhead p = s at h2 h3 ⊢
      obtain ⟨⟨kernel, events, outputs⟩, p'⟩ := s
      obtain ⟨r1, r2, r3⟩ := ih h2
      simp only at h2 h3 r1 r2 r3 ⊢
      rw [← r1]
      generalize kernel.runBatchAhead p' fuel = t at r2 r3 ⊢
      obtain ⟨⟨kernel', later, more⟩, p''⟩ := t
      simp only at r2 r3 ⊢
      exact ⟨by first | rfl | trivial, r2, r3.trans h3⟩
    · exact ⟨rfl, hp, rfl⟩

theorem Plan.good_add {k : Kernel sys} {actors : List σ.Id} (done : List (Done k actors)) :
    ∀ p : Plan sys, p.actors = actors → p.Good k → (∀ j a, p.steps.get? j = some a → a.taken = []) →
      (p.add done).actors = actors ∧ (p.add done).Good k ∧
        (∀ j a, (p.add done).steps.get? j = some a → a.taken = []) := by
  induction done with
  | nil => intro p h1 h2 h3; exact ⟨h1, h2, h3⟩
  | cons d done ih =>
    intro p hact hp htaken
    apply ih (p.set d.1.1 d.1.2) hact
    · refine hp.frame (fun _ _ => ⟨rfl, rfl⟩) rfl (fun j hj => get?_set_ne _ _ (Ne.symm hj))
        (fun a h => ?_)
      rw [get?_set_self] at h
      cases h
      obtain ⟨hm, hup, ht, hfit⟩ := d.2
      refine ⟨hact ▸ hm, hup, ?_⟩
      rw [ht]
      exact hfit
    · intro j a h
      by_cases hj : d.1.1 = j
      · subst hj; rw [get?_set_self] at h; cases h; exact d.2.2.2.1
      · rw [get?_set_ne _ _ hj] at h; exact htaken _ _ h

/-- The plan `plan` builds fits the kernel, whatever the number of workers and however the actors
are cut into pieces, and no step of it is taken. -/
theorem good_plan (k : Kernel sys) (spread : Spread) (wave : List (Envelope σ)) :
    (k.plan spread wave).Good k ∧ (k.plan spread wave).real k = k := by
  have hempty : ({} : Plan sys).Good k ∧ ({} : Plan sys).real k = k :=
    ⟨fun _ _ h => by simp at h, rfl⟩
  suffices (k.plan spread wave).Good k ∧
      ∀ j a, (k.plan spread wave).steps.get? j = some a → a.taken = [] from
    ⟨this.1, fixAll_untaken _ _ _ this.2⟩
  unfold plan
  dsimp only
  split
  · exact ⟨hempty.1, fun _ _ h => by simp at h⟩
  · split
    · exact ⟨hempty.1, fun _ _ h => by simp at h⟩
    · rename_i first others hc
      clear hc
      obtain ⟨h0a, h0g, h0t⟩ := Plan.good_add (first.map Job.run)
        { actors := (mail wave).toList.map Sigma.fst } rfl (fun _ _ h => by simp at h)
        (fun _ _ h => by simp at h)
      generalize Plan.add { actors := (mail wave).toList.map Sigma.fst } (first.map Job.run) = p
        at h0a h0g h0t
      induction others generalizing p with
      | nil => exact ⟨h0g, h0t⟩
      | cons t others ih =>
        obtain ⟨h1, h2, h3⟩ := Plan.good_add _ p h0a h0g h0t
        exact ih _ h1 h2 h3

/-! Waves. -/

theorem runBatch_of_wait {k : Kernel sys} (h : k.wait ≠ .none) (fuel : Nat) :
    k.runBatch fuel = { kernel := k } := by
  cases fuel with
  | zero => rfl
  | succ fuel => rw [runBatch_succ, ite_eq_right_iff.mpr (fun h' => absurd h' h)]

/-- Doing `a` units of work and then `b` is doing `a + b`. -/
theorem runBatch_add (k : Kernel sys) (a b : Nat) :
    k.runBatch (a + b) =
      { kernel := ((k.runBatch a).kernel.runBatch b).kernel
        events := (k.runBatch a).events ++ ((k.runBatch a).kernel.runBatch b).events
        outputs := (k.runBatch a).outputs ++ ((k.runBatch a).kernel.runBatch b).outputs } := by
  induction a generalizing k with
  | zero => rw [Nat.zero_add]; rfl
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega, runBatch_succ, runBatch_succ]
    split
    · simp only [ih, List.append_assoc]
    · next h => simp [runBatch_of_wait h]

/-- Up to `fuel` units of work, a wave at a time, each wave's steps worked out as `spread` says
before the kernel takes them in order. At the end of a wave the kernel writes the state of each
actor whose last step it did not take. -/
def waves (k : Kernel sys) (spread : Spread) (fuel : Nat) : Step sys :=
  if _h : fuel = 0 then { kernel := k }
  else if k.wait = .none then
    let n := min fuel (max 1 k.queue.length)
    match k.runBatchAhead (k.plan spread (k.queue.toList.take n)) n with
    | ({ kernel, events, outputs }, p) =>
      match waves (p.real kernel) spread (fuel - n) with
      | { kernel, events := later, outputs := more } =>
        { kernel, events := events ++ later, outputs := outputs ++ more }
  else { kernel := k }
termination_by fuel
decreasing_by omega

/-- `runBatch`, its actors' steps worked out in parallel when there are `workers` threads to do
it; on one, `runBatch` itself. -/
def runWaves (k : Kernel sys) (spread : Spread) (fuel : Nat) : Step sys :=
  if spread.workers ≤ 1 then k.runBatch fuel else k.waves spread fuel

/-- A wave is `runBatch` on its units of work. -/
theorem wave_eq (k : Kernel sys) (spread : Spread) (n : Nat) (wave : List (Envelope σ)) :
    { (k.runBatchAhead (k.plan spread wave) n).1 with
        kernel := (k.runBatchAhead (k.plan spread wave) n).2.real
          (k.runBatchAhead (k.plan spread wave) n).1.kernel } = k.runBatch n := by
  have h := (runBatchAhead_eq (good_plan k spread wave).1 n).1
  rw [(good_plan k spread wave).2] at h
  exact h

theorem waves_eq (k : Kernel sys) (spread : Spread) (fuel : Nat) :
    k.waves spread fuel = k.runBatch fuel := by
  induction fuel using Nat.strongRecOn generalizing k with
  | _ fuel ih =>
    rw [waves]
    split
    · next h => subst h; rfl
    · split
      · next hw =>
        simp only
        have hn : 0 < min fuel (max 1 k.queue.length) := by omega
        have hwave := wave_eq k spread (min fuel (max 1 k.queue.length))
          (k.queue.toList.take (min fuel (max 1 k.queue.length)))
        conv => rhs; rw [show fuel = min fuel (max 1 k.queue.length)
          + (fuel - min fuel (max 1 k.queue.length)) by omega]
        rw [runBatch_add, ← hwave]
        generalize k.runBatchAhead _ _ = s
        obtain ⟨⟨kernel, events, outputs⟩, p⟩ := s
        simp only
        rw [ih _ (by omega)]
      · next hw => exact (runBatch_of_wait hw fuel).symm

/-- However a batch's waves are spread, over however many workers in pieces of whatever size, a
batch of waves is `runBatch`: the same kernel, the same events and the same outputs, in the same
order. -/
theorem runWaves_eq (k : Kernel sys) (spread : Spread) (fuel : Nat) :
    k.runWaves spread fuel = k.runBatch fuel := by
  unfold runWaves
  split
  · rfl
  · exact waves_eq k spread fuel

/-- Every input, in order. -/
def acceptAll (k : Kernel sys) : List σ.In → Kernel sys
  | [] => k
  | x :: xs => (k.accept x).kernel.acceptAll xs

theorem exec_inputs (k : Kernel sys) (inputs : List σ.In) :
    k.exec (inputs.map .input) =
      { kernel := k.acceptAll inputs, events := inputs.map .input, outputs := [] } := by
  induction inputs generalizing k with
  | nil => rfl
  | cons x xs ih =>
    rw [List.map_cons, exec_cons, ih]
    rfl

end Kernel

end Lanes
