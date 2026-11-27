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
first, timers in their turn, effects performed one actor after another, but takes each step from
the plan instead of calling `step` (`Kernel.runBatchAhead`). A step is taken from the plan only
while it is the plan's next message that is delivered and the actor has done nothing since the
wave began but take the plan's steps; a start, a timer or another message drops the actor's plan
and its steps are taken as usual.

So the work done is `runBatch`'s, value for value (`Kernel.runWaves_eq`): the journal, replay,
snapshots and every theorem about the kernel are unchanged, and which thread worked out a step
cannot be told. What makes it so is that handling a message for one actor changes no other
actor's state or whether it is up (`Kernel.Frame`).
-/

@[expose] public section

namespace Lanes

variable {σ : Signature}

namespace Kernel

variable {sys : System σ} [Hashable σ.Id]

/-- An actor's steps worked out ahead: each message with `step`'s answer to it, from the state
the answer before it leaves. -/
abbrev Ahead (sys : System σ) (i : σ.Id) := List (σ.Msg i × (sys.State i × List (Effect σ i)))

def ahead (sys : System σ) (i : σ.Id) : sys.State i → List (σ.Msg i) → Ahead sys i
  | _, [] => []
  | s, m :: ms =>
    let r := (sys.actor i).step s m
    (m, r) :: ahead sys i r.1 ms

/-- Each answer is `step`'s from the state the answer before it leaves, the first from `s`. -/
def Fits (sys : System σ) (i : σ.Id) : sys.State i → Ahead sys i → Prop
  | _, [] => True
  | s, (m, r) :: rest => r = (sys.actor i).step s m ∧ Fits sys i r.1 rest

omit [Hashable σ.Id] in
theorem fits_ahead (i : σ.Id) (s : sys.State i) (ms : List (σ.Msg i)) :
    Fits sys i s (ahead sys i s ms) := by
  induction ms generalizing s with
  | nil => trivial
  | cons m ms ih => exact ⟨rfl, ih _⟩

/-- The steps worked out ahead for some of the actors. -/
structure Plan (sys : System σ) [Hashable σ.Id] where
  steps : Std.DHashMap σ.Id (Ahead sys) := ∅

namespace Plan

def get (p : Plan sys) (i : σ.Id) : Ahead sys i :=
  (p.steps.get? i).getD []

def set (p : Plan sys) (i : σ.Id) (a : Ahead sys i) : Plan sys :=
  ⟨p.steps.insert i a⟩

def drop (p : Plan sys) (i : σ.Id) : Plan sys :=
  ⟨p.steps.erase i⟩

/-- What the plan holds of each actor fits it as the kernel has it: it is up, and the plan's
steps start from its state. -/
def Good (p : Plan sys) (k : Kernel sys) : Prop :=
  ∀ i, p.get i = [] ∨ ((k.cell i).up = true ∧ Fits sys i (k.cell i).state (p.get i))

theorem get_set (p : Plan sys) (i : σ.Id) (a : Ahead sys i) : (p.set i a).get = update p.get i a := by
  funext j
  by_cases h : j = i
  · subst h
    simp [get, set, Std.DHashMap.get?_insert_self]
  · have h' : ¬ i = j := fun h' => h h'.symm
    simp [get, set, Std.DHashMap.get?_insert, h, h']

theorem get_drop (p : Plan sys) (i : σ.Id) : (p.drop i).get = update p.get i [] := by
  funext j
  by_cases h : j = i
  · subst h
    simp [get, drop]
  · have h' : ¬ (i == j) = true := by simpa using fun h' => h h'.symm
    simp [get, drop, Std.DHashMap.get?_erase, h, h']

theorem good_empty (k : Kernel sys) : ({} : Plan sys).Good k :=
  fun _ => .inl (by simp [get])

end Plan

/-- Everyone but `i` has the state it had, and is up or down as it was. -/
def Frame (i : σ.Id) (k k' : Kernel sys) : Prop :=
  ∀ j, j ≠ i → (k'.cell j).state = (k.cell j).state ∧ (k'.cell j).up = (k.cell j).up

theorem Frame.trans {i : σ.Id} {a b c : Kernel sys} (h : Frame i a b) (h' : Frame i b c) :
    Frame i a c := fun j hj =>
  ⟨(h' j hj).1.trans (h j hj).1, (h' j hj).2.trans (h j hj).2⟩

/-- A plan stays good where only `i` moved, if what it now holds for `i` fits `i`. -/
theorem Plan.Good.frame {p p' : Plan sys} {k k' : Kernel sys} {i : σ.Id} (hp : p.Good k)
    (hf : Frame i k k') {a : Ahead sys i} (hget : p'.get = update p.get i a)
    (ha : a = [] ∨ ((k'.cell i).up = true ∧ Fits sys i (k'.cell i).state a)) : p'.Good k' := by
  intro j
  rw [hget]
  by_cases hj : j = i
  · subst hj
    simpa using ha
  · rw [update_of_ne _ _ hj, (hf j hj).1, (hf j hj).2]
    exact hp j

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

/-! What the kernel does with a plan: `run1`, `step` and `runBatch`, with steps from the plan. -/

/-- Handle `msg` for `i` as `handle` does, with the plan's step if it is the plan's next
message. -/
def handleAhead (k : Kernel sys) (p : Plan sys) (i : σ.Id) (msg : σ.Msg i) :
    Kernel sys × Plan sys × List σ.Out :=
  match p.get i with
  | (m, r) :: rest =>
    if m = msg then
      match k.settle i r with
      | (k, outs) =>
        let k := k.rest i
        (k, if (k.cell i).up then p.set i rest else p.drop i, outs)
    else
      match k.handle i msg with
      | (k, outs) => (k, p.drop i, outs)
  | [] =>
    match k.handle i msg with
    | (k, outs) => (k, p, outs)

def run1Ahead (k : Kernel sys) (p : Plan sys) : Step sys × Plan sys :=
  match k.queue.pop? with
  | none => ({ kernel := k }, p)
  | some (e, rest) =>
    if (k.cell e.dst).up then
      match ({ k with queue := rest }).handleAhead p e.dst e.msg with
      | (k, p, outs) =>
        ({ kernel := k, events := .deliver e :: outs.map .output, outputs := outs }, p)
    else
      match k.startActor e.dst with
      | (k, outs) =>
        ({ kernel := k, events := .start e.dst :: outs.map .output, outputs := outs }, p.drop e.dst)

def stepAhead (k : Kernel sys) (p : Plan sys) : Step sys × Plan sys :=
  match k.timerNext with
  | some (due, ⟨i, msg⟩) => (({ k with timerTurn := false }).fire i msg due, p.drop i)
  | none => ({ k with timerTurn := true }).run1Ahead p

def runBatchAhead (k : Kernel sys) (p : Plan sys) : (fuel : Nat) → Step sys
  | 0 => { kernel := k }
  | fuel + 1 =>
    if k.wait = .none then
      match k.stepAhead p with
      | ({ kernel, events, outputs }, p) =>
        match kernel.runBatchAhead p fuel with
        | { kernel, events := later, outputs := more } =>
          { kernel, events := events ++ later, outputs := outputs ++ more }
    else { kernel := k }

theorem handleAhead_eq {k : Kernel sys} {p : Plan sys} (hp : p.Good k) (i : σ.Id) (msg : σ.Msg i) :
    ((k.handleAhead p i msg).1, (k.handleAhead p i msg).2.2) = k.handle i msg
      ∧ (k.handleAhead p i msg).2.1.Good (k.handle i msg).1 := by
  unfold handleAhead
  split
  · next m r rest heq =>
    have hfit : r = (sys.actor i).step (k.cell i).state m ∧ Fits sys i r.1 rest := by
      rcases hp i with h | ⟨-, h⟩
      · rw [heq] at h; cases h
      · rw [heq] at h; exact h
    split
    · next hm =>
      subst hm
      have hh : k.handle i m = ((k.settle i r).1.rest i, (k.settle i r).2) := by
        rw [handle_eq, ← hfit.1]
      have hf := frame_handle k i m
      have hst := settle_cell_state k i r
      have hfs := frame_settle k i r
      rw [hh] at hf ⊢
      generalize k.settle i r = s at hf hst hfs ⊢
      obtain ⟨k1, outs⟩ := s
      simp only at hf hst hfs ⊢
      refine ⟨by first | rfl | trivial, ?_⟩
      split
      · next hup =>
        refine hp.frame hf (Plan.get_set p i rest) (.inr ⟨hup, ?_⟩)
        rw [rest_up_state _ i hup, hst]
        exact hfit.2
      · exact hp.frame hf (Plan.get_drop p i) (.inl rfl)
    · exact ⟨rfl, hp.frame (frame_handle k i msg) (Plan.get_drop p i) (.inl rfl)⟩
  · next heq =>
    refine ⟨rfl, hp.frame (frame_handle k i msg) ?_ (.inl rfl)⟩
    rw [← heq, update_eq_self]

theorem run1Ahead_eq {k : Kernel sys} {p : Plan sys} (hp : p.Good k) :
    (k.run1Ahead p).1 = k.run1 ∧ (k.run1Ahead p).2.Good k.run1.kernel := by
  rw [run1_eq]
  unfold run1Ahead
  cases hq : k.queue.pop? with
  | none => exact ⟨rfl, hp⟩
  | some v =>
    obtain ⟨e, rest⟩ := v
    by_cases hup : (k.cell e.dst).up = true
    · simp only [hup, ite_true]
      have hp' : p.Good { k with queue := rest } := hp
      obtain ⟨heq, hgood⟩ := handleAhead_eq hp' e.dst e.msg
      rw [← heq] at hgood ⊢
      generalize ({ k with queue := rest }).handleAhead p e.dst e.msg = a at hgood ⊢
      obtain ⟨k', p', outs⟩ := a
      exact ⟨rfl, hgood⟩
    · simp only [hup, Bool.false_eq_true, ite_false]
      exact ⟨by first | rfl | trivial, hp.frame (frame_startActor k e.dst) (Plan.get_drop p e.dst)
        (.inl rfl)⟩

theorem stepAhead_eq {k : Kernel sys} {p : Plan sys} (hp : p.Good k) :
    (k.stepAhead p).1 = k.step ∧ (k.stepAhead p).2.Good k.step.kernel := by
  unfold stepAhead step
  cases ht : k.timerNext with
  | some v =>
    obtain ⟨due, i, msg⟩ := v
    exact ⟨rfl, hp.frame (frame_fire { k with timerTurn := false } i msg due) (Plan.get_drop p i)
      (.inl rfl)⟩
  | none => exact run1Ahead_eq (k := { k with timerTurn := true }) hp

/-- With a good plan, a batch is `runBatch`'s, value for value. -/
theorem runBatchAhead_eq {k : Kernel sys} {p : Plan sys} (hp : p.Good k) (fuel : Nat) :
    k.runBatchAhead p fuel = k.runBatch fuel := by
  induction fuel generalizing k p with
  | zero => rfl
  | succ fuel ih =>
    rw [runBatch_succ]
    unfold runBatchAhead
    split
    · obtain ⟨h1, h2⟩ := stepAhead_eq hp
      have hrest := ih h2
      rw [← h1] at hrest ⊢
      generalize k.stepAhead p = s at hrest ⊢
      obtain ⟨⟨kernel, events, outputs⟩, p'⟩ := s
      simp only at hrest ⊢
      rw [hrest]
    · rfl

/-! Working out a wave's steps. -/

/-- An actor that is up, its state, and its messages in the wave in order. -/
abbrev Job (k : Kernel sys) :=
  { x : (i : σ.Id) × sys.State i × List (σ.Msg i) //
    (k.cell x.1).up = true ∧ x.2.1 = (k.cell x.1).state }

/-- An actor's steps worked out, with why they fit it. -/
abbrev Done (k : Kernel sys) :=
  { y : (i : σ.Id) × Ahead sys i // (k.cell y.1).up = true ∧ Fits sys y.1 (k.cell y.1).state y.2 }

def Job.run {k : Kernel sys} (x : Job k) : Done k :=
  ⟨⟨x.1.1, ahead sys x.1.1 x.1.2.1 x.1.2.2⟩, x.2.1, by rw [← x.2.2]; exact fits_ahead ..⟩

/-- The messages of `wave` by receiver, each receiver's in the order they are queued. -/
def mail (wave : List (Envelope σ)) : Std.DHashMap σ.Id (fun i => List (σ.Msg i)) :=
  wave.reverse.foldl (fun m e => m.insert e.dst (e.msg :: (m.get? e.dst).getD [])) ∅

/-- The actors of `wave` that are up, with their state and their messages. The state is taken
out here so that a task working on it holds the state and not the kernel: an object another
thread may see is never updated in place again. -/
def jobs (k : Kernel sys) (wave : List (Envelope σ)) : List (Job k) :=
  (mail wave).toList.filterMap fun ⟨i, ms⟩ =>
    let c := k.cell i
    if h : c.up = true then some ⟨⟨i, c.state, ms⟩, h, rfl⟩ else none

/-- `xs` in pieces of `size`, in order. -/
def chunks {α : Type} (size : Nat) : List α → List (List α)
  | [] => []
  | x :: xs => (x :: xs).take (max 1 size) :: chunks size ((x :: xs).drop (max 1 size))
termination_by xs => xs.length
decreasing_by simp only [List.length_drop, List.length_cons]; omega

def Plan.add {k : Kernel sys} (p : Plan sys) (done : List (Done k)) : Plan sys :=
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
      let p := Plan.add {} (first.map Job.run)
      tasks.foldl (fun p t => p.add t.get) p

theorem Plan.Good.add {k : Kernel sys} {p : Plan sys} (hp : p.Good k) (done : List (Done k)) :
    (p.add done).Good k := by
  induction done generalizing p with
  | nil => exact hp
  | cons d done ih =>
    refine ih (p := p.set d.1.1 d.1.2) ?_
    intro i
    rw [Plan.get_set]
    by_cases h : i = d.1.1
    · subst h
      simpa using Or.inr d.2
    · rw [update_of_ne _ _ h]
      exact hp i

theorem good_plan (k : Kernel sys) (spread : Spread) (wave : List (Envelope σ)) :
    (k.plan spread wave).Good k := by
  unfold plan
  dsimp only
  split
  · exact Plan.good_empty k
  · split
    · exact Plan.good_empty k
    · rename_i first others hc
      clear hc
      have h0 := (Plan.good_empty (sys := sys) k).add (first.map Job.run)
      generalize Plan.add {} (first.map Job.run) = p at h0
      induction others generalizing p with
      | nil => exact h0
      | cons t others ih => exact ih _ (h0.add _)

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
before the kernel takes them in order. -/
def waves (k : Kernel sys) (spread : Spread) (fuel : Nat) : Step sys :=
  if _h : fuel = 0 then { kernel := k }
  else if k.wait = .none then
    let n := min fuel (max 1 k.queue.length)
    match k.runBatchAhead (k.plan spread (k.queue.toList.take n)) n with
    | { kernel, events, outputs } =>
      match waves kernel spread (fuel - n) with
      | { kernel, events := later, outputs := more } =>
        { kernel, events := events ++ later, outputs := outputs ++ more }
  else { kernel := k }
termination_by fuel
decreasing_by omega

/-- `runBatch`, its actors' steps worked out in parallel when there are `workers` threads to do
it; on one, `runBatch` itself. -/
def runWaves (k : Kernel sys) (spread : Spread) (fuel : Nat) : Step sys :=
  if spread.workers ≤ 1 then k.runBatch fuel else k.waves spread fuel

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
        rw [runBatchAhead_eq (good_plan _ _ _), ih _ (by omega)]
        conv => rhs; rw [show fuel = min fuel (max 1 k.queue.length)
          + (fuel - min fuel (max 1 k.queue.length)) by omega]
        rw [runBatch_add]
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
