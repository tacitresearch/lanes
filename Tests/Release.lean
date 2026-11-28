/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
Releasing actors at rest (`Kernel.rest`, `docs/decisions/D51-release-actors-at-rest.md`),
checked before it is proved (rule 5.1). A client churns through actors, one per identity, and a
kernel that releases them is driven side by side with one that keeps every actor it started,
through every sequence of operations up to a bound: both hand over the same outputs, report the
same events but for starts, and hold the same actors in the same states. Under a shell that does
anything, the releasing kernel is checked against the semantics instead. Then at scale, on the
kernel alone and on a live runtime: a hundred thousand identities are touched and the kernel stays
small.
-/

namespace Tests.Release

open Lanes Lanes.Check Std.Async

inductive Msg (I : Type) where
  | ping
  | set (v : Nat)
  | arm
  | ring
  | pass (to : I)
  deriving DecidableEq, Repr, Hashable

abbrev sig (I : Type) [DecidableEq I] : Signature where
  Id := I
  Msg _ := Msg I
  In := I × Msg I
  Out := I × Nat

/-- An actor that is at rest at zero, with no timer, when `release` says so. -/
def counter {I : Type} [DecidableEq I] (release : Bool) (self : I) : (sig I).Actor self Nat where
  init := 0
  step n
    | .ping => (n, [.emit (self, n)])
    | .set v => (v, [])
    | .arm => (n, [.after 1 .ring])
    | .ring => (0, [.emit (self, n)])
    | .pass to => (n, [.send to .ping])
  fresh n := release && n == 0
  fresh_recover _ h := by simp_all

abbrev churn (I : Type) [DecidableEq I] (release : Bool) : System (sig I) where
  State _ := Nat
  actor := counter release
  accept x := ⟨x.1, x.2⟩

abbrev S := sig (Fin 2)

def ids : List (Fin 2) := [0, 1]

/-- An event, with what tells events apart, unless it is a start. -/
def key : Event S → Option (Nat × Option (Fin 2) × Fin 2 × Msg (Fin 2))
  | .deliver e => some (0, e.src, e.dst, e.msg)
  | .timeout i msg => some (1, none, i, msg)
  | .input x => some (2, none, x.1, x.2)
  | .output out => some (3, none, out.1, .set out.2)
  | _ => none

structure Pair where
  kept : Kernel (churn (Fin 2) false)
  released : Kernel (churn (Fin 2) true)
  /-- What each handed over in the last operation. -/
  shown : List (Fin 2 × Nat) × List (Fin 2 × Nat) := ([], [])
  /-- The events each reported in the last operation, starts left out. -/
  awake : List (Nat × Option (Fin 2) × Fin 2 × Msg (Fin 2)) ×
    List (Nat × Option (Fin 2) × Fin 2 × Msg (Fin 2)) := ([], [])

abbrev Timer := Msg (Fin 2) × Nat × Nat

def cells {release : Bool} (k : Kernel (churn (Fin 2) release)) :
    List (Bool × Nat × Bool × List Timer) :=
  ids.map fun i => (k.cells.contains i, (k.cell i).state, (k.cell i).up,
    (k.cell i).timers.map fun (m, due) => ((m : Msg (Fin 2)), due.deadline_ms, due.token))

def agenda {release : Bool} (k : Kernel (churn (Fin 2) release)) :
    List (Nat × Nat × Fin 2 × Msg (Fin 2)) :=
  k.agenda.toList.map fun (due, ⟨i, msg⟩) => (due.deadline_ms, due.token, i, (msg : Msg (Fin 2)))

def queue {release : Bool} (k : Kernel (churn (Fin 2) release)) :
    List (Option (Fin 2) × Fin 2 × Msg (Fin 2)) :=
  k.queue.toList.map fun e => (e.src, e.dst, (e.msg : Msg (Fin 2)))

def view {release : Bool} (k : Kernel (churn (Fin 2) release)) :=
  (cells k, agenda k, queue k, k.nextToken, k.clock_ms, k.timerTurn)

instance : BEq Pair := ⟨fun a b =>
  view a.kept == view b.kept && view a.released == view b.released && a.shown == b.shown
    && a.awake == b.awake⟩
instance : Hashable Pair := ⟨fun p => hash (view p.kept, view p.released, p.shown, p.awake)⟩

/-- A client that sends anything to anyone, and work that drains the queue. The clock goes
forward only when nothing is queued, so a timer is never due while a message waits: when one is,
the two kernels may take them in different orders, both of which the semantics allows, since a
start takes a turn of its own. -/
def ops (p : Pair) : List (Kernel.Op S) :=
  let inputs := ids.flatMap fun i =>
    [Msg.ping, .set 0, .set 1, .arm, .pass (i + 1)].map fun msg => Kernel.Op.input (i, msg)
  inputs ++ [.batch 20] ++ if p.kept.queue.isEmpty then [.advance (p.kept.clock_ms + 1)] else []

def both (p : Pair) (op : Kernel.Op S) : Pair :=
  let (kept, released) := match op with
    | .input _ => (p.kept.apply op, p.released.apply op)
    | _ => (p.kept.exec [op, .batch 20], p.released.exec [op, .batch 20])
  { kept := kept.kernel, released := released.kernel, shown := (kept.outputs, released.outputs)
    awake := (kept.events.filterMap key, released.events.filterMap key) }

def side : Model Pair (Kernel.Op S) where
  init := [{ kept := (Kernel.boot (churn (Fin 2) false)).1
             released := (Kernel.boot (churn (Fin 2) true)).1 }]
  next p := (ops p).map fun op => (op, both p op)

def gone (p : Pair) (i : Fin 2) : Bool :=
  (p.kept.cell i).up && !p.released.cells.contains i

def properties : List (Property Pair) :=
  [ .always "the same outputs" fun p => p.shown.1 == p.shown.2,
    .always "the same events but for starts" fun p => p.awake.1 == p.awake.2,
    .always "the same states and timers" fun p =>
      ids.all fun i => (p.kept.cell i).state == (p.released.cell i).state
        && (p.kept.cell i).timers == (p.released.cell i).timers,
    .always "the same queue and agenda" fun p =>
      queue p.kept == queue p.released && agenda p.kept == agenda p.released,
    .always "a released actor is at rest in the kernel that keeps it" fun p =>
      ids.all fun i => p.released.cells.contains i
        || ((p.kept.cell i).state == 0 && (p.kept.cell i).timers.isEmpty),
    .always "the kernel that releases holds no more actors" fun p =>
      p.released.cells.size ≤ p.kept.cells.size,
    .sometimes "an actor is released" fun p => ids.any (gone p),
    .sometimes "every actor is released" fun p => ids.all (gone p),
    .sometimes "a released actor has mail queued" fun p =>
      ids.any fun i => gone p i && (queue p.released).any (·.2.1 == i),
    .sometimes "an actor at zero is kept for its timer" fun p =>
      ids.any fun i => (p.released.cell i).up && (p.released.cell i).state == 0
        && !(p.released.cell i).timers.isEmpty,
    .sometimes "an actor is kept for its state" fun p =>
      ids.any fun i => (p.released.cell i).up && (p.released.cell i).state != 0]

/-! Against the semantics, with a shell that does anything, in any order: the events the
releasing kernel reports, but for the starts that bring released actors back, are a run of the
semantics, and the kernel is that run's state with actors at rest released
(`Kernel.exec_sound`). -/

abbrev R := churn (Fin 2) true

def resume (c : SysState R) : Event S → Option (SysState R)
  | .start i => if c.up i then some c else c.step Kernel.env (.start i)
  | ev => c.step Kernel.env ev

def releasedFrom (c b : SysState R) : Bool :=
  (ids.all fun i =>
    (b.state i == c.state i && b.up i == c.up i && b.timers i == c.timers i)
      || ((R.actor i).fresh (c.state i) && c.up i && (c.timers i).isEmpty && !b.up i
        && b.state i == (R.actor i).init && (b.timers i).isEmpty))
  && b.net == c.net && b.outbox == c.outbox

structure Follow where
  run : Option (SysState R)
  kernel : Kernel R
  /-- Whether the last operation started an actor that the run has up. -/
  restarted : Bool := false

def semantic (c : SysState R) :
    List (Nat × Bool × List (Msg (Fin 2))) × List (Option (Fin 2) × Fin 2 × Msg (Fin 2))
      × List (Fin 2 × Nat) :=
  (ids.map fun i => (c.state i, c.up i, (c.timers i : List (Msg (Fin 2)))),
    c.net.map fun e => (e.src, e.dst, (e.msg : Msg (Fin 2))), c.outbox)

instance : BEq Follow := ⟨fun a b => view a.kernel == view b.kernel
  && a.run.map semantic == b.run.map semantic && a.restarted == b.restarted⟩
instance : Hashable Follow := ⟨fun f => hash (view f.kernel, f.run.map semantic, f.restarted)⟩

def hostile (k : Kernel R) : List (Kernel.Op S) :=
  let inputs := ids.flatMap fun i =>
    [Msg.ping, .set 0, .set 1, .arm, .pass (i + 1)].map fun msg => Kernel.Op.input (i, msg)
  let fires := (agenda k).map fun (deadline_ms, token, i, msg) =>
    Kernel.Op.fire (σ := S) i msg ⟨deadline_ms, token⟩
  inputs ++ [.advance (k.clock_ms + 1), .step, .batch 2] ++ fires

def follow : Model Follow (Kernel.Op S) where
  init := [{ run := some (SysState.init R Kernel.env), kernel := (Kernel.boot R).1 }]
  next f := (hostile f.kernel).map fun op =>
    let r := f.kernel.apply op
    (op, { run := f.run.bind fun c => r.events.foldlM resume c, kernel := r.kernel
           restarted := f.run.any fun c => r.events.any fun | .start i => c.up i | _ => false })

def following : List (Property Follow) :=
  [ .always "the events but for starts are a run of the semantics" (·.run.isSome),
    .always "the kernel is that run's state with actors at rest released" fun f =>
      f.run.all fun c => releasedFrom c f.kernel.abs,
    .sometimes "a released actor has mail queued" fun f =>
      f.run.any fun c => ids.any fun i =>
        c.up i && !f.kernel.cells.contains i && c.net.any (·.dst == i),
    .sometimes "a released actor is started again" (·.restarted) ]

/-! At scale: a hundred thousand identities, each touched once and left at rest. -/

def strangers : Nat := 100000

def touch {release : Bool} (k : Kernel (churn Nat release)) (n : Nat) :
    Kernel (churn Nat release) × List (Nat × Nat) :=
  match k.exec [.input (n, .ping), .batch 4] with
  | { kernel, outputs, .. } => (kernel, outputs)

def churned (release : Bool) (count : Nat) : Kernel (churn Nat release) × Nat :=
  (List.range count).foldl (init := ((Kernel.boot (churn Nat release)).1, 0)) fun (k, zeros) n =>
    let (k, outs) := touch k n
    (k, zeros + outs.countP (· == (n, 0)))

/-- How many actors a live runtime holds: those a peek at every actor finds started. -/
def held {release : Bool} (rt : Runtime (churn Nat release)) : Async Nat := do
  let reply : IO.Promise (Option Nat) ← IO.Promise.new
  discard <| rt.tryPeek [] (fun p => reply.resolve (p.map (·.others.length))) (every := fun _ => true)
  return ((← await reply.result?).join).getD 0

/-- A live runtime on which `touched` identities are touched once each: how many actors it holds
then, how many outputs said zero, and what was handed over afterwards, when an identity touched
before is touched again and one never touched is touched. The handler counts rather than keeps:
it runs on the workers' threads, and an array two threads can see is copied on every push. -/
def live (release : Bool) (touched : Nat) : Async (Nat × Nat × List (Nat × Nat)) := do
  let zeros ← IO.mkRef 0
  let after ← IO.mkRef false
  let shown ← IO.mkRef #[]
  let rt ← Runtime.start (churn Nat release) {}
    (fun out => do
      if ← after.get then shown.modify (·.push out)
      else if out.2 == 0 then zeros.modify (· + 1))
  for n in [0:touched] do rt.input (n, .ping)
  rt.idle
  let actors ← held rt
  after.set true
  rt.input (7, .set 5)
  rt.input (7, .ping)
  rt.input (7, .set 0)
  rt.input (7, .ping)
  rt.input (strangers + 1, .ping)
  rt.idle
  rt.stop
  return (actors, ← zeros.get, (← shown.get).toList)

def tests : List (String × Bool) :=
  let r := search side properties { maxDepth := some 4, constraint := fun p => p.kept.nextToken ≤ 2 }
  let f := search follow following { maxDepth := some 4, constraint := fun f => f.kernel.nextToken ≤ 2 }
  let (kept, keptZeros) := churned false 2000
  let (released, releasedZeros) := churned true strangers
  let again := (released.exec [.input (5, .set 3), .input (5, .ping), .input (5, .set 0),
    .input (5, .ping), .input (6, .ping), .batch 20]).outputs
  [ ("release: side by side with a kernel that keeps every actor, nothing tells them apart, to depth 4",
      r.passed && r.witnesses.length == 5),
    ("release: whatever the shell does, the releasing kernel is the semantics with actors released, to depth 4",
      f.passed && f.witnesses.length == 2),
    ("release: the kernel that keeps them grows with every identity touched",
      kept.cells.size == 2000 && keptZeros == 2000),
    ("release: a hundred thousand identities touched, and the kernel holds none of them",
      released.cells.size == 0 && releasedZeros == strangers),
    ("release: a released actor touched again is as new",
      again == [(5, 3), (5, 0), (6, 0)] && released.cells.size == 0) ]

def liveTests : Async (List (String × Bool)) := do
  let (actors, count, after) ← live true strangers
  let (keptActors, _, _) ← live false (strangers / 5)
  IO.eprintln s!"release: {strangers} identities touched; the runtime holds {actors} actors, {keptActors} of {strangers / 5} without release"
  return [("release: a live runtime touched by a hundred thousand identities stays small",
      count == strangers && actors ≤ 1 && keptActors ≥ strangers / 10),
    ("release: on a live runtime a released actor touched again is as new",
      after.filter (·.1 == 7) == [(7, 5), (7, 0)] && after.length == 3
        && after.contains (strangers + 1, 0))]

end Tests.Release

