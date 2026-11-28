/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Lanes.Proofs

/-!
Two systems written apart and joined: a front that takes questions and a back that doubles
numbers. The front's queries are wired to the back and the back's results to the front, so from
outside the join takes questions and gives answers, and no query is ever seen leaving.

Then projection (`Lanes/Proof/JoinSound.lean`), checked before it was proved: every state the
join reaches, seen from either side, is among the states that side reaches alone, compared
exactly. A second pair, `herald` and `keeper`, shows why the side that boots second is seen
only up to the order of messages on different links. And one run of the join beside the run of
the front alone that `SysState.run_left` promises.
-/

namespace Tests.Join

open Lanes

inductive FrontIn where
  | ask (n : Nat)
  | reply (n : Nat)
  deriving DecidableEq, Repr, Hashable

inductive FrontOut where
  | query (n : Nat)
  | result (n : Nat)
  deriving DecidableEq, Repr, Hashable

abbrev frontSig : Signature where
  Id := Unit
  Msg _ := FrontIn
  In := FrontIn
  Out := FrontOut

/-- The state counts the answers given. -/
abbrev front : System frontSig where
  State _ := Nat
  actor _ :=
    { init := 0
      step := fun s msg =>
        match msg with
        | .ask n => (s, [.emit (.query n)])
        | .reply n => (s + 1, [.emit (.result n)])
      recover := fun s => (s, []) }
  accept x := ⟨(), x⟩

abbrev backSig : Signature where
  Id := Unit
  Msg _ := Nat
  In := Nat
  Out := Nat

abbrev back : System backSig where
  State _ := Unit
  actor _ := { init := (), step := fun _ n => ((), [.emit (2 * n)]), recover := fun s => (s, []) }
  accept x := ⟨(), x⟩

def wiring : Wiring frontSig backSig where
  toRight
    | .query n => some n
    | .result _ => none
  toLeft n := some (.reply n)

abbrev joined := front.join back wiring

/-- From outside: a number in, a number out. -/
abbrev service := joined.mapIO (In := Nat) (Out := Nat) (fun n => .inl (.ask n)) fun
  | .inl (.result n) => n
  | _ => 0

instance : frontSig.Inspect := {}
instance : front.Inspect := {}
instance : backSig.Inspect := {}
instance : back.Inspect := {}
instance : (joinSig frontSig backSig).Inspect := .join
instance : joined.Inspect := .join
instance : ((joinSig frontSig backSig).withIO Nat Nat).Inspect := .withIO
instance : service.Inspect := .mapIO

def check :=
  Check.system service { driver := Driver.anyOrder [3, 5] }
    [ .always "only doubled questions come out" fun w => w.state.outbox.all (· ∈ [6, 10]),
      .always "the front has answered no more than was asked" fun w =>
        w.state.state (.inl ()) ≤ 2,
      .sometimes "both answers are waiting to leave" fun w =>
        w.state.outbox.length == 2 ]
    { checkDeadlock := true
      terminal := fun w => w.driver.isEmpty && w.state.state (.inl ()) == 2 }

/-- A state compared as it is, message order included. The checker's own comparison merges
states that differ in the order of messages on different links, which projection must not. -/
structure Exact {σ : Signature} (sys : System σ) where
  state : SysState sys

instance {σ : Signature} {sys : System σ} [σ.Inspect] [sys.Inspect] : BEq (Exact sys) where
  beq x y :=
    (Enum.all (α := σ.Id)).all (fun i => x.state.state i == y.state.state i
      && x.state.up i == y.state.up i && x.state.timers i == y.state.timers i)
    && x.state.net == y.state.net && x.state.outbox == y.state.outbox

instance {σ : Signature} {sys : System σ} [σ.Inspect] [sys.Inspect] : Hashable (Exact sys) where
  hash x := x.state.hash

/-- Every state `sys` reaches within the bound, with any of `inputs` arriving at any time. -/
def explore {σ : Signature} (sys : System σ) [σ.Inspect] [sys.Inspect] (env : EnvModel σ)
    (inputs : List σ.In) (within : SysState sys → Bool) : Check.Search (Exact sys) (Event σ) :=
  let model : Check.Model (Exact sys) (Event σ) :=
    { init := [⟨SysState.init sys env⟩]
      next := fun x =>
        (x.state.successors env ++ inputs.filterMap fun input =>
          (x.state.step env (.input input)).map (Event.input input, ·)).map fun (ev, c) =>
            (ev, ⟨c.compact⟩) }
  let opts : Check.Options (Exact sys) := { constraint := fun x => within x.state }
  (Check.Search.start model [] opts []).run model [] opts (fun _ => "") opts.maxStates

def explored {σ : Signature} {sys : System σ} [σ.Inspect] [sys.Inspect]
    (search : Check.Search (Exact sys) (Event σ)) : Bool :=
  search.complete && search.head ≥ search.queue.size

/-- Asks from outside travel on a reliable link, everything else on a network link, and every
actor may crash: a crash of the front loses the asks and keeps the replies. -/
def faulty : EnvModel (joinSig frontSig backSig) where
  link src _ := if src.isSome then Link.network else Link.reliable
  mayCrash _ := true

def joinedStates :=
  explore joined faulty [.inl (.ask 3), .inl (.reply 6)] fun c =>
    c.state (.inl ()) ≤ 2 && c.net.length ≤ 3 && c.outbox.length ≤ 2

/-- The front alone. Its bounds leave room for one input and one output more than the join's:
a step of the join can be an input and a delivery, or a delivery and an output. -/
def frontStates (inputs : List FrontIn) :=
  explore front faulty.left inputs fun c =>
    c.state () ≤ 2 && c.net.length ≤ 4 && c.outbox.length ≤ 3

def seenFromFront (inputs : List FrontIn) : Bool :=
  let alone := frontStates inputs
  explored alone && joinedStates.queue.all fun v => alone.contains ⟨v.path.last.state.left⟩

def backStates :=
  explore back faulty.right [3] fun c => c.net.length ≤ 4 && c.outbox.length ≤ 1

/-- No result waits to leave before the front has answered. -/
def resultAnswered (c : SysState front) : Prop :=
  ∀ n, .result n ∈ c.outbox → 0 < c.state ()

def frontCheck :=
  Check.system front
    { env := faulty.left, driver := Driver.anyOrder [.ask 3, .reply 6, .reply 6], maxCrashes := 1 }
    [ .always "no result waits to leave before the front has answered" fun w =>
        w.state.outbox.all fun out => !(out matches .result _) || 0 < w.state.state (),
      .sometimes "a result waits to leave" fun w => w.state.outbox.any (· matches .result _) ]
    { constraint := fun w => w.state.state () ≤ 3 && w.state.outbox.length ≤ 3 }

theorem front_resultAnswered (env : EnvModel frontSig) : front.Invariant env resultAnswered := by
  refine (System.Inductive.of_monotone env ?_ ?_ ?_ ?_ ?_).invariant
  · intro n h
    simp [SysState.blank] at h
  · intro c c' hc hbelow n h
    rw [hbelow.state]
    exact hc n (hbelow.outbox _ h)
  · exact fun c x hc => hc
  · intro c i msg hc _ n h
    cases msg with
    | ask m => exact hc n (by simpa [SysState.grow, Effect.emits] using h)
    | reply m => simp [SysState.grow]
  · intro c i hc n h
    simpa [SysState.grow] using hc n (by simpa [SysState.grow, Effect.emits] using h)

/-- The same holds of the front inside the join, whatever the back does. -/
theorem joined_resultAnswered (env : EnvModel (joinSig frontSig backSig)) :
    joined.Invariant env fun c => resultAnswered c.left :=
  (front_resultAnswered env.left).join_left

/-- A boot actor whose start is an output. -/
abbrev heraldSig : Signature where
  Id := Unit
  Msg _ := Unit
  Out := Unit

abbrev herald : System heraldSig where
  State _ := Unit
  actor _ := { init := (), step := fun s _ => (s, []), recover := fun s => (s, [.emit ()]) }
  accept := nofun
  boot := [()]

/-- A boot actor that starts by sending itself a note (`true`). Inputs arrive as `false`. -/
abbrev keeperSig : Signature where
  Id := Unit
  Msg _ := Bool
  In := Unit

abbrev keeper : System keeperSig where
  State _ := Unit
  actor _ := { init := (), step := fun s _ => (s, []), recover := fun s => (s, [.send () true]) }
  accept _ := ⟨(), false⟩
  boot := [()]

abbrev heralded := herald.join keeper { toRight := fun _ => some () }

instance : heraldSig.Inspect := {}
instance : herald.Inspect := {}
instance : keeperSig.Inspect := {}
instance : keeper.Inspect := {}

def keeperEnv : EnvModel keeperSig :=
  EnvModel.right ({} : EnvModel (joinSig heraldSig keeperSig))

def keeperStates :=
  explore keeper keeperEnv [()] fun c => c.net.length ≤ 4

private theorem mem_tail_of_erase {α : Type} [DecidableEq α] {l : List α} {a x : α}
    (h : x ∈ (l.erase a).tail) : x ∈ l.tail := by
  cases l with
  | nil => simp at h
  | cons y ys =>
    by_cases hy : y = a
    · subst hy
      rw [List.erase_cons_head] at h
      exact List.mem_of_mem_tail h
    · rw [List.erase_cons_tail (by simpa using hy)] at h
      exact List.mem_of_mem_erase h

/-- Alone, the keeper stays up and never has an input ahead of the note it sent itself. -/
theorem keeper_note_first {c : SysState keeper} (h : keeper.Reachable keeperEnv c) :
    c.up () = true ∧ ∀ e ∈ c.net.tail, e.src = none := by
  induction h with
  | init => exact ⟨rfl, fun e he => absurd he (by
      rw [show (SysState.init keeper keeperEnv).net = [⟨some (), (), true⟩] from rfl]
      simp)⟩
  | @step c c' ev _ hstep ih =>
    cases ev with
    | input x =>
      obtain rfl := SysState.step_input.mp hstep
      refine ⟨ih.1, fun e he => ?_⟩
      cases hnet : c.net with
      | nil => simp [hnet] at he
      | cons y ys =>
        simp only [hnet, List.cons_append, List.tail_cons, List.mem_append,
          List.mem_singleton] at he
        rcases he with he | rfl
        · exact ih.2 e (by simp [hnet, he])
        · rfl
    | deliver e =>
      obtain ⟨_, _, rfl⟩ := SysState.step_deliver.mp hstep
      exact ⟨ih.1, fun x hx => ih.2 x (mem_tail_of_erase hx)⟩
    | duplicate e =>
      obtain ⟨_, _, _, rfl⟩ := SysState.step_duplicate.mp hstep
      exact ih
    | drop e =>
      obtain ⟨_, _, rfl⟩ := SysState.step_drop.mp hstep
      exact ⟨ih.1, fun x hx => ih.2 x (mem_tail_of_erase hx)⟩
    | timeout i msg =>
      obtain ⟨_, _, rfl⟩ := SysState.step_timeout.mp hstep
      exact ih
    | output out => exact nomatch out
    | crash i =>
      obtain ⟨_, hcrash, _⟩ := SysState.step_crash.mp hstep
      exact absurd hcrash (by simp [keeperEnv, EnvModel.right])
    | start i =>
      obtain ⟨hdown, _, _⟩ := SysState.step_start.mp hstep
      rw [ih.1] at hdown
      cases hdown
    | restart =>
      obtain ⟨hmay, _⟩ := SysState.step_restart.mp hstep
      exact absurd hmay (by simp [keeperEnv, EnvModel.right])

/-- So the join's first state, seen from the keeper, is no state of the keeper alone: there
the herald's input is ahead of the note. -/
theorem heralded_right_not_alone :
    ¬keeper.Reachable keeperEnv (SysState.init heralded {}).right := fun h => by
  have hnote := (keeper_note_first h).2 ⟨some (), (), true⟩ (by
    rw [show (SysState.init heralded {}).right.net
      = [⟨none, (), false⟩, ⟨some (), (), true⟩] from rfl]
    simp)
  simp at hnote

/-- A question asked and answered through the join. -/
def joinedRun : List (Event (joinSig frontSig backSig)) :=
  [.input (.inl (.ask 4)), .start (.inl ()), .deliver ⟨none, .inl (), .ask 4⟩, .start (.inr ()),
    .deliver ⟨some (.inl ()), .inr (), (4 : Nat)⟩, .deliver ⟨some (.inr ()), .inl (), .reply 8⟩,
    .output (.inl (.result 8))]

/-- The same seen from the front, alone: the query is handed over and the reply is an input. -/
def frontRun : List (Event frontSig) :=
  [.input (.ask 4), .start (), .deliver ⟨none, (), .ask 4⟩, .output (.query 4),
    .input (.reply 8), .deliver ⟨none, (), .reply 8⟩, .output (.result 8)]

def told : Deed frontSig → FrontIn ⊕ FrontOut
  | .handle _ msg => .inl msg
  | .output out => .inr out

def runsAgree : Bool :=
  let env : EnvModel (joinSig frontSig backSig) := {}
  match (SysState.init joined env).run env joinedRun,
      (SysState.init front env.left).run env.left frontRun with
  | some c, some c' =>
    (⟨c.left⟩ : Exact front) == ⟨c'⟩
      && (frontRun.filterMap wiring.shown).map told == (joinedRun.filterMap Event.leftDeed).map told
      && (joinedRun.filterMap Event.leftDeed).map told
        == [.inl (.ask 4), .inl (.reply 8), .inr (.result 8)]
  | _, _ => false

def tests : List (String × Bool) :=
  [ ("join: two systems wired together answer through each other, in every interleaving",
      check.ok),
    ("join: a wired output is a message to the other system, not an output of the join",
      match (SysState.init joined {}).run {}
          [.input (.inl (.ask 4)), .start (.inl ()), .deliver ⟨none, .inl (), .ask 4⟩] with
      | some c => c.outbox.isEmpty && c.net == [⟨some (.inl ()), .inr (), (4 : Nat)⟩]
      | none => false),
    ("join: every state of the join, seen from the front, is a state of the front alone",
      explored joinedStates && seenFromFront [.ask 3, .reply 6]),
    ("join: the front is seen crashed with a reply in flight, and with two answers given",
      joinedStates.queue.any (fun v =>
        let c := v.path.last.state.left
        !c.up () && c.net.contains ⟨none, (), .reply 6⟩)
      && joinedStates.queue.any fun v => v.path.last.state.left.state () == 2),
    ("join: seen from the front, what the back sends is an input",
      !seenFromFront [.ask 3]),
    ("join: the front alone gives no result before it has answered",
      frontCheck.ok),
    ("join: every state of the join, seen from the back, is a state of the back alone",
      explored backStates
      && joinedStates.queue.all fun v => backStates.contains ⟨v.path.last.state.right⟩),
    ("join: the side that boots second sees an input older than its own first message",
      (SysState.init heralded {}).right.net == [⟨none, (), false⟩, ⟨some (), (), true⟩]
      && explored keeperStates
      && !keeperStates.contains ⟨(SysState.init heralded {}).right⟩),
    ("join: the side that boots second reaches that state alone, up to message order",
      keeperStates.queue.any fun v =>
        v.path.last.state.equiv keeperEnv (SysState.init heralded {}).right),
    ("join: a run of the join and a run of the front alone reach the same state and show the "
        ++ "same deeds, the wired query not among them",
      runsAgree) ]

end Tests.Join
