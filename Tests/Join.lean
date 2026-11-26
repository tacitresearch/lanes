/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
Two systems written apart and joined: a front that takes questions and a back that doubles
numbers. The front's queries are wired to the back and the back's results to the front, so from
outside the join takes questions and gives answers, and no query is ever seen leaving.
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
  explored alone && joinedStates.queue.all fun v => alone.seen.contains ⟨v.path.last.state.left⟩

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

def tests : List (String × Bool) :=
  [ ("join: two systems wired together answer through each other, in every interleaving",
      check.ok && check.complete),
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
      frontCheck.ok && frontCheck.complete),
    ("join: every state of the join, seen from the back, is a state of the back alone",
      explored backStates
      && joinedStates.queue.all fun v => backStates.seen.contains ⟨v.path.last.state.right⟩),
    ("join: the side that boots second sees an input older than its own first message",
      (SysState.init heralded {}).right.net == [⟨none, (), false⟩, ⟨some (), (), true⟩]
      && explored keeperStates
      && !keeperStates.seen.contains ⟨(SysState.init heralded {}).right⟩),
    ("join: the side that boots second reaches that state alone, up to message order",
      keeperStates.queue.any fun v =>
        v.path.last.state.equiv keeperEnv (SysState.init heralded {}).right) ]

end Tests.Join
