/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Examples.Bank
import Tests.Bank

/-!
A system split across two shards behaves as the one system (`Lanes/Actors/ShardSound.lean`),
checked before it was proved: every state the split reaches, read as one state, is among the
states the system reaches alone, compared as the checker compares states. The bank has its two
accounts on different shards; `relay` adds boot actors, timers and `stop`. `fragile` shows what
the theorem has to assume about booting.
-/

namespace Tests.Split

open Lanes

/-- A state compared as the checker compares states. -/
structure UpTo {σ : Signature} (sys : System σ) (env : EnvModel σ) where
  state : SysState sys

instance {σ : Signature} {sys : System σ} {env : EnvModel σ} [σ.Inspect] [sys.Inspect] :
    BEq (UpTo sys env) where
  beq x y := x.state.equiv env y.state

instance {σ : Signature} {sys : System σ} {env : EnvModel σ} [σ.Inspect] [sys.Inspect] :
    Hashable (UpTo sys env) where
  hash x := x.state.hash

/-- Every state `sys` reaches within the bound, with any of `inputs` arriving at any time. -/
def explore {σ : Signature} (sys : System σ) [σ.Inspect] [sys.Inspect] (env : EnvModel σ)
    (inputs : List σ.In) (within : SysState sys → Bool) :
    Check.Search (UpTo sys env) (Event σ) :=
  let model : Check.Model (UpTo sys env) (Event σ) :=
    { init := [⟨SysState.init sys env⟩]
      next := fun x =>
        (x.state.successors env ++ inputs.filterMap fun input =>
          (x.state.step env (.input input)).map (Event.input input, ·)).map fun (ev, c) =>
            (ev, ⟨c.compact⟩) }
  let opts : Check.Options (UpTo sys env) := { constraint := fun x => within x.state }
  (Check.Search.start model [] opts []).run model [] opts (fun _ => "") opts.maxStates

def explored {σ : Signature} {sys : System σ} {env : EnvModel σ} [σ.Inspect] [sys.Inspect]
    (search : Check.Search (UpTo sys env) (Event σ)) : Bool :=
  search.complete && search.head ≥ search.queue.size

structure Compared (σ : Signature) (sys : System σ) (hosts : σ.Id → Bool) (env : EnvModel σ)
    [σ.Inspect] [sys.Inspect] [(splitSig σ).Inspect] [(sys.split hosts).Inspect] where
  alone : Check.Search (UpTo sys env) (Event σ)
  split : Check.Search (UpTo (sys.split hosts) (env.split hosts)) (Event (splitSig σ))

section Compare

variable {σ : Signature} {sys : System σ} {hosts : σ.Id → Bool} {env : EnvModel σ}
  [σ.Inspect] [sys.Inspect] [(splitSig σ).Inspect] [(sys.split hosts).Inspect]

/-- `sys` alone and split by `hosts`, each explored within the same bound on the one state,
with the inputs of the split given to the shard that hosts their receiver. -/
def compare (sys : System σ) [sys.Inspect] (hosts : σ.Id → Bool) [(sys.split hosts).Inspect]
    (env : EnvModel σ) (inputs : List σ.In) (within : SysState sys → Bool) :
    Compared σ sys hosts env where
  alone := explore sys env inputs within
  split := explore (sys.split hosts) (env.split hosts) (inputs.map (Split.route sys hosts))
    fun c => within c.merged

namespace Compared

def complete (r : Compared σ sys hosts env) : Bool :=
  explored r.alone && explored r.split

/-- Every state of the split, merged, is a state of the system alone. -/
def sound (r : Compared σ sys hosts env) : Bool :=
  r.split.queue.all fun v => r.alone.seen.contains ⟨v.path.last.state.merged⟩

/-- The split loses no behaviour: every state of the system alone is a state of the split,
merged. -/
def full (r : Compared σ sys hosts env) : Bool :=
  let merged : Std.HashSet (UpTo sys env) :=
    r.split.queue.foldl (fun seen v => seen.insert ⟨v.path.last.state.merged⟩) {}
  r.alone.queue.all fun v => merged.contains v.path.last

def somewhere (r : Compared σ sys hosts env) (p : SysState (sys.split hosts) → Bool) : Bool :=
  r.split.queue.any fun v => p v.path.last.state

end Compared

end Compare

section Bank

open Examples.Bank Tests.Bank

/-- Credits travel on a network link, requests on a reliable one, and every account may crash:
a crash loses the requests waiting and keeps the credits. -/
def faulty : EnvModel (sig (Fin 2)) where
  link src _ := if src.isSome then Link.network else Link.reliable
  mayCrash _ := true

def bankHosts : Fin 2 → Bool := (· == 0)

instance : (splitSig (sig (Fin 2))).Inspect := .split
instance : (Bank2.split bankHosts).Inspect := .split

def bankCompared (env : EnvModel (sig (Fin 2))) (inputs : List (Request (Fin 2))) :=
  compare Bank2 bankHosts env inputs fun c =>
    c.net.length ≤ 2 && c.outbox.length ≤ 1
      && (Enum.all (α := Fin 2)).all fun a => (c.state a).balance ≤ 3

def bankReliable := bankCompared {} [.transfer ⟨1, 0, 1, 1⟩, .transfer ⟨2, 1, 0, 2⟩]

def bankFaulty := bankCompared faulty [.transfer ⟨1, 0, 1, 1⟩]

end Bank

inductive RelayMsg where
  | ping
  | tick
  | halt
  deriving DecidableEq, Repr, Hashable

/-- Two boot actors that greet each other when they start, again on a timer, and stop when told
to from outside. The state counts greetings received, up to two. -/
abbrev relaySig : Signature where
  Id := Fin 2
  Msg _ := RelayMsg
  In := Fin 2
  Out := Fin 2

abbrev relay : System relaySig where
  State _ := Nat
  actor i :=
    { init := 0
      step := fun s msg =>
        match msg with
        | .ping => (min (s + 1) 2, [.emit i])
        | .tick => (s, [.send (i + 1) .ping])
        | .halt => (s, [.cancel .tick, .stop])
      recover := fun s => (s, [.send (i + 1) .ping, .after 10 .tick]) }
  accept i := ⟨i, .halt⟩
  boot := [0, 1]

instance : relaySig.Inspect := {}
instance : relay.Inspect := {}

/-- The left shard hosts actor 1, so the split boots the two in the other order. -/
def relayHosts : Fin 2 → Bool := (· == 1)

instance : (splitSig relaySig).Inspect := .split
instance : (relay.split relayHosts).Inspect := .split

def relayEnv : EnvModel relaySig where
  link src dst := if src == some 0 then Link.network else if dst == 0 then Link.unordered else {}
  mayCrash i := i == 0
  restarts i := i == 1

def relayCompared :=
  compare relay relayHosts relayEnv [1] fun c => c.net.length ≤ 2 && c.outbox.length ≤ 1

/-- `true` stops the first time it starts. `false` boots before it and sends it a message,
which is lost with that stop. -/
abbrev fragileSig : Signature where
  Id := Bool
  Msg _ := Unit

/-- The state counts starts. -/
abbrev fragile : System fragileSig where
  State _ := Nat
  actor i :=
    { init := 0
      step := fun s _ => (s, [])
      recover := fun s => (s + 1, if i then (if s = 0 then [.stop] else []) else [.send true ()]) }
  accept := nofun
  boot := [false, true]

instance : fragileSig.Inspect := {}
instance : fragile.Inspect := {}

instance : (splitSig fragileSig).Inspect := .split
instance : (fragile.split id).Inspect := .split

def fragileCompared :=
  compare fragile id {} [] fun c => c.net.length ≤ 2 && c.state true ≤ 3

def tests : List (String × Bool) :=
  [ ("split: the bank on two shards reaches only states of the bank, reliable links",
      bankReliable.complete && bankReliable.sound && bankReliable.full),
    ("split: the bank on two shards reaches only states of the bank, with crashes and loss",
      bankFaulty.complete && bankFaulty.sound
        && bankFaulty.full),
    ("split: a credit crosses between the shards, and an account is down with one in flight",
      bankFaulty.somewhere (fun c =>
        c.net.contains ⟨some (.inl 0), .inr 1, .credit 1⟩)
      && bankFaulty.somewhere fun c =>
        c.state (.inr 1) == ⟨3⟩ && !c.up (.inr 1)
          && c.net.contains ⟨some (.inl 0), .inr 1, .credit 1⟩),
    ("split: boot actors, timers and stop on two shards reach only states of the one system",
      relayCompared.complete && relayCompared.sound && relayCompared.full),
    ("split: the relay is seen stopped, restarted, and with a timer armed on either shard",
      relayCompared.somewhere (fun c => !c.up (.inl 1) && c.timers (.inl 1) == [])
      && relayCompared.somewhere (fun c => c.state (.inr 0) == 2 && c.timers (.inr 0) == [.tick])
      && relayCompared.somewhere fun c => c.state (.inl 1) == 2),
    ("split: no copy that only forwards ever runs",
      relayCompared.split.queue.all fun v =>
        let c := v.path.last.state
        !c.up (.inl 0) && !c.up (.inr 1) && c.net.all fun e =>
          Split.atHome relayHosts e.dst && e.src.all (Split.atHome relayHosts)),
    ("split: a boot actor that stops as it starts loses a message alone and keeps it when split",
      (SysState.init fragile {}).net.isEmpty
      && (SysState.init (fragile.split id) (EnvModel.split {} id)).merged.net
        == [⟨some false, true, ()⟩]),
    ("split: so the split starts it a second time, which the system alone never does",
      (match (SysState.init (fragile.split id) (EnvModel.split {} id)).run (EnvModel.split {} id)
          [.start (.inl true)] with
        | some c => c.merged.state true == 2
        | none => false)
      && fragileCompared.complete && !fragileCompared.sound
      && fragileCompared.alone.queue.all fun v => v.path.last.state.state true == 1) ]

end Tests.Split
