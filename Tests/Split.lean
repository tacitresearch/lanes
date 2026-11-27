/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Examples.Bank
import Tests.Bank
import Tests.Join

/-!
A system split across two shards behaves as the one system (`Lanes/Runtime/ShardSound.lean`),
checked before it was proved: every state the split reaches, read as one state, is among the
states the system reaches alone, compared as the checker compares states. The bank has its two
accounts on different shards; `relay` adds boot actors, timers and `stop`.

The same comparisons run on three shards (`System.shards`, `Lanes/Runtime/ShardsSound.lean`).

Two systems show where the statement stops. `fragile` has a boot actor that stops as it starts:
the split boots one shard before the other, so a message is kept that the system alone loses.
`chorus` has two actors that say the same thing: the split can hand over the newer of two equal
outputs, so its state is a state of the system only up to the order of the outputs waiting.
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

/-- The system alone and on shards, explored within the same bound on the one state. -/
structure Compared {σ τ : Signature} (sys : System σ) (env : EnvModel σ) (shards : System τ)
    (shardsEnv : EnvModel τ) [σ.Inspect] [sys.Inspect] [τ.Inspect] [shards.Inspect] where
  alone : Check.Search (UpTo sys env) (Event σ)
  split : Check.Search (UpTo shards shardsEnv) (Event τ)
  merged : SysState shards → SysState sys

section Compare

variable {σ τ : Signature} {sys : System σ} {env : EnvModel σ} {shards : System τ}
  {shardsEnv : EnvModel τ} [σ.Inspect] [sys.Inspect] [τ.Inspect] [shards.Inspect]

/-- `sys` alone and split by `hosts`, each explored within the same bound on the one state,
with the inputs of the split given to the shard that hosts their receiver. -/
def compare (sys : System σ) [sys.Inspect] (hosts : σ.Id → Bool) [(splitSig σ).Inspect]
    [(sys.split hosts).Inspect] (env : EnvModel σ) (inputs : List σ.In)
    (within : SysState sys → Bool) : Compared sys env (sys.split hosts) (env.split hosts) where
  alone := explore sys env inputs within
  split := explore (sys.split hosts) (env.split hosts) (inputs.map (Split.route sys hosts))
    fun c => within c.merged
  merged := SysState.merged

/-- The same on `n` shards. -/
def compareShards {n : Nat} (sys : System σ) [sys.Inspect] (hosts : σ.Id → Fin n)
    [(shardsSig σ n).Inspect] [(sys.shards hosts).Inspect] (env : EnvModel σ)
    (inputs : List σ.In) (within : SysState sys → Bool) :
    Compared sys env (sys.shards hosts) (env.shards hosts) where
  alone := explore sys env inputs within
  split := explore (sys.shards hosts) (env.shards hosts) (inputs.map (Shards.route sys hosts))
    fun c => within c.unsharded
  merged := SysState.unsharded

namespace Compared

def complete (r : Compared sys env shards shardsEnv) : Bool :=
  explored r.alone && explored r.split

/-- Every state on the shards, merged, is a state of the system alone. -/
def sound (r : Compared sys env shards shardsEnv) : Bool :=
  r.split.queue.all fun v => r.alone.contains ⟨r.merged v.path.last.state⟩

/-- The shards lose no behaviour: every state of the system alone is a state on the shards,
merged. -/
def full (r : Compared sys env shards shardsEnv) : Bool :=
  let merged : Std.HashSet (UpTo sys env) :=
    r.split.queue.foldl (fun seen v => seen.insert ⟨r.merged v.path.last.state⟩) {}
  r.alone.queue.all fun v => merged.contains v.path.last

def somewhere (r : Compared sys env shards shardsEnv) (p : SysState shards → Bool) : Bool :=
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

/-- Boot actors in a ring that greet the next one when they start, again on a timer, and stop
when told to from outside. The state says whether a greeting was received. -/
abbrev relaySig (n : Nat) [NeZero n] : Signature where
  Id := Fin n
  Msg _ := RelayMsg
  In := Fin n
  Out := Fin n

abbrev relay (n : Nat) [NeZero n] : System (relaySig n) where
  State _ := Bool
  actor i :=
    { init := false
      step := fun s msg =>
        match msg with
        | .ping => (true, [.emit i])
        | .tick => (s, [.send (i + 1) .ping])
        | .halt => (s, [.cancel .tick, .stop])
      recover := fun s => (s, [.send (i + 1) .ping, .after 10 .tick]) }
  accept i := ⟨i, .halt⟩
  boot := List.finRange n

instance {n : Nat} [NeZero n] : (relaySig n).Inspect := {}
instance {n : Nat} [NeZero n] : (relay n).Inspect := {}

/-- The left shard hosts actor 1, so the split boots the two in the other order. -/
def relayHosts : Fin 2 → Bool := (· == 1)

instance : (splitSig (relaySig 2)).Inspect := .split
instance : ((relay 2).split relayHosts).Inspect := .split

def relayEnv (n : Nat) [NeZero n] : EnvModel (relaySig n) where
  link src dst := if src == some 0 then Link.network else if dst == 0 then Link.unordered else {}
  mayCrash i := i == 0
  restarts i := i == 1

def relayCompared :=
  compare (relay 2) relayHosts (relayEnv 2) [1] fun c => c.net.length ≤ 2 && c.outbox.length ≤ 1

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

def fragileLossy :=
  compare fragile id { link := fun _ _ => { lossy := true } } [] fun c =>
    c.net.length ≤ 2 && c.state true ≤ 3

/-- Alone and without faults, `fragile` never moves after it has booted. -/
theorem fragile_alone {c : SysState fragile} (h : fragile.Reachable {} c) :
    c = SysState.init fragile {} := by
  have hnet : (SysState.init fragile {}).net = [] := rfl
  have htimers : ∀ i, (SysState.init fragile {}).timers i = [] := fun i => by cases i <;> rfl
  have hmail : ∀ i, (SysState.init fragile {}).hasMail i = false := fun i => by cases i <;> rfl
  induction h with
  | init => rfl
  | step ev _ hstep ih =>
    subst ih
    cases ev with
    | input x => exact nomatch x
    | deliver e =>
      have hmem := SysState.mem_of_deliverable (SysState.step_deliver.mp hstep).2.1
      simp [hnet] at hmem
    | duplicate e => exact absurd (SysState.step_duplicate.mp hstep).2.1 (by simp [Link.reliable])
    | drop e => exact absurd (SysState.step_drop.mp hstep).1 (by simp [Link.reliable])
    | timeout i msg =>
      have hmem := (SysState.step_timeout.mp hstep).2.1
      simp [htimers] at hmem
    | output out => exact nomatch out
    | crash i => exact absurd (SysState.step_crash.mp hstep).2.1 (by simp)
    | start i =>
      have hmay := (SysState.step_start.mp hstep).2.1
      simp [hmail] at hmay

/-- So the theorem needs its assumption on booting: split, `fragile` starts its second actor
twice, and alone it starts it once. -/
theorem fragile_split_not_alone :
    ∃ c, fragile.SplitReachable id {} c ∧
      ¬∃ c', fragile.Reachable {} c' ∧ SysState.Equiv {} c' c.merged := by
  refine ⟨_, System.SplitReachable.init.step (.start (.inl true)) rfl rfl, ?_⟩
  rintro ⟨c', hc', hequiv⟩
  have hstate := congrFun hequiv.state true
  rw [fragile_alone hc'] at hstate
  exact absurd hstate (by decide)

/-- `true` says 1 and then 0, `false` says 0. The state counts what an actor has said. -/
abbrev chorusSig : Signature where
  Id := Bool
  Msg _ := Unit
  In := Bool
  Out := Nat

abbrev chorus : System chorusSig where
  State _ := Nat
  actor i :=
    { init := 0
      step := fun s _ => (s + 1, [.emit (if i && s == 0 then 1 else 0)])
      recover := fun s => (s, []) }
  accept i := ⟨i, ()⟩

instance : chorusSig.Inspect := {}
instance : chorus.Inspect := {}

instance : (splitSig chorusSig).Inspect := .split
instance : (chorus.split id).Inspect := .split

/-- The split after all three have spoken and the left shard has handed over its 0: the 0 of
the right shard, which is older than the 1, still waits. -/
def chorusSplit : Option (SysState (chorus.split id)) :=
  (SysState.init (chorus.split id) (EnvModel.split {} id)).run (EnvModel.split {} id)
    [ .input (.inr (.inl false)), .input (.inl (.inl true)), .input (.inl (.inl true)),
      .start (.inr false), .start (.inl true),
      .deliver ⟨none, .inr false, ()⟩, .deliver ⟨none, .inl true, ()⟩,
      .deliver ⟨none, .inl true, ()⟩, .output (.inl (.inl 0)) ]

/-- Every state of the chorus alone in which no more has been said. -/
def chorusAlone :=
  Tests.Join.explore chorus {} [true, false] fun c =>
    c.state true ≤ 2 && c.state false ≤ 1 && c.net.length ≤ 3 && c.outbox.length ≤ 3

/-! The same on three shards (`Lanes/Runtime/ShardsSound.lean`): the bank with an account on
each, the relay with three actors each on the shard after its own, and `fragile` on two of
three shards. -/

section Three

open Examples.Bank

abbrev Bank3 := bank (Fin 3) 1

instance : (sig (Fin 3)).Inspect := {}
instance : Bank3.Inspect := {}
instance : (shardsSig (sig (Fin 3)) 3).Inspect := .shards
instance : (Bank3.shards id).Inspect := .shards

def faulty3 : EnvModel (sig (Fin 3)) where
  link src _ := if src.isSome then Link.network else Link.reliable
  mayCrash _ := true

def bank3Compared (env : EnvModel (sig (Fin 3))) (inputs : List (Request (Fin 3))) :=
  compareShards Bank3 id env inputs fun c =>
    c.net.length ≤ 2 && c.outbox.length ≤ 1
      && (Enum.all (α := Fin 3)).all fun a => (c.state a).balance ≤ 2

def bank3Reliable := bank3Compared {} [.transfer ⟨1, 0, 1, 1⟩, .transfer ⟨2, 1, 2, 1⟩]

def bank3Faulty := bank3Compared faulty3 [.transfer ⟨1, 0, 1, 1⟩, .transfer ⟨2, 1, 2, 1⟩]

def relay3Hosts : Fin 3 → Fin 3 := (· + 1)

instance : (shardsSig (relaySig 3) 3).Inspect := .shards
instance : ((relay 3).shards relay3Hosts).Inspect := .shards

def relay3Compared :=
  compareShards (relay 3) relay3Hosts (relayEnv 3) [1] fun c =>
    c.net.length ≤ 3 && c.outbox.length ≤ 1

/-- `true` on the first shard, `false` on the last, so `true` boots first. -/
def fragile3Hosts : Bool → Fin 3 := fun b => if b then 0 else 2

instance : (shardsSig fragileSig 3).Inspect := .shards
instance : (fragile.shards fragile3Hosts).Inspect := .shards

def fragile3Compared :=
  compareShards fragile fragile3Hosts {} [] fun c => c.net.length ≤ 2 && c.state true ≤ 3

def fragile3Lossy :=
  compareShards fragile fragile3Hosts { link := fun _ _ => { lossy := true } } [] fun c =>
    c.net.length ≤ 2 && c.state true ≤ 3

/-- On three shards as on two, the theorem needs its assumption on booting. -/
theorem fragile_shards_not_alone :
    ∃ c, fragile.ShardsReachable fragile3Hosts {} c ∧
      ¬∃ c', fragile.Reachable {} c' ∧ SysState.Equiv {} c' c.unsharded := by
  refine ⟨_, System.ShardsReachable.init.step (.start (0, true)) rfl rfl, ?_⟩
  rintro ⟨c', hc', hequiv⟩
  have hstate := congrFun hequiv.state true
  rw [fragile_alone hc'] at hstate
  exact absurd hstate (by decide)

def threeShards : List (String × Bool) :=
  [ ("shards: the bank on three shards reaches only states of the bank, reliable links",
      bank3Reliable.complete && bank3Reliable.sound && bank3Reliable.full),
    ("shards: the bank on three shards reaches only states of the bank, with crashes and loss",
      bank3Faulty.complete && bank3Faulty.sound && bank3Faulty.full),
    ("shards: a credit crosses from the second shard to the third",
      bank3Faulty.somewhere fun c => c.net.contains ⟨some (1, 1), (2, 2), .credit 1⟩),
    ("shards: the relay on three shards reaches only states of the relay",
      relay3Compared.complete && relay3Compared.sound && relay3Compared.full),
    ("shards: the relay is seen stopped and with a timer armed on a shard",
      relay3Compared.somewhere (fun c => !c.up (1, 0) && c.timers (1, 0) == [])
      && relay3Compared.somewhere fun c => c.state (0, 2) && c.timers (0, 2) == [.tick]),
    ("shards: no copy that only forwards ever runs, on three shards",
      relay3Compared.split.queue.all fun v =>
        let c := v.path.last.state
        (Enum.all (α := Fin 3 × Fin 3)).all (fun x => Shards.atHome (σ := relaySig 3) relay3Hosts x || !c.up x)
          && c.net.all fun e => e.atHomeAll relay3Hosts),
    ("shards: a boot actor that stops as it starts keeps a message on three shards",
      (SysState.init (fragile.shards fragile3Hosts) (EnvModel.shards {} fragile3Hosts)).unsharded.net
        == [⟨some false, true, ()⟩]
      && fragile3Compared.complete && !fragile3Compared.sound),
    ("shards: where the link to it is lossy, three shards are the system again",
      fragile3Lossy.complete && fragile3Lossy.sound && fragile3Lossy.full) ]

end Three

section Bank

open Examples.Bank

/-- No balance of the bank on two shards is ever negative, from the same fact about the bank. -/
theorem split_balance_nonneg {A : Type} [DecidableEq A] (opening : Nat) (hosts : A → Bool)
    (env : EnvModel (sig A)) {c : SysState ((bank A opening).split hosts)}
    (hc : (bank A opening).SplitReachable hosts env c) (a : A) :
    0 ≤ (c.merged.state a).balance :=
  System.Invariant.split_state (Q := fun s : A → Account => 0 ≤ (s a).balance)
    (fun env => balance_nonneg opening env a) hc

/-- The same on any number of shards. -/
theorem shards_balance_nonneg {A : Type} [DecidableEq A] {n : Nat} (opening : Nat)
    (hosts : A → Fin n) (env : EnvModel (sig A)) {c : SysState ((bank A opening).shards hosts)}
    (hc : (bank A opening).ShardsReachable hosts env c) (a : A) :
    0 ≤ (c.unsharded.state a).balance :=
  System.Invariant.shards_state (Q := fun s : A → Account => 0 ≤ (s a).balance)
    (fun env => balance_nonneg opening env a) hc

theorem three_shards_balance_nonneg (env : EnvModel (sig (Fin 3)))
    {c : SysState (Bank3.shards id)} (hc : Bank3.ShardsReachable id env c) (a : Fin 3) :
    0 ≤ (c.unsharded.state a).balance :=
  shards_balance_nonneg 1 id env hc a

end Bank

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
      && relayCompared.somewhere (fun c => c.state (.inr 0) && c.timers (.inr 0) == [.tick])
      && relayCompared.somewhere fun c => c.state (.inl 1) && c.timers (.inl 1) == [.tick]),
    ("split: no copy that only forwards ever runs",
      relayCompared.split.queue.all fun v =>
        let c := v.path.last.state
        !c.up (.inl 0) && !c.up (.inr 1) && c.net.all fun e =>
          e.atHome relayHosts),
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
      && fragileCompared.alone.queue.all fun v => v.path.last.state.state true == 1),
    ("split: where the link to it is lossy nothing is lost, and the split is the system again",
      fragileLossy.complete && fragileLossy.sound && fragileLossy.full),
    ("split: equal outputs of the two shards leave in an order the system alone cannot have",
      match chorusSplit with
      | some c =>
        c.merged.outbox == [0, 1] && Tests.Join.explored chorusAlone
          && !chorusAlone.contains ⟨c.merged⟩
          && chorusAlone.queue.any fun v => v.path.last.state.equiv {} c.merged
      | none => false) ] ++ threeShards

end Tests.Split
