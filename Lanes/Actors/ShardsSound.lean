/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Actors.ShardSound

/-!
# A system on any number of shards behaves as the one system

`System.joinAll sys route` is a family of systems of one signature side by side, an output that
`route` names as an input of a member being a message to the actor that member's `accept` names.
`System.shards sys hosts` is the family of the shards of `sys`: shard `k` hosts the actors that
`hosts` sends to `k`, and a parcel goes to the shard that hosts its receiver. That is what
`Lanes.Peers` runs, process `k` running `sys.shard (hosts · == k)` with `Peers.Config.home` the
address of process `hosts i` for each actor `i`.

It is not built from `System.split`, because the theorem for two shards does not compose. A
split of a split has shards of a join, not shards of `sys`, and the outer theorem concludes
`Reachable`, which admits parcels from outside and inputs given to the wrong shard, where the
inner theorem needs a well-routed run. A join with a split on one side is not a split, and the
theorem for two shards is about `split` alone, not a congruence for `join`.

`System.ShardsReachable.unsharded` is the theorem, stated and proved as for two shards: every
state of a well-routed run, read as one state, is a state `sys` reaches alone up to
`SysState.Equiv`, when booting loses no message (`System.SteadyBoot`). The shards boot one after
another, each in the order of the boot list. Invariants of actor states proved for every
environment need no condition (`System.Invariant.shards_state`).
-/

@[expose] public section

namespace Lanes

variable {σ τ : Signature} {n : Nat}

abbrev joinAllSig (τ : Signature) (n : Nat) : Signature where
  Id := Fin n × τ.Id
  Msg x := τ.Msg x.2
  In := Fin n × τ.In
  Out := Fin n × τ.Out

def joinAllEffect (sys : Fin n → System τ) (route : τ.Out → Option (Fin n × τ.In))
    (x : Fin n × τ.Id) : Effect τ x.2 → Effect (joinAllSig τ n) x
  | .send to msg => .send (x.1, to) msg
  | .emit out =>
    match route out with
    | some (k, y) => .send (k, ((sys k).accept y).1) ((sys k).accept y).2
    | none => .emit (x.1, out)
  | .after delay_ms msg => .after delay_ms msg
  | .cancel msg => .cancel msg
  | .stop => .stop

/-- The members of a family side by side. An output that `route` sends to a member is a message
to the actor that member's `accept` names; every other output leaves. The members boot in
order. -/
abbrev System.joinAll (sys : Fin n → System τ) (route : τ.Out → Option (Fin n × τ.In)) :
    System (joinAllSig τ n) where
  State x := (sys x.1).State x.2
  actor x := ((sys x.1).actor x.2).mapEff fun eff => [joinAllEffect sys route x eff]
  accept y := ⟨(y.1, ((sys y.1).accept y.2).1), ((sys y.1).accept y.2).2⟩
  boot := (List.finRange n).flatMap fun k => (sys k).boot.map (k, ·)

abbrev shardsSig (σ : Signature) (n : Nat) : Signature := joinAllSig (shardSig σ) n

def shardsRoute (hosts : σ.Id → Fin n) : (shardSig σ).Out → Option (Fin n × (shardSig σ).In)
  | .inl _ => none
  | .inr parcel => some (hosts parcel.1, .inr parcel)

/-- `sys` on `n` shards: shard `k` hosts the actors that `hosts` sends to `k`. -/
abbrev System.shards (sys : System σ) (hosts : σ.Id → Fin n) : System (shardsSig σ n) :=
  System.joinAll (fun k => sys.shard fun i => hosts i == k) (shardsRoute hosts)

@[instance_reducible] def Signature.Inspect.joinAll [τ.Inspect] : (joinAllSig τ n).Inspect where
  enumId := inferInstanceAs (Enum (Fin n × τ.Id))
  reprId := inferInstanceAs (Repr (Fin n × τ.Id))
  hashId := inferInstanceAs (Hashable (Fin n × τ.Id))
  reprMsg x := inferInstanceAs (Repr (τ.Msg x.2))
  hashMsg x := inferInstanceAs (Hashable (τ.Msg x.2))
  reprIn := inferInstanceAs (Repr (Fin n × τ.In))
  hashIn := inferInstanceAs (Hashable (Fin n × τ.In))
  reprOut := inferInstanceAs (Repr (Fin n × τ.Out))
  hashOut := inferInstanceAs (Hashable (Fin n × τ.Out))

@[instance_reducible] def System.Inspect.joinAll {sys : Fin n → System τ}
    {route : τ.Out → Option (Fin n × τ.In)} [∀ k, (sys k).Inspect] :
    (System.joinAll sys route).Inspect where
  beqState x := inferInstanceAs (BEq ((sys x.1).State x.2))
  reprState x := inferInstanceAs (Repr ((sys x.1).State x.2))
  hashState x := inferInstanceAs (Hashable ((sys x.1).State x.2))

@[instance_reducible] def Signature.Inspect.shards [σ.Inspect] : (shardsSig σ n).Inspect :=
  @Signature.Inspect.joinAll _ _ .shard

@[instance_reducible] def System.Inspect.shards {sys : System σ} [sys.Inspect]
    {hosts : σ.Id → Fin n} : (sys.shards hosts).Inspect :=
  @System.Inspect.joinAll _ _ _ _ fun _ => .shard

namespace Shards

/-- Whether a copy is on the shard that hosts its actor. -/
def atHome (hosts : σ.Id → Fin n) (x : Fin n × σ.Id) : Bool := hosts x.2 == x.1

/-- An input of `sys`, given to the shard that hosts its receiver. -/
def route (sys : System σ) (hosts : σ.Id → Fin n) (x : σ.In) : (shardsSig σ n).In :=
  (hosts (sys.accept x).1, .inl x)

def output? : (shardsSig σ n).Out → Option σ.Out
  | (_, .inl out) => some out
  | (_, .inr _) => none

/-- Whether an event is well routed: an input from outside goes to the shard that hosts its
receiver, and no parcel comes from outside. -/
def routed (sys : System σ) (hosts : σ.Id → Fin n) : Event (shardsSig σ n) → Bool
  | .input (k, .inl x) => hosts (sys.accept x).1 == k
  | .input (_, .inr _) => false
  | _ => true

end Shards

/-- A message in flight between copies, as a message between the actors they stand for. -/
def Envelope.unsharded (e : Envelope (shardsSig σ n)) : Envelope σ :=
  ⟨e.src.map Prod.snd, e.dst.2, e.msg⟩

def Envelope.atHomeAll (hosts : σ.Id → Fin n) (e : Envelope (shardsSig σ n)) : Bool :=
  Shards.atHome hosts e.dst && e.src.all (Shards.atHome hosts)

/-- The event of `sys` that an event of the shards is. -/
def Event.unsharded? : Event (shardsSig σ n) → Option (Event σ)
  | .input (_, .inl x) => some (.input x)
  | .input (_, .inr _) => none
  | .deliver e => some (.deliver e.unsharded)
  | .duplicate e => some (.duplicate e.unsharded)
  | .drop e => some (.drop e.unsharded)
  | .timeout x msg => some (.timeout x.2 msg)
  | .output out => (Shards.output? out).map .output
  | .crash x => some (.crash x.2)
  | .start x => some (.start x.2)

/-- The environment of the shards that `env` is for `sys`. A copy that only forwards never
crashes and never restarts by itself. -/
def EnvModel.shards (env : EnvModel σ) (hosts : σ.Id → Fin n) : EnvModel (shardsSig σ n) where
  link src dst := env.link (src.map Prod.snd) dst.2
  mayCrash x := Shards.atHome hosts x && env.mayCrash x.2
  restarts x := Shards.atHome hosts x && env.restarts x.2

variable {sys : System σ} {hosts : σ.Id → Fin n}

/-- The shards read as one state: each actor is its copy on the shard that hosts it. -/
def SysState.unsharded (c : SysState (sys.shards hosts)) : SysState sys where
  state i := c.state (hosts i, i)
  up i := c.up (hosts i, i)
  net := c.net.map Envelope.unsharded
  timers i := c.timers (hosts i, i)
  outbox := c.outbox.filterMap Shards.output?

/-- What holds of the shards in every well-routed run: nothing is in flight to or from a copy
that only forwards, those copies are down, and no parcel waits to leave. -/
structure Shards.AtHome (c : SysState (sys.shards hosts)) : Prop where
  net : ∀ e ∈ c.net, e.atHomeAll hosts = true
  down : ∀ x, Shards.atHome hosts x = false → c.up x = false
  outbox : ∀ out ∈ c.outbox, (Shards.output? out).isSome = true

/-- The states the shards reach when every input from outside is given to the shard that hosts
its receiver and no parcel comes from outside. -/
inductive System.ShardsReachable (sys : System σ) (hosts : σ.Id → Fin n) (env : EnvModel σ) :
    SysState (sys.shards hosts) → Prop
  | init : ShardsReachable sys hosts env (SysState.init (sys.shards hosts) (env.shards hosts))
  | step {c c' : SysState (sys.shards hosts)} (ev : Event (shardsSig σ n)) :
    ShardsReachable sys hosts env c → Shards.routed sys hosts ev = true →
    c.step (env.shards hosts) ev = some c' → ShardsReachable sys hosts env c'

end Lanes
