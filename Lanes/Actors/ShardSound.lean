/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Actors.Shard
public import Lanes.Actors.JoinSound

/-!
# A system split across two shards behaves as the one system

`System.split sys hosts` is two shards of `sys` joined: every parcel one emits is a parcel
input of the other. Each actor has a copy on either shard; the copy on the shard that hosts it
is the actor, the other only forwards. `SysState.merged` reads a state of the split as a state
of `sys`.
-/

@[expose] public section

namespace Lanes

variable {σ : Signature}

instance (priority := low) {α : Type} {β : α → Type} [Hashable α] [∀ a, Hashable (β a)] :
    Hashable (Sigma β) where
  hash p := mixHash (hash p.1) (hash p.2)

@[instance_reducible] def Signature.Inspect.shard [σ.Inspect] : (shardSig σ).Inspect where
  enumId := inferInstanceAs (Enum σ.Id)
  reprId := inferInstanceAs (Repr σ.Id)
  hashId := inferInstanceAs (Hashable σ.Id)
  reprMsg i := inferInstanceAs (Repr (σ.Msg i))
  hashMsg i := inferInstanceAs (Hashable (σ.Msg i))
  reprIn := inferInstanceAs (Repr (σ.In ⊕ Parcel σ))
  hashIn := inferInstanceAs (Hashable (σ.In ⊕ Parcel σ))
  reprOut := inferInstanceAs (Repr (σ.Out ⊕ Parcel σ))
  hashOut := inferInstanceAs (Hashable (σ.Out ⊕ Parcel σ))

@[instance_reducible] def System.Inspect.shard {sys : System σ} [sys.Inspect]
    {hosts : σ.Id → Bool} : (sys.shard hosts).Inspect where
  beqState i := inferInstanceAs (BEq (sys.State i))
  reprState i := inferInstanceAs (Repr (sys.State i))
  hashState i := inferInstanceAs (Hashable (sys.State i))

abbrev splitSig (σ : Signature) : Signature := joinSig (shardSig σ) (shardSig σ)

/-- Every parcel a shard emits is a parcel input of the other. Ordinary outputs leave. -/
def shardWiring (σ : Signature) : Wiring (shardSig σ) (shardSig σ) where
  toRight
    | .inl _ => none
    | .inr parcel => some (.inr parcel)
  toLeft
    | .inl _ => none
    | .inr parcel => some (.inr parcel)

/-- `sys` on two shards: the left one hosts the actors `hosts` names, the right one the rest. -/
abbrev System.split (sys : System σ) (hosts : σ.Id → Bool) : System (splitSig σ) :=
  (sys.shard hosts).join (sys.shard fun i => !hosts i) (shardWiring σ)

@[instance_reducible] def Signature.Inspect.split [σ.Inspect] : (splitSig σ).Inspect :=
  @Signature.Inspect.join _ _ .shard .shard

@[instance_reducible] def System.Inspect.split {sys : System σ} [sys.Inspect]
    {hosts : σ.Id → Bool} : (sys.split hosts).Inspect :=
  @System.Inspect.join _ _ _ _ _ .shard .shard

namespace Split

/-- The actor a copy stands for. -/
@[simp] def actorOf : σ.Id ⊕ σ.Id → σ.Id
  | .inl i => i
  | .inr i => i

/-- The copy of `i` on the shard that hosts it. -/
def home (hosts : σ.Id → Bool) (i : σ.Id) : σ.Id ⊕ σ.Id :=
  if hosts i then .inl i else .inr i

@[simp] def atHome (hosts : σ.Id → Bool) : σ.Id ⊕ σ.Id → Bool
  | .inl i => hosts i
  | .inr i => !hosts i

/-- An input of `sys`, given to the shard that hosts its receiver. -/
def route (sys : System σ) (hosts : σ.Id → Bool) (x : σ.In) : (splitSig σ).In :=
  if hosts (sys.accept x).1 then .inl (.inl x) else .inr (.inl x)

@[simp] def output? : (splitSig σ).Out → Option σ.Out
  | .inl (.inl out) | .inr (.inl out) => some out
  | .inl (.inr _) | .inr (.inr _) => none

end Split

/-- A message in flight between copies, as a message between the actors they stand for. -/
def Envelope.merged : Envelope (splitSig σ) → Envelope σ
  | ⟨src, .inl i, msg⟩ => ⟨src.map Split.actorOf, i, msg⟩
  | ⟨src, .inr i, msg⟩ => ⟨src.map Split.actorOf, i, msg⟩

/-- The event of `sys` that an event of the split is. A parcel is not an input or an output of
`sys`, so a parcel from outside or handed to the outside is no event of `sys`. -/
def Event.merged? : Event (splitSig σ) → Option (Event σ)
  | .input (.inl (.inl x)) | .input (.inr (.inl x)) => some (.input x)
  | .input (.inl (.inr _)) | .input (.inr (.inr _)) => none
  | .deliver e => some (.deliver e.merged)
  | .duplicate e => some (.duplicate e.merged)
  | .drop e => some (.drop e.merged)
  | .timeout (.inl i) msg | .timeout (.inr i) msg => some (.timeout i msg)
  | .output out => (Split.output? out).map .output
  | .crash x => some (.crash (Split.actorOf x))
  | .start x => some (.start (Split.actorOf x))

/-- Whether an event of the split is well routed: an input from outside goes to the shard that
hosts its receiver, and no parcel comes from outside. Every other event is. -/
def Event.routed (sys : System σ) (hosts : σ.Id → Bool) : Event (splitSig σ) → Bool
  | .input (.inl (.inl x)) => hosts (sys.accept x).1
  | .input (.inr (.inl x)) => !hosts (sys.accept x).1
  | .input (.inl (.inr _)) | .input (.inr (.inr _)) => false
  | _ => true

/-- The environment of the split that `env` is for `sys`: a link between two copies is the link
between their actors, and a copy on the shard that hosts it crashes and restarts as its actor
does. A copy that only forwards never crashes and never restarts by itself. -/
def EnvModel.split (env : EnvModel σ) (hosts : σ.Id → Bool) : EnvModel (splitSig σ) where
  link src dst := env.link (src.map Split.actorOf) (Split.actorOf dst)
  mayCrash x := Split.atHome hosts x && env.mayCrash (Split.actorOf x)
  restarts x := Split.atHome hosts x && env.restarts (Split.actorOf x)

variable {sys : System σ} {hosts : σ.Id → Bool}

/-- The two shards read as one state: each actor is its copy on the shard that hosts it, the
messages in flight keep their order, and so do the outputs. -/
def SysState.merged (c : SysState (sys.split hosts)) : SysState sys where
  state i := if hosts i then c.state (.inl i) else c.state (.inr i)
  up i := if hosts i then c.up (.inl i) else c.up (.inr i)
  net := c.net.map Envelope.merged
  timers i := if hosts i then c.timers (.inl i) else c.timers (.inr i)
  outbox := c.outbox.filterMap Split.output?

/-- What holds of the split in every well-routed run: nothing is in flight to or from a copy
that only forwards, those copies are down, and no parcel waits to leave. -/
structure SysState.AtHome (c : SysState (sys.split hosts)) : Prop where
  dst : ∀ e ∈ c.net, Split.atHome hosts e.dst = true
  src : ∀ e ∈ c.net, ∀ x, e.src = some x → Split.atHome hosts x = true
  down : ∀ x, Split.atHome hosts x = false → c.up x = false
  outbox : ∀ out ∈ c.outbox, (Split.output? out).isSome = true

/-- The states the split reaches when every input from outside is given to the shard that hosts
its receiver and no parcel comes from outside. -/
inductive System.SplitReachable (sys : System σ) (hosts : σ.Id → Bool) (env : EnvModel σ) :
    SysState (sys.split hosts) → Prop
  | init : SplitReachable sys hosts env (SysState.init (sys.split hosts) (env.split hosts))
  | step {c c' : SysState (sys.split hosts)} (ev : Event (splitSig σ)) :
    SplitReachable sys hosts env c → ev.routed sys hosts = true →
    c.step (env.split hosts) ev = some c' → SplitReachable sys hosts env c'

end Lanes

end
