/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Runtime.ShardSound

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

end

public section

namespace Lanes

variable {σ : Signature} {n : Nat} {sys : System σ} {hosts : σ.Id → Fin n} {env : EnvModel σ}

namespace Shards

theorem atHome_iff {x : Fin n × σ.Id} : atHome hosts x = true ↔ hosts x.2 = x.1 := by
  simp [atHome]

theorem routed_route (sys : System σ) (hosts : σ.Id → Fin n) (x : σ.In) :
    routed sys hosts (.input (route sys hosts x)) = true := by
  simp [route, routed]

/-- The copy at home of an actor is named by the actor. -/
theorem eq_home {x : Fin n × σ.Id} (h : atHome hosts x = true) : x = (hosts x.2, x.2) :=
  Prod.ext (atHome_iff.mp h).symm rfl

theorem eq_of_snd {x y : Fin n × σ.Id} (hx : atHome hosts x = true) (hy : atHome hosts y = true)
    (h : x.2 = y.2) : x = y := by
  rw [eq_home hx, eq_home hy, h]

theorem update_home {β : σ.Id → Type} (f : (x : Fin n × σ.Id) → β x.2) (i : σ.Id) (v : β i) :
    (fun j => update f (hosts i, i) v (hosts j, j)) = update (fun j => f (hosts j, j)) i v := by
  funext j
  by_cases h : j = i
  · subst h
    simp
  · have hne : ((hosts j, j) : Fin n × σ.Id) ≠ (hosts i, i) := fun e => h (congrArg Prod.snd e)
    simp [update_of_ne _ _ hne, update_of_ne _ _ h]

/-- An effect of an actor, as its copy on shard `x.1` performs it. -/
def effect (sys : System σ) (hosts : σ.Id → Fin n) (x : Fin n × σ.Id) (eff : Effect σ x.2) :
    Effect (shardsSig σ n) x :=
  joinAllEffect (fun k => sys.shard fun i => hosts i == k) (shardsRoute hosts) x
    (shardEffect (fun i => hosts i == x.1) eff)

theorem effect_isStop (x : Fin n × σ.Id) (eff : Effect σ x.2) :
    (effect sys hosts x eff).isStop = eff.isStop := by
  cases eff with
  | send to msg =>
    by_cases h : hosts to = x.1 <;>
      simp [effect, shardEffect, joinAllEffect, shardsRoute, Effect.isStop, h]
  | _ => simp [effect, shardEffect, joinAllEffect, shardsRoute, Effect.isStop]

theorem effect_send (x : Fin n × σ.Id) (to : σ.Id) (msg : σ.Msg to) :
    effect sys hosts x (.send to msg) = .send (hosts to, to) msg := by
  obtain ⟨k, i⟩ := x
  by_cases h : hosts to = k
  · subst h
    simp [effect, shardEffect, joinAllEffect]
  · simp [effect, shardEffect, joinAllEffect, shardsRoute, h]

theorem actor_eq {x : Fin n × σ.Id} (hx : atHome hosts x = true) :
    (sys.shards hosts).actor x
      = ((sys.actor x.2).mapEff fun eff => [shardEffect (fun i => hosts i == x.1) eff]).mapEff
          fun eff => [joinAllEffect (fun k => sys.shard fun i => hosts i == k)
            (shardsRoute hosts) x eff] := by
  show Actor.mapEff _ (if (hosts x.2 == x.1) = true then _ else _) = _
  simp only [show (hosts x.2 == x.1) = true from hx, ↓reduceIte]

theorem actor_step (i : σ.Id) (s : sys.State i) (msg : σ.Msg i) :
    ((sys.shards hosts).actor (hosts i, i)).step s msg
      = (((sys.actor i).step s msg).1,
          ((sys.actor i).step s msg).2.map (effect sys hosts (hosts i, i))) := by
  rw [actor_eq (by simp [atHome])]
  exact Prod.ext rfl (flatMap_singletons _ _ _)

theorem actor_recover (i : σ.Id) (s : sys.State i) :
    ((sys.shards hosts).actor (hosts i, i)).recover s
      = (((sys.actor i).recover s).1,
          ((sys.actor i).recover s).2.map (effect sys hosts (hosts i, i))) := by
  rw [actor_eq (by simp [atHome])]
  exact Prod.ext rfl (flatMap_singletons _ _ _)

end Shards

namespace Envelope

theorem atHomeAll_dst {e : Envelope (shardsSig σ n)} (h : e.atHomeAll hosts = true) :
    Shards.atHome hosts e.dst = true := by
  simp only [atHomeAll, Bool.and_eq_true] at h
  exact h.1

theorem unsharded_inj {e e' : Envelope (shardsSig σ n)} (he : e.atHomeAll hosts = true)
    (he' : e'.atHomeAll hosts = true) (h : e.unsharded = e'.unsharded) : e = e' := by
  obtain ⟨src, dst, msg⟩ := e
  obtain ⟨src', dst', msg'⟩ := e'
  simp only [atHomeAll, Bool.and_eq_true] at he he'
  simp only [unsharded, Envelope.mk.injEq] at h
  obtain ⟨hsrc, hdst, hmsg⟩ := h
  obtain rfl := Shards.eq_of_snd he.1 he'.1 hdst
  have hsrc : src = src' := by
    rcases src with _ | s <;> rcases src' with _ | s' <;> simp only [Option.map_none,
      Option.map_some, reduceCtorEq, Option.some.injEq] at hsrc ⊢
    exact Shards.eq_of_snd he.2 he'.2 hsrc
  subst hsrc
  rw [eq_of_heq hmsg]

theorem unsharded_sameLink {e x : Envelope (shardsSig σ n)} (he : e.atHomeAll hosts = true)
    (hx : x.atHomeAll hosts = true) : e.unsharded.sameLink x.unsharded = e.sameLink x := by
  simp only [atHomeAll, Bool.and_eq_true] at he hx
  simp only [sameLink, unsharded]
  congr 1
  · apply decide_eq_decide.mpr
    constructor
    · intro h
      rcases hs : e.src with _ | s <;> rcases hs' : x.src with _ | s' <;>
        simp only [hs, hs', Option.map_none, Option.map_some, reduceCtorEq,
          Option.some.injEq] at h ⊢
      rw [hs] at he
      rw [hs'] at hx
      exact Shards.eq_of_snd he.2 hx.2 h
    · exact fun h => h ▸ rfl
  · exact decide_eq_decide.mpr ⟨Shards.eq_of_snd he.1 hx.1, fun h => h ▸ rfl⟩

end Envelope

namespace SysState

variable {c : SysState (sys.shards hosts)}

private theorem unsharded_setState (c : SysState (sys.shards hosts)) (i : σ.Id)
    (v : sys.State i) :
    ({ c with state := update c.state (hosts i, i) v } : SysState (sys.shards hosts)).unsharded
      = { c.unsharded with state := update c.unsharded.state i v } :=
  SysState.ext' (Shards.update_home (β := sys.State) c.state i v) rfl rfl rfl rfl

private theorem unsharded_setUp (c : SysState (sys.shards hosts)) (i : σ.Id) (b : Bool) :
    ({ c with up := update c.up (hosts i, i) b } : SysState (sys.shards hosts)).unsharded
      = { c.unsharded with up := update c.unsharded.up i b } :=
  SysState.ext' rfl (Shards.update_home (β := fun _ => Bool) c.up i b) rfl rfl rfl

private theorem unsharded_retime (c : SysState (sys.shards hosts)) (i : σ.Id)
    (f : List (σ.Msg i) → List (σ.Msg i)) :
    ({ c with timers := update c.timers (hosts i, i) (f (c.timers (hosts i, i))) } :
        SysState (sys.shards hosts)).unsharded
      = { c.unsharded with timers := update c.unsharded.timers i (f (c.unsharded.timers i)) } :=
  SysState.ext' rfl rfl rfl
    (Shards.update_home (β := fun i => List (σ.Msg i)) c.timers i _) rfl

private theorem perform_unsharded (hc : Shards.AtHome c) (i : σ.Id) (eff : Effect σ i) :
    Shards.AtHome (c.perform (hosts i, i) (Shards.effect sys hosts (hosts i, i) eff)) ∧
      (c.perform (hosts i, i) (Shards.effect sys hosts (hosts i, i) eff)).unsharded
        = c.unsharded.perform i eff := by
  cases eff with
  | send to msg =>
    rw [Shards.effect_send]
    refine ⟨⟨fun e he => ?_, hc.down, hc.outbox⟩, ?_⟩
    · rcases List.mem_append.mp he with he | he
      · exact hc.net e he
      · obtain rfl := List.mem_singleton.mp he
        simp [Envelope.atHomeAll, Shards.atHome]
    · simp [perform, unsharded, Envelope.unsharded]
  | emit out =>
    refine ⟨⟨hc.net, hc.down, fun o ho => ?_⟩, ?_⟩
    · rcases List.mem_append.mp ho with ho | ho
      · exact hc.outbox o ho
      · obtain rfl := List.mem_singleton.mp ho
        rfl
    · simp [Shards.effect, shardEffect, joinAllEffect, shardsRoute, perform, unsharded,
        Shards.output?]
  | after delay_ms msg =>
    exact ⟨⟨hc.net, hc.down, hc.outbox⟩,
      unsharded_retime c i fun t => if msg ∈ t then t else t ++ [msg]⟩
  | cancel msg => exact ⟨⟨hc.net, hc.down, hc.outbox⟩, unsharded_retime c i fun t => t.erase msg⟩
  | stop => exact ⟨hc, rfl⟩

private theorem performAll_unsharded (hc : Shards.AtHome c) (i : σ.Id) (effs : List (Effect σ i)) :
    Shards.AtHome (c.performAll (hosts i, i) (effs.map (Shards.effect sys hosts (hosts i, i)))) ∧
      (c.performAll (hosts i, i) (effs.map (Shards.effect sys hosts (hosts i, i)))).unsharded
        = c.unsharded.performAll i effs := by
  induction effs generalizing c with
  | nil => exact ⟨hc, rfl⟩
  | cons eff effs ih =>
    obtain ⟨h₁, h₂⟩ := perform_unsharded hc i eff
    obtain ⟨h₃, h₄⟩ := ih h₁
    exact ⟨h₃, by rw [List.map_cons, performAll_cons, h₄, h₂, performAll_cons]⟩

private theorem down_unsharded (hc : Shards.AtHome c) (i : σ.Id) :
    Shards.AtHome (c.down (env.shards hosts) (hosts i, i)) ∧
      (c.down (env.shards hosts) (hosts i, i)).unsharded = c.unsharded.down env i := by
  have hx : Shards.atHome hosts (hosts i, i) = true := by simp [Shards.atHome]
  refine ⟨⟨fun e he => hc.net e (List.mem_filter.mp he).1, fun y hy => ?_, hc.outbox⟩, ?_⟩
  · by_cases hyx : y = (hosts i, i)
    · subst hyx
      simp [down]
    · simpa [down, hyx] using hc.down y hy
  · have hnet : (c.net.filter fun e => decide (e.dst ≠ (hosts i, i))
          || ((env.shards hosts).link e.src e.dst).lossy).map Envelope.unsharded
        = (c.net.map Envelope.unsharded).filter fun e => decide (e.dst ≠ i)
          || (env.link e.src e.dst).lossy := by
      rw [List.filter_map]
      congr 1
      refine List.filter_congr fun e he => ?_
      have hne : e.dst ≠ (hosts i, i) ↔ e.dst.2 ≠ i :=
        not_congr ⟨fun h => h ▸ rfl,
          fun h => Shards.eq_of_snd (Envelope.atHomeAll_dst (hc.net e he)) hx h⟩
      simp only [Function.comp, Envelope.unsharded, EnvModel.shards]
      congr 1
      exact decide_eq_decide.mpr hne
    have hup := congrArg SysState.up (unsharded_setUp c i false)
    have htimers := congrArg SysState.timers (unsharded_retime c i fun _ => [])
    exact SysState.ext' rfl hup hnet htimers rfl

private theorem settle_unsharded (hc : Shards.AtHome c) (i : σ.Id) (v : sys.State i)
    (effs : List (Effect σ i)) :
    Shards.AtHome (c.settle (env.shards hosts) (hosts i, i)
        (v, effs.map (Shards.effect sys hosts (hosts i, i)))) ∧
      (c.settle (env.shards hosts) (hosts i, i)
        (v, effs.map (Shards.effect sys hosts (hosts i, i)))).unsharded
        = c.unsharded.settle env i (v, effs) := by
  have hstop : (effs.map (Shards.effect sys hosts (hosts i, i))).any Effect.isStop
      = effs.any Effect.isStop :=
    Effect.any_isStop_map (Shards.effect_isStop (hosts i, i)) effs
  obtain ⟨h₁, h₂⟩ := performAll_unsharded
    (c := { c with state := update c.state (hosts i, i) v }) ⟨hc.net, hc.down, hc.outbox⟩ i effs
  rw [unsharded_setState c i v] at h₂
  simp only [settle, hstop]
  split
  · obtain ⟨h₃, h₄⟩ := down_unsharded (env := env) h₁ i
    exact ⟨h₃, by rw [h₄, h₂]⟩
  · exact ⟨h₁, h₂⟩

private theorem handle_unsharded (hc : Shards.AtHome c) (i : σ.Id) (msg : σ.Msg i) :
    Shards.AtHome (c.handle (env.shards hosts) (hosts i, i) msg) ∧
      (c.handle (env.shards hosts) (hosts i, i) msg).unsharded
        = c.unsharded.handle env i msg := by
  have h := settle_unsharded (env := env) hc i ((sys.actor i).step (c.state (hosts i, i)) msg).1
    ((sys.actor i).step (c.state (hosts i, i)) msg).2
  simp only [handle]
  rw [Shards.actor_step]
  exact h

private theorem startActor_unsharded (hc : Shards.AtHome c) (i : σ.Id) :
    Shards.AtHome (c.startActor (env.shards hosts) (hosts i, i)) ∧
      (c.startActor (env.shards hosts) (hosts i, i)).unsharded
        = c.unsharded.startActor env i := by
  have hup : Shards.AtHome
      ({ c with up := update c.up (hosts i, i) true } : SysState (sys.shards hosts)) := by
    refine ⟨hc.net, fun y hy => ?_, hc.outbox⟩
    have hyx : y ≠ (hosts i, i) := fun h => by
      rw [h] at hy
      simp [Shards.atHome] at hy
    simpa [hyx] using hc.down y hy
  have h := settle_unsharded (env := env) hup i
    ((sys.actor i).recover (c.state (hosts i, i))).1
    ((sys.actor i).recover (c.state (hosts i, i))).2
  rw [unsharded_setUp c i true] at h
  simp only [startActor]
  rw [Shards.actor_recover]
  exact h

private theorem unsharded_erase (hc : Shards.AtHome c) {e : Envelope (shardsSig σ n)}
    (he : e ∈ c.net) :
    Shards.AtHome ({ c with net := c.net.erase e } : SysState (sys.shards hosts)) ∧
      ({ c with net := c.net.erase e } : SysState (sys.shards hosts)).unsharded
        = { c.unsharded with net := c.unsharded.net.erase e.unsharded } :=
  ⟨⟨fun x hx => hc.net x (List.mem_of_mem_erase hx), hc.down, hc.outbox⟩,
    SysState.ext' rfl rfl
      (map_erase fun x hx h => Envelope.unsharded_inj (hc.net x hx) (hc.net e he) h) rfl rfl⟩

private theorem deliverable_unsharded (hc : Shards.AtHome c) {e : Envelope (shardsSig σ n)}
    (h : c.deliverable (env.shards hosts) e = true) :
    c.unsharded.deliverable env e.unsharded = true := by
  have he := mem_of_deliverable h
  have hlink : (env.shards hosts).link e.src e.dst = env.link e.unsharded.src e.unsharded.dst :=
    rfl
  simp only [deliverable, hlink] at h ⊢
  split at h
  · next hord =>
    have hfind : c.net.find? e.sameLink = some e := by simpa using h
    have hsame : ∀ x ∈ c.net, (e.unsharded.sameLink ∘ Envelope.unsharded) x = e.sameLink x :=
      fun x hx => Envelope.unsharded_sameLink (hc.net e he) (hc.net x hx)
    simp [hord, unsharded, List.find?_map, find?_congr hsame, hfind]
  · next hord =>
    simp only [hord]
    simpa [unsharded] using List.mem_map_of_mem (f := Envelope.unsharded) he

private theorem up_atHome (hc : Shards.AtHome c) {x : Fin n × σ.Id} (hup : c.up x = true) :
    Shards.atHome hosts x = true := by
  cases h : Shards.atHome hosts x with
  | true => rfl
  | false => simp [hc.down x h] at hup

end SysState

/-- One event of the shards is one event of `sys`: it leads `c.unsharded` to `c'.unsharded`,
but for the order of the outputs waiting when the event hands one over. -/
theorem Shards.AtHome.step {c c' : SysState (sys.shards hosts)} {ev : Event (shardsSig σ n)}
    (hc : Shards.AtHome c) (hev : Shards.routed sys hosts ev = true)
    (hstep : c.step (env.shards hosts) ev = some c') :
    Shards.AtHome c' ∧ ∃ ev' m, ev.unsharded? = some ev' ∧ c.unsharded.step env ev' = some m ∧
      m.outbox.Perm c'.unsharded.outbox ∧ { m with outbox := c'.unsharded.outbox } = c'.unsharded := by
  open SysState in
  have same : ∀ {m m' : SysState sys}, m' = m →
      m.outbox.Perm m'.outbox ∧ { m with outbox := m'.outbox } = m' := by
    rintro m _ rfl
    exact ⟨.refl _, rfl⟩
  cases ev with
  | input y =>
    obtain rfl := step_input.mp hstep
    obtain ⟨k, x | parcel⟩ := y
    · refine ⟨⟨fun e he => ?_, hc.down, hc.outbox⟩, .input x, _, rfl, step_input.mpr rfl, same ?_⟩
      · rcases List.mem_append.mp he with he | he
        · exact hc.net e he
        · obtain rfl := List.mem_singleton.mp he
          simpa [Envelope.atHomeAll, Shards.routed, Shards.atHome] using hev
      · simp [unsharded, Envelope.unsharded]
    · exact absurd hev (by simp [Shards.routed])
  | deliver e =>
    obtain ⟨hup, hdel, rfl⟩ := step_deliver.mp hstep
    obtain ⟨src, ⟨k, i⟩, msg⟩ := e
    have hx := up_atHome hc hup
    obtain rfl : hosts i = k := Shards.atHome_iff.mp hx
    obtain ⟨h₁, h₂⟩ := unsharded_erase hc (mem_of_deliverable hdel)
    obtain ⟨h₃, h₄⟩ := handle_unsharded (env := env) h₁ i msg
    rw [h₂] at h₄
    exact ⟨h₃, .deliver _, _, rfl,
      step_deliver.mpr ⟨hup, deliverable_unsharded hc hdel, rfl⟩, same h₄⟩
  | duplicate e =>
    obtain ⟨hup, hdup, hdel, rfl⟩ := step_duplicate.mp hstep
    obtain ⟨src, ⟨k, i⟩, msg⟩ := e
    have hx := up_atHome hc hup
    obtain rfl : hosts i = k := Shards.atHome_iff.mp hx
    obtain ⟨h₃, h₄⟩ := handle_unsharded (env := env) hc i msg
    exact ⟨h₃, .duplicate _, _, rfl,
      step_duplicate.mpr ⟨hup, hdup, deliverable_unsharded hc hdel, rfl⟩, same h₄⟩
  | drop e =>
    obtain ⟨hlossy, hmem, rfl⟩ := step_drop.mp hstep
    obtain ⟨h₁, h₂⟩ := unsharded_erase hc hmem
    exact ⟨h₁, .drop e.unsharded, _, rfl,
      step_drop.mpr ⟨hlossy, List.mem_map_of_mem hmem, rfl⟩, same h₂⟩
  | timeout x msg =>
    obtain ⟨hup, hmem, rfl⟩ := step_timeout.mp hstep
    obtain ⟨k, i⟩ := x
    have hx := up_atHome hc hup
    obtain rfl : hosts i = k := Shards.atHome_iff.mp hx
    obtain ⟨h₃, h₄⟩ := handle_unsharded (env := env)
      (c := { c with timers := update c.timers (hosts i, i) ((c.timers (hosts i, i)).erase msg) })
      ⟨hc.net, hc.down, hc.outbox⟩ i msg
    rw [unsharded_retime c i fun t => t.erase msg] at h₄
    exact ⟨h₃, .timeout i msg, _, rfl, step_timeout.mpr ⟨hup, hmem, h₄⟩, same rfl⟩
  | output out =>
    obtain ⟨hmem, rfl⟩ := step_output.mp hstep
    obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp (hc.outbox out hmem)
    exact ⟨⟨hc.net, hc.down, fun x hx => hc.outbox x (mem_of_mem_erase hx)⟩, .output o, _,
      by simp [Event.unsharded?, ho],
      step_output.mpr ⟨List.mem_filterMap.mpr ⟨out, hmem, ho⟩, rfl⟩,
      filterMap_erase_perm hmem ho, rfl⟩
  | crash x =>
    obtain ⟨hup, hcrash, rfl⟩ := step_crash.mp hstep
    obtain ⟨k, i⟩ := x
    have hx := up_atHome hc hup
    obtain rfl : hosts i = k := Shards.atHome_iff.mp hx
    obtain ⟨h₁, h₂⟩ := down_unsharded (env := env) hc i
    exact ⟨h₁, .crash i, _, rfl,
      step_crash.mpr ⟨hup, by simpa [EnvModel.shards, hx] using hcrash, rfl⟩, same h₂⟩
  | start x =>
    obtain ⟨hup, hmail, rfl⟩ := step_start.mp hstep
    have hx : Shards.atHome hosts x = true := by
      rcases hmail with hmail | hrestarts
      · obtain ⟨e, he, rfl⟩ : ∃ e ∈ c.net, e.dst = x := by simpa [hasMail] using hmail
        exact Envelope.atHomeAll_dst (hc.net e he)
      · simp only [EnvModel.shards, Bool.and_eq_true] at hrestarts
        exact hrestarts.1
    obtain ⟨k, i⟩ := x
    obtain rfl : hosts i = k := Shards.atHome_iff.mp hx
    obtain ⟨h₁, h₂⟩ := startActor_unsharded (env := env) hc i
    refine ⟨h₁, .start i, _, rfl,
      step_start.mpr ⟨hup, hmail.imp (fun hmail => ?_) (fun h => ?_), rfl⟩, same h₂⟩
    · obtain ⟨e, he, hdst⟩ : ∃ e ∈ c.net, e.dst = (hosts i, i) := by
        simpa [hasMail] using hmail
      simpa [hasMail, unsharded] using ⟨e, he, by simp [Envelope.unsharded, hdst]⟩
    · simpa [EnvModel.shards, hx] using h

namespace SysState

private theorem blank_atHome : Shards.AtHome (SysState.blank (sys.shards hosts)) :=
  ⟨fun _ h => (nomatch h), fun _ _ => rfl, fun _ h => (nomatch h)⟩

private theorem blank_unsharded :
    (SysState.blank (sys.shards hosts)).unsharded = SysState.blank sys :=
  SysState.ext' (funext fun i => by simp [unsharded, blank, Actor.mapEff]) rfl rfl rfl rfl

private theorem boot_unsharded (l : List (Fin n × σ.Id))
    (hl : ∀ x ∈ l, Shards.atHome hosts x = true) :
    ∀ c : SysState (sys.shards hosts), Shards.AtHome c →
      Shards.AtHome (l.foldl (fun c x => c.startActor (env.shards hosts) x) c) ∧
        (l.foldl (fun c x => c.startActor (env.shards hosts) x) c).unsharded
          = (l.map Prod.snd).foldl (fun c i => c.startActor env i) c.unsharded := by
  induction l with
  | nil => exact fun c hc => ⟨hc, rfl⟩
  | cons x l ih =>
    intro c hc
    obtain ⟨k, i⟩ := x
    obtain rfl : hosts i = k := Shards.atHome_iff.mp (hl _ List.mem_cons_self)
    obtain ⟨h₁, h₂⟩ := startActor_unsharded (env := env) hc i
    obtain ⟨h₃, h₄⟩ := ih (fun y hy => hl y (List.mem_cons_of_mem _ hy)) _ h₁
    exact ⟨h₃, by rw [List.foldl_cons, h₄, h₂, List.map_cons, List.foldl_cons]⟩

/-- Booting the actors shard by shard, each shard in the order of the boot list, leaves the same
state as booting them in that order, up to the order of messages on different links. -/
theorem boot_grouped (hosts : σ.Id → Fin n) (l : List σ.Id) (c : SysState sys) :
    Equiv env (l.foldl started c)
      (((List.finRange n).flatMap fun k => l.filter (hosts · == k)).foldl started c) := by
  suffices h : ∀ (ks : List (Fin n)), ks.Nodup → ∀ (l : List σ.Id), (∀ i ∈ l, hosts i ∈ ks) →
      ∀ c : SysState sys, Equiv env (l.foldl started c)
        ((ks.flatMap fun k => l.filter (hosts · == k)).foldl started c) from
    h _ (List.nodup_finRange n) l (fun i _ => List.mem_finRange _) c
  intro ks
  induction ks with
  | nil =>
    intro _ l hl c
    cases l with
    | nil => exact .refl env _
    | cons i l => exact absurd (hl i List.mem_cons_self) (by simp)
  | cons k ks ih =>
    intro hnodup l hl c
    have hk : k ∉ ks := (List.nodup_cons.mp hnodup).1
    have hrest : (ks.flatMap fun k' => (l.filter fun i => !(hosts i == k)).filter (hosts · == k'))
        = ks.flatMap fun k' => l.filter (hosts · == k') := by
      simp only [List.flatMap_def]
      congr 1
      refine List.map_congr_left fun k' hk' => ?_
      rw [List.filter_filter]
      refine List.filter_congr fun i _ => ?_
      by_cases h : hosts i = k'
      · have hne : k' ≠ k := fun h' => hk (h' ▸ hk')
        simp [h, hne]
      · simp [h]
    have hl' : ∀ i ∈ l.filter (fun i => !(hosts i == k)), hosts i ∈ ks := fun i hi => by
      obtain ⟨hi, hik⟩ := List.mem_filter.mp hi
      rcases List.mem_cons.mp (hl i hi) with h | h
      · simp [h] at hik
      · exact h
    have h := (boot_sorted (env := env) (hosts · == k) l c).trans
      (by rw [List.foldl_append]; exact ih (List.nodup_cons.mp hnodup).2 _ hl' _)
    rw [hrest, ← List.foldl_append] at h
    simpa only [List.flatMap_cons] using h

end SysState

/-- The shards boot one after another: the first state, read as one state, is `sys` booted shard
by shard. -/
theorem SysState.init_unsharded (sys : System σ) (hosts : σ.Id → Fin n) (env : EnvModel σ) :
    Shards.AtHome (SysState.init (sys.shards hosts) (env.shards hosts)) ∧
      (SysState.init (sys.shards hosts) (env.shards hosts)).unsharded
        = ((List.finRange n).flatMap fun k => sys.boot.filter (hosts · == k)).foldl
          (fun c i => c.startActor env i) (SysState.blank sys) := by
  have hl : ∀ x ∈ (List.finRange n).flatMap
      (fun k => (sys.boot.filter (hosts · == k)).map ((k, ·) : σ.Id → Fin n × σ.Id)),
      Shards.atHome hosts x = true := by
    intro x hx
    obtain ⟨k, -, hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    simpa [Shards.atHome] using (List.mem_filter.mp hi).2
  obtain ⟨h₁, h₂⟩ := SysState.boot_unsharded (env := env) _ hl _ SysState.blank_atHome
  refine ⟨h₁, h₂.trans ?_⟩
  rw [SysState.blank_unsharded, List.map_flatMap]
  simp [List.map_map, Function.comp_def]

/-- The first state of the shards, read as one state, is the first state of `sys` up to the
order of messages on different links. -/
theorem SysState.init_unsharded_equiv (hosts : σ.Id → Fin n) (hboot : sys.SteadyBoot env) :
    SysState.Equiv env (SysState.init sys env)
      (SysState.init (sys.shards hosts) (env.shards hosts)).unsharded := by
  rw [(SysState.init_unsharded sys hosts env).2, SysState.init,
    SysState.boot_eq_started hboot _ (fun _ h => h),
    SysState.boot_eq_started hboot _ fun i hi => by
      obtain ⟨_, -, hi⟩ := List.mem_flatMap.mp hi
      exact (List.mem_filter.mp hi).1]
  exact SysState.boot_grouped hosts sys.boot _

variable {c : SysState (sys.shards hosts)}

theorem System.ShardsReachable.atHome (h : sys.ShardsReachable hosts env c) : Shards.AtHome c := by
  induction h with
  | init => exact (SysState.init_unsharded sys hosts env).1
  | step ev _ hev hstep ih => exact (ih.step hev hstep).1

/-- The theorem in its general form: if the first state of the shards, read as one state, is a
state `sys` reaches up to the order of unrelated messages, so is every state of a well-routed
run. -/
theorem System.ShardsReachable.unsharded_of_init
    (hinit : ∃ c₀, sys.Reachable env c₀ ∧
      SysState.Equiv env c₀ (SysState.init (sys.shards hosts) (env.shards hosts)).unsharded)
    (h : sys.ShardsReachable hosts env c) :
    ∃ c', sys.Reachable env c' ∧ SysState.Equiv env c' c.unsharded := by
  induction h with
  | init => exact hinit
  | @step c c₂ ev hc hev hstep ih =>
    obtain ⟨-, ev', m, -, hstep', hperm, hm⟩ := hc.atHome.step (env := env) hev hstep
    exact (System.Near.step ev' ih hstep').equiv (hm ▸ ⟨rfl, rfl, rfl, .refl env _, hperm⟩)

/-- **A system on any number of shards behaves as the one system.** In a run in which every
input from outside is given to the shard that hosts its receiver and no parcel comes from
outside, every state, read as one state, is a state `sys` reaches alone, up to the order of
messages no actor can tell apart and of the outputs waiting to leave. -/
theorem System.ShardsReachable.unsharded (hboot : sys.SteadyBoot env)
    (h : sys.ShardsReachable hosts env c) :
    ∃ c', sys.Reachable env c' ∧ SysState.Equiv env c' c.unsharded :=
  h.unsharded_of_init ⟨_, .init, SysState.init_unsharded_equiv hosts hboot⟩

theorem System.Invariant.shards {P : SysState sys → Prop} (h : sys.Invariant env P)
    (hP : ∀ a b, SysState.Equiv env a b → P a → P b) (hboot : sys.SteadyBoot env)
    (hc : sys.ShardsReachable hosts env c) : P c.unsharded :=
  let ⟨c', hc', hequiv⟩ := hc.unsharded hboot
  hP c' _ hequiv (h c' hc')

theorem System.ShardsReachable.run {evs : List (Event (shardsSig σ n))}
    {c c' : SysState (sys.shards hosts)} (h : sys.ShardsReachable hosts env c)
    (hevs : ∀ ev ∈ evs, Shards.routed sys hosts ev = true)
    (hrun : c.run (env.shards hosts) evs = some c') : sys.ShardsReachable hosts env c' := by
  induction evs generalizing c with
  | nil =>
    simp only [SysState.run, Option.some.injEq] at hrun
    exact hrun ▸ h
  | cons ev evs ih =>
    simp only [SysState.run] at hrun
    cases hstep : c.step (env.shards hosts) ev with
    | none => simp [hstep] at hrun
    | some c₁ =>
      exact ih (h.step ev (hevs ev List.mem_cons_self) hstep)
        (fun e he => hevs e (List.mem_cons_of_mem _ he)) (by simpa [hstep] using hrun)

/-- A well-routed run stays one when every link may also lose messages. -/
theorem System.ShardsReachable.lossy (h : sys.ShardsReachable hosts env c) :
    sys.ShardsReachable hosts env.lossy c := by
  have henv : env.lossy.shards hosts = (env.shards hosts).lossy := rfl
  have hdrops : ∀ drops : List (Envelope (shardsSig σ n)),
      ∀ ev ∈ drops.map Event.drop, Shards.routed sys hosts ev = true := by
    intro drops ev hev
    obtain ⟨d, -, rfl⟩ := List.mem_map.mp hev
    rfl
  induction h with
  | init =>
    obtain ⟨drops, hrun⟩ := SysState.init_lossy (sys.shards hosts) (env.shards hosts)
    rw [← henv] at hrun
    exact System.ShardsReachable.init.run (hdrops drops) hrun
  | step ev _ hev hstep ih =>
    obtain ⟨drops, hrun⟩ := SysState.step_lossy hstep
    rw [← henv] at hrun
    refine ih.run (fun e he => ?_) hrun
    rcases List.mem_cons.mp he with rfl | he
    · exact hev
    · exact hdrops drops e he

/-- An invariant of `sys` proved for every environment asks nothing of booting. -/
theorem System.Invariant.shards_of_forall {P : SysState sys → Prop}
    (h : ∀ env, sys.Invariant env P) (hP : ∀ a b, SysState.Equiv env.lossy a b → P a → P b)
    (hc : sys.ShardsReachable hosts env c) : P c.unsharded :=
  let ⟨c', hc', hequiv⟩ := hc.lossy.unsharded fun _ _ _ _ _ => rfl
  hP c' _ hequiv (h env.lossy c' hc')

/-- An invariant of the actor states of `sys`, proved for every environment, holds of the actor
states of the shards. -/
theorem System.Invariant.shards_state {Q : ((i : σ.Id) → sys.State i) → Prop}
    (h : ∀ env, sys.Invariant env fun c => Q c.state) (hc : sys.ShardsReachable hosts env c) :
    Q c.unsharded.state :=
  System.Invariant.shards_of_forall h (fun _ _ hequiv ha => hequiv.state ▸ ha) hc

end Lanes
