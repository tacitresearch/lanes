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
def actorOf {ι : Type} : ι ⊕ ι → ι
  | .inl i => i
  | .inr i => i

/-- The copy of `i` on the shard that hosts it. -/
def home {ι : Type} (hosts : ι → Bool) (i : ι) : ι ⊕ ι :=
  if hosts i then .inl i else .inr i

def atHome {ι : Type} (hosts : ι → Bool) : ι ⊕ ι → Bool
  | .inl i => hosts i
  | .inr i => !hosts i

/-- An input of `sys`, given to the shard that hosts its receiver. -/
def route (sys : System σ) (hosts : σ.Id → Bool) (x : σ.In) : (splitSig σ).In :=
  if hosts (sys.accept x).1 then .inl (.inl x) else .inr (.inl x)

def output? : (splitSig σ).Out → Option σ.Out
  | .inl (.inl out) | .inr (.inl out) => some out
  | .inl (.inr _) | .inr (.inr _) => none

def msgOf : (x : σ.Id ⊕ σ.Id) → (splitSig σ).Msg x → σ.Msg (actorOf x)
  | .inl _, msg => msg
  | .inr _, msg => msg

end Split

/-- A message in flight between copies, as a message between the actors they stand for. -/
def Envelope.merged (e : Envelope (splitSig σ)) : Envelope σ :=
  ⟨e.src.map Split.actorOf, Split.actorOf e.dst, Split.msgOf (σ := σ) e.dst e.msg⟩

/-- Whether a message travels between copies on the shards that host them. -/
def Envelope.atHome (hosts : σ.Id → Bool) (e : Envelope (splitSig σ)) : Bool :=
  Split.atHome hosts e.dst && e.src.all (Split.atHome hosts)

/-- The event of `sys` that an event of the split is. A parcel is not an input or an output of
`sys`, so a parcel from outside or handed to the outside is no event of `sys`. -/
def Event.merged? : Event (splitSig σ) → Option (Event σ)
  | .input (.inl (.inl x)) | .input (.inr (.inl x)) => some (.input x)
  | .input (.inl (.inr _)) | .input (.inr (.inr _)) => none
  | .deliver e => some (.deliver e.merged)
  | .duplicate e => some (.duplicate e.merged)
  | .drop e => some (.drop e.merged)
  | .timeout x msg => some (.timeout (Split.actorOf x) (Split.msgOf (σ := σ) x msg))
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
  net : ∀ e ∈ c.net, e.atHome hosts = true
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

public section

namespace Lanes

variable {σ : Signature} {sys : System σ} {hosts : σ.Id → Bool} {env : EnvModel σ}

private theorem map_erase_of_inj {α β : Type} [DecidableEq α] [DecidableEq β] {f : α → β}
    {l : List α} {a : α} (inj : ∀ x ∈ l, f x = f a → x = a) :
    (l.erase a).map f = (l.map f).erase (f a) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    have ih := ih fun y hy => inj y (List.mem_cons_of_mem _ hy)
    by_cases hx : x = a
    · subst hx
      simp
    · have hfx : f x ≠ f a := fun h => hx (inj x List.mem_cons_self h)
      simp [hx, hfx, ih]

private theorem flatMap_singletons {α β γ : Type} (f : α → β) (g : β → γ) (l : List α) :
    (l.flatMap fun a => [f a]).flatMap (fun b => [g b]) = l.map fun a => g (f a) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, ih]

private theorem mem_of_mem_erase {α : Type} [DecidableEq α] {l : List α} {a x : α}
    (h : x ∈ l.erase a) : x ∈ l :=
  List.mem_of_mem_erase h

private theorem find?_congr {α : Type} {p q : α → Bool} {l : List α} (h : ∀ x ∈ l, p x = q x) :
    l.find? p = l.find? q := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.find?_cons, h x List.mem_cons_self]
    rw [ih fun y hy => h y (List.mem_cons_of_mem _ hy)]

private theorem filterMap_erase_perm {α β : Type} [DecidableEq α] [DecidableEq β]
    {f : α → Option β} {l : List α} {a : α} {b : β} (ha : a ∈ l) (hb : f a = some b) :
    ((l.filterMap f).erase b).Perm ((l.erase a).filterMap f) := by
  have h := ((List.perm_cons_erase ha).filterMap f).erase b
  rwa [List.filterMap_cons_some hb, List.erase_cons_head] at h

private theorem pick_update_inl {γ : σ.Id ⊕ σ.Id → Type} {β : σ.Id → Type}
    (l : ∀ i, γ (.inl i) → β i) (r : ∀ i, γ (.inr i) → β i) (f : (x : σ.Id ⊕ σ.Id) → γ x)
    {i : σ.Id} (h : hosts i = true) (v : γ (.inl i)) :
    (fun k => if hosts k then l k (update f (.inl i) v (.inl k))
      else r k (update f (.inl i) v (.inr k)))
      = update (fun k => if hosts k then l k (f (.inl k)) else r k (f (.inr k))) i (l i v) := by
  funext k
  by_cases hk : k = i
  · subst hk
    simp [h]
  · simp [update, hk]

private theorem pick_update_inr {γ : σ.Id ⊕ σ.Id → Type} {β : σ.Id → Type}
    (l : ∀ i, γ (.inl i) → β i) (r : ∀ i, γ (.inr i) → β i) (f : (x : σ.Id ⊕ σ.Id) → γ x)
    {i : σ.Id} (h : hosts i = false) (v : γ (.inr i)) :
    (fun k => if hosts k then l k (update f (.inr i) v (.inl k))
      else r k (update f (.inr i) v (.inr k)))
      = update (fun k => if hosts k then l k (f (.inl k)) else r k (f (.inr k))) i (r i v) := by
  funext k
  by_cases hk : k = i
  · subst hk
    simp [h]
  · simp [update, hk]

namespace Split

section

variable {ι : Type} {hosts : ι → Bool}

@[simp] theorem actorOf_inl (i : ι) : actorOf (.inl i : ι ⊕ ι) = i := rfl

@[simp] theorem actorOf_inr (i : ι) : actorOf (.inr i : ι ⊕ ι) = i := rfl

@[simp] theorem atHome_inl (hosts : ι → Bool) (i : ι) : atHome hosts (.inl i) = hosts i := rfl

@[simp] theorem atHome_inr (hosts : ι → Bool) (i : ι) : atHome hosts (.inr i) = !hosts i := rfl

theorem atHome_home (hosts : ι → Bool) (i : ι) : atHome hosts (home hosts i) = true := by
  unfold home
  split <;> simp [*]

@[simp] theorem actorOf_home (hosts : ι → Bool) (i : ι) : actorOf (home hosts i) = i := by
  unfold home
  split <;> rfl

theorem home_actorOf {x : ι ⊕ ι} (h : atHome hosts x = true) : home hosts (actorOf x) = x := by
  cases x <;> simp_all [home]

/-- Two copies on the shards that host them are copies of different actors. -/
theorem eq_of_actorOf {x y : ι ⊕ ι} (hx : atHome hosts x = true) (hy : atHome hosts y = true)
    (h : actorOf x = actorOf y) : x = y := by
  rw [← home_actorOf hx, ← home_actorOf hy, h]

end

private def stateOf : (x : σ.Id ⊕ σ.Id) → (sys.split hosts).State x → sys.State (actorOf x)
  | .inl _, s => s
  | .inr _, s => s

/-- An effect of an actor, as its copy on the shard that hosts it performs it. -/
private def effect (sys : System σ) (hosts : σ.Id → Bool) :
    (x : σ.Id ⊕ σ.Id) → Effect σ (actorOf x) → Effect (splitSig σ) x
  | .inl _, eff => (shardWiring σ).left (sys.shard fun k => !hosts k) (shardEffect hosts eff)
  | .inr _, eff =>
    (shardWiring σ).right (sys.shard hosts) (shardEffect (fun k => !hosts k) eff)

private theorem effect_isStop (x : σ.Id ⊕ σ.Id) (eff : Effect σ (actorOf x)) :
    (effect sys hosts x eff).isStop = eff.isStop := by
  rcases x with i | i <;> cases eff with
  | send to msg =>
    cases h : hosts to <;>
      simp [effect, shardEffect, Wiring.left, Wiring.right, shardWiring, Effect.isStop, h]
  | _ => simp [effect, shardEffect, Wiring.left, Wiring.right, shardWiring, Effect.isStop]

end Split

namespace Envelope

private theorem atHome_dst {e : Envelope (splitSig σ)} (h : e.atHome hosts = true) :
    Split.atHome hosts e.dst = true := by
  simp only [atHome, Bool.and_eq_true] at h
  exact h.1

private theorem merged_inj {e e' : Envelope (splitSig σ)} (he : e.atHome hosts = true)
    (he' : e'.atHome hosts = true) (h : e.merged = e'.merged) : e = e' := by
  obtain ⟨src, dst, msg⟩ := e
  obtain ⟨src', dst', msg'⟩ := e'
  simp only [atHome, Bool.and_eq_true] at he he'
  simp only [merged, Envelope.mk.injEq] at h
  obtain ⟨hsrc, hdst, hmsg⟩ := h
  obtain rfl := Split.eq_of_actorOf he.1 he'.1 hdst
  have hsrc : src = src' := by
    rcases src with _ | s <;> rcases src' with _ | s' <;> simp only [Option.map_none,
      Option.map_some, reduceCtorEq, Option.some.injEq] at hsrc ⊢
    exact Split.eq_of_actorOf (by simpa using he.2) (by simpa using he'.2) hsrc
  subst hsrc
  have hmsg : msg = msg' := by
    rcases dst with i | i <;> exact eq_of_heq hmsg
  rw [hmsg]

private theorem merged_sameLink {e x : Envelope (splitSig σ)} (he : e.atHome hosts = true)
    (hx : x.atHome hosts = true) : e.merged.sameLink x.merged = e.sameLink x := by
  simp only [atHome, Bool.and_eq_true] at he hx
  simp only [sameLink, merged]
  congr 1
  · apply decide_eq_decide.mpr
    constructor
    · intro h
      rcases hs : e.src with _ | s <;> rcases hs' : x.src with _ | s' <;>
        simp only [hs, hs', Option.map_none, Option.map_some, reduceCtorEq,
          Option.some.injEq] at h ⊢
      exact Split.eq_of_actorOf (by simpa [hs] using he.2) (by simpa [hs'] using hx.2) h
    · exact fun h => h ▸ rfl
  · exact decide_eq_decide.mpr ⟨Split.eq_of_actorOf he.1 hx.1, fun h => h ▸ rfl⟩

end Envelope

namespace Split

private theorem effect_send (x : σ.Id ⊕ σ.Id) (to : σ.Id) (msg : σ.Msg to) :
    effect sys hosts x (.send to msg)
      = if hosts to then .send (.inl to) msg else .send (.inr to) msg := by
  rcases x with i | i <;> cases h : hosts to <;>
    simp [effect, shardEffect, Wiring.left, Wiring.right, shardWiring, h]

end Split

namespace SysState

variable {c : SysState (sys.split hosts)} {x : σ.Id ⊕ σ.Id}

private theorem merged_state (c : SysState (sys.split hosts)) (hx : Split.atHome hosts x = true) :
    c.merged.state (Split.actorOf x) = Split.stateOf x (c.state x) := by
  rcases x with i | i <;> simp_all [merged, Split.stateOf]

private theorem merged_up (c : SysState (sys.split hosts)) (hx : Split.atHome hosts x = true) :
    c.merged.up (Split.actorOf x) = c.up x := by
  rcases x with i | i <;> simp_all [merged]

private theorem merged_setState (c : SysState (sys.split hosts))
    (hx : Split.atHome hosts x = true) (v : (sys.split hosts).State x) :
    ({ c with state := update c.state x v } : SysState (sys.split hosts)).merged
      = { c.merged with state := update c.merged.state (Split.actorOf x) (Split.stateOf x v) } := by
  rcases x with i | i
  · exact SysState.ext' (pick_update_inl (hosts := hosts) (γ := (sys.split hosts).State) (β := sys.State)
      (fun _ s => s) (fun _ s => s) c.state (by simpa using hx) v)
      rfl rfl rfl rfl
  · exact SysState.ext' (pick_update_inr (hosts := hosts) (γ := (sys.split hosts).State) (β := sys.State)
      (fun _ s => s) (fun _ s => s) c.state (by simpa using hx) v)
      rfl rfl rfl rfl

private theorem merged_setUp (c : SysState (sys.split hosts)) (hx : Split.atHome hosts x = true)
    (b : Bool) :
    ({ c with up := update c.up x b } : SysState (sys.split hosts)).merged
      = { c.merged with up := update c.merged.up (Split.actorOf x) b } := by
  rcases x with i | i
  · exact SysState.ext' rfl
      (pick_update_inl (hosts := hosts) (γ := fun _ => Bool) (β := fun _ => Bool)
        (fun _ s => s) (fun _ s => s) c.up (by simpa using hx) b) rfl rfl rfl
  · exact SysState.ext' rfl
      (pick_update_inr (hosts := hosts) (γ := fun _ => Bool) (β := fun _ => Bool)
        (fun _ s => s) (fun _ s => s) c.up (by simpa using hx) b) rfl rfl rfl

private theorem merged_retime_inl (c : SysState (sys.split hosts)) {i : σ.Id}
    (h : hosts i = true) (f : List (σ.Msg i) → List (σ.Msg i)) :
    ({ c with timers := update c.timers (.inl i) (f (c.timers (.inl i))) } :
        SysState (sys.split hosts)).merged
      = { c.merged with timers := update c.merged.timers i (f (c.merged.timers i)) } := by
  have ht : c.merged.timers i = c.timers (.inl i) := by simp [merged, h]
  rw [ht]
  exact SysState.ext' rfl rfl rfl (pick_update_inl (hosts := hosts)
    (γ := fun x => List ((splitSig σ).Msg x)) (β := fun i => List (σ.Msg i))
    (fun _ s => s) (fun _ s => s) c.timers h _) rfl

private theorem merged_retime_inr (c : SysState (sys.split hosts)) {i : σ.Id}
    (h : hosts i = false) (f : List (σ.Msg i) → List (σ.Msg i)) :
    ({ c with timers := update c.timers (.inr i) (f (c.timers (.inr i))) } :
        SysState (sys.split hosts)).merged
      = { c.merged with timers := update c.merged.timers i (f (c.merged.timers i)) } := by
  have ht : c.merged.timers i = c.timers (.inr i) := by simp [merged, h]
  rw [ht]
  exact SysState.ext' rfl rfl rfl (pick_update_inr (hosts := hosts)
    (γ := fun x => List ((splitSig σ).Msg x)) (β := fun i => List (σ.Msg i))
    (fun _ s => s) (fun _ s => s) c.timers h _) rfl

private theorem perform_send (hc : c.AtHome) (hx : Split.atHome hosts x = true)
    {y : σ.Id ⊕ σ.Id} (hy : Split.atHome hosts y = true) (msg : (splitSig σ).Msg y) :
    (c.perform x (.send y msg)).AtHome ∧
      (c.perform x (.send y msg)).merged
        = c.merged.perform (Split.actorOf x) (.send (Split.actorOf y) (Split.msgOf y msg)) := by
  refine ⟨⟨fun e he => ?_, hc.down, hc.outbox⟩, ?_⟩
  · rcases List.mem_append.mp he with he | he
    · exact hc.net e he
    · obtain rfl := List.mem_singleton.mp he
      simp only [Envelope.atHome, Option.all_some, Bool.and_eq_true]
      exact ⟨hy, hx⟩
  · simp [perform, merged, Envelope.merged]

private theorem perform_merged (hc : c.AtHome) (hx : Split.atHome hosts x = true)
    (eff : Effect σ (Split.actorOf x)) :
    (c.perform x (Split.effect sys hosts x eff)).AtHome ∧
      (c.perform x (Split.effect sys hosts x eff)).merged
        = c.merged.perform (Split.actorOf x) eff := by
  cases eff with
  | send to msg =>
    rw [Split.effect_send]
    split
    · next h => exact perform_send hc hx (y := .inl to) (by simpa using h) msg
    · next h => exact perform_send hc hx (y := .inr to) (by simpa using h) msg
  | emit out =>
    rcases x with i | i
    · refine ⟨⟨hc.net, hc.down, fun o ho => ?_⟩, ?_⟩
      · rcases List.mem_append.mp ho with ho | ho
        · exact hc.outbox o ho
        · obtain rfl := List.mem_singleton.mp ho
          rfl
      · simp [Split.effect, shardEffect, Wiring.left, shardWiring, perform, merged, Split.output?]
    · refine ⟨⟨hc.net, hc.down, fun o ho => ?_⟩, ?_⟩
      · rcases List.mem_append.mp ho with ho | ho
        · exact hc.outbox o ho
        · obtain rfl := List.mem_singleton.mp ho
          rfl
      · simp [Split.effect, shardEffect, Wiring.right, shardWiring, perform, merged, Split.output?]
  | after delay_ms msg =>
    rcases x with i | i
    · exact ⟨⟨hc.net, hc.down, hc.outbox⟩,
        merged_retime_inl c (by simpa using hx) fun t => if msg ∈ t then t else t ++ [msg]⟩
    · exact ⟨⟨hc.net, hc.down, hc.outbox⟩,
        merged_retime_inr c (by simpa using hx) fun t => if msg ∈ t then t else t ++ [msg]⟩
  | cancel msg =>
    rcases x with i | i
    · exact ⟨⟨hc.net, hc.down, hc.outbox⟩,
        merged_retime_inl c (by simpa using hx) fun t => t.erase msg⟩
    · exact ⟨⟨hc.net, hc.down, hc.outbox⟩,
        merged_retime_inr c (by simpa using hx) fun t => t.erase msg⟩
  | stop => rcases x with i | i <;> exact ⟨hc, rfl⟩

private theorem performAll_merged (hc : c.AtHome) (hx : Split.atHome hosts x = true)
    (effs : List (Effect σ (Split.actorOf x))) :
    (c.performAll x (effs.map (Split.effect sys hosts x))).AtHome ∧
      (c.performAll x (effs.map (Split.effect sys hosts x))).merged
        = c.merged.performAll (Split.actorOf x) effs := by
  induction effs generalizing c with
  | nil => exact ⟨hc, rfl⟩
  | cons eff effs ih =>
    obtain ⟨h₁, h₂⟩ := perform_merged hc hx eff
    obtain ⟨h₃, h₄⟩ := ih h₁
    exact ⟨h₃, by rw [List.map_cons, performAll_cons, h₄, h₂, performAll_cons]⟩

private theorem down_merged (hc : c.AtHome) (hx : Split.atHome hosts x = true) :
    (c.down (env.split hosts) x).AtHome ∧
      (c.down (env.split hosts) x).merged = c.merged.down env (Split.actorOf x) := by
  refine ⟨⟨fun e he => hc.net e (List.mem_filter.mp he).1, fun y hy => ?_, hc.outbox⟩, ?_⟩
  · by_cases hyx : y = x
    · subst hyx
      simp [down]
    · simpa [down, hyx] using hc.down y hy
  · have hnet : (c.net.filter fun e => decide (e.dst ≠ x)
          || ((env.split hosts).link e.src e.dst).lossy).map Envelope.merged
        = (c.net.map Envelope.merged).filter fun e => decide (e.dst ≠ Split.actorOf x)
          || (env.link e.src e.dst).lossy := by
      rw [List.filter_map]
      congr 1
      refine List.filter_congr fun e he => ?_
      have hne : e.dst ≠ x ↔ Split.actorOf e.dst ≠ Split.actorOf x :=
        not_congr ⟨fun h => h ▸ rfl, Split.eq_of_actorOf (Envelope.atHome_dst (hc.net e he)) hx⟩
      simp only [Function.comp, Envelope.merged, EnvModel.split]
      congr 1
      exact decide_eq_decide.mpr hne
    have hup := congrArg SysState.up (merged_setUp c hx false)
    rcases x with i | i
    · have htimers : ({ c with timers := update c.timers (.inl i) [] } :
          SysState (sys.split hosts)).merged.timers = update c.merged.timers i [] :=
        congrArg SysState.timers (merged_retime_inl c (by simpa using hx) fun _ => [])
      exact SysState.ext' rfl hup hnet htimers rfl
    · have htimers : ({ c with timers := update c.timers (.inr i) [] } :
          SysState (sys.split hosts)).merged.timers = update c.merged.timers i [] :=
        congrArg SysState.timers (merged_retime_inr c (by simpa using hx) fun _ => [])
      exact SysState.ext' rfl hup hnet htimers rfl

private theorem settle_merged (hc : c.AtHome) (hx : Split.atHome hosts x = true)
    (v : (sys.split hosts).State x) (effs : List (Effect σ (Split.actorOf x))) :
    (c.settle (env.split hosts) x (v, effs.map (Split.effect sys hosts x))).AtHome ∧
      (c.settle (env.split hosts) x (v, effs.map (Split.effect sys hosts x))).merged
        = c.merged.settle env (Split.actorOf x) (Split.stateOf x v, effs) := by
  have hstop : (effs.map (Split.effect sys hosts x)).any Effect.isStop
      = effs.any Effect.isStop := by
    rw [List.any_map]
    congr 1
    funext eff
    exact Split.effect_isStop x eff
  obtain ⟨h₁, h₂⟩ := performAll_merged
    (c := { c with state := update c.state x v }) ⟨hc.net, hc.down, hc.outbox⟩ hx effs
  rw [merged_setState c hx v] at h₂
  simp only [settle, hstop]
  split
  · obtain ⟨h₃, h₄⟩ := down_merged (env := env) h₁ hx
    exact ⟨h₃, by rw [h₄, h₂]⟩
  · exact ⟨h₁, h₂⟩

end SysState

namespace Split

private theorem actor_inl {i : σ.Id} (h : hosts i = true) :
    (sys.split hosts).actor (.inl i)
      = ((sys.actor i).mapEff fun eff => [shardEffect hosts eff]).mapEff fun eff =>
          [(shardWiring σ).left (sys.shard fun k => !hosts k) eff] := by
  show Actor.mapEff _ (if hosts i then _ else _) = _
  simp only [h, ↓reduceIte]

private theorem actor_inr {i : σ.Id} (h : hosts i = false) :
    (sys.split hosts).actor (.inr i)
      = ((sys.actor i).mapEff fun eff => [shardEffect (fun k => !hosts k) eff]).mapEff fun eff =>
          [(shardWiring σ).right (sys.shard hosts) eff] := by
  show Actor.mapEff _ (if (!hosts i) = true then _ else _) = _
  simp only [h, Bool.not_false, ↓reduceIte]

private theorem actor_step {x : σ.Id ⊕ σ.Id} (hx : atHome hosts x = true)
    (s : (sys.split hosts).State x) (msg : (splitSig σ).Msg x) :
    stateOf x (((sys.split hosts).actor x).step s msg).1
        = ((sys.actor (actorOf x)).step (stateOf x s) (msgOf x msg)).1 ∧
      (((sys.split hosts).actor x).step s msg).2
        = ((sys.actor (actorOf x)).step (stateOf x s) (msgOf x msg)).2.map (effect sys hosts x) := by
  rcases x with i | i
  · rw [actor_inl (by simpa using hx)]
    exact ⟨rfl, flatMap_singletons _ _ _⟩
  · rw [actor_inr (by simpa using hx)]
    exact ⟨rfl, flatMap_singletons _ _ _⟩

private theorem actor_recover {x : σ.Id ⊕ σ.Id} (hx : atHome hosts x = true)
    (s : (sys.split hosts).State x) :
    stateOf x (((sys.split hosts).actor x).recover s).1
        = ((sys.actor (actorOf x)).recover (stateOf x s)).1 ∧
      (((sys.split hosts).actor x).recover s).2
        = ((sys.actor (actorOf x)).recover (stateOf x s)).2.map (effect sys hosts x) := by
  rcases x with i | i
  · rw [actor_inl (by simpa using hx)]
    exact ⟨rfl, flatMap_singletons _ _ _⟩
  · rw [actor_inr (by simpa using hx)]
    exact ⟨rfl, flatMap_singletons _ _ _⟩

end Split

namespace SysState

variable {c : SysState (sys.split hosts)} {x : σ.Id ⊕ σ.Id}

private theorem handle_merged (hc : c.AtHome) (hx : Split.atHome hosts x = true)
    (msg : (splitSig σ).Msg x) :
    (c.handle (env.split hosts) x msg).AtHome ∧
      (c.handle (env.split hosts) x msg).merged
        = c.merged.handle env (Split.actorOf x) (Split.msgOf x msg) := by
  obtain ⟨hstate, heffs⟩ := Split.actor_step hx (c.state x) msg
  have h := settle_merged (env := env) hc hx (((sys.split hosts).actor x).step (c.state x) msg).1
    ((sys.actor (Split.actorOf x)).step (Split.stateOf x (c.state x)) (Split.msgOf x msg)).2
  rw [← heffs, hstate, ← merged_state c hx] at h
  exact h

private theorem startActor_merged (hc : c.AtHome) (hx : Split.atHome hosts x = true) :
    (c.startActor (env.split hosts) x).AtHome ∧
      (c.startActor (env.split hosts) x).merged = c.merged.startActor env (Split.actorOf x) := by
  obtain ⟨hstate, heffs⟩ := Split.actor_recover hx (c.state x)
  have hup : ({ c with up := update c.up x true } : SysState (sys.split hosts)).AtHome := by
    refine ⟨hc.net, fun y hy => ?_, hc.outbox⟩
    have hyx : y ≠ x := fun h => by
      rw [h, hx] at hy
      cases hy
    simpa [hyx] using hc.down y hy
  have h := settle_merged (env := env) hup hx (((sys.split hosts).actor x).recover (c.state x)).1
    ((sys.actor (Split.actorOf x)).recover (Split.stateOf x (c.state x))).2
  rw [← heffs, hstate, ← merged_state c hx, merged_setUp c hx true] at h
  exact h

private theorem merged_timers_inl (c : SysState (sys.split hosts)) {i : σ.Id}
    (h : hosts i = true) : c.merged.timers i = c.timers (.inl i) := by
  simp [merged, h]

private theorem merged_timers_inr (c : SysState (sys.split hosts)) {i : σ.Id}
    (h : hosts i = false) : c.merged.timers i = c.timers (.inr i) := by
  simp [merged, h]

private theorem merged_erase (hc : c.AtHome) {e : Envelope (splitSig σ)} (he : e ∈ c.net) :
    ({ c with net := c.net.erase e } : SysState (sys.split hosts)).AtHome ∧
      ({ c with net := c.net.erase e } : SysState (sys.split hosts)).merged
        = { c.merged with net := c.merged.net.erase e.merged } :=
  ⟨⟨fun x hx => hc.net x (List.mem_of_mem_erase hx), hc.down, hc.outbox⟩,
    SysState.ext' rfl rfl
      (map_erase_of_inj fun x hx h => Envelope.merged_inj (hc.net x hx) (hc.net e he) h) rfl rfl⟩

private theorem deliverable_merged (hc : c.AtHome) {e : Envelope (splitSig σ)}
    (h : c.deliverable (env.split hosts) e = true) :
    c.merged.deliverable env e.merged = true := by
  have he := mem_of_deliverable h
  have hlink : (env.split hosts).link e.src e.dst = env.link e.merged.src e.merged.dst := rfl
  simp only [deliverable, hlink] at h ⊢
  split at h
  · next hord =>
    have hfind : c.net.find? e.sameLink = some e := by simpa using h
    have hsame : ∀ x ∈ c.net, (e.merged.sameLink ∘ Envelope.merged) x = e.sameLink x := fun x hx =>
      Envelope.merged_sameLink (hc.net e he) (hc.net x hx)
    simp [hord, merged, List.find?_map, find?_congr hsame, hfind]
  · next hord =>
    simp only [hord]
    simpa [merged] using List.mem_map_of_mem (f := Envelope.merged) he

private theorem sameBut {m m' : SysState sys} (h : m' = m) :
    m.outbox.Perm m'.outbox ∧ { m with outbox := m'.outbox } = m' := by
  subst h
  exact ⟨.refl _, rfl⟩

private theorem up_atHome (hc : c.AtHome) (hup : c.up x = true) : Split.atHome hosts x = true := by
  cases h : Split.atHome hosts x with
  | true => rfl
  | false => simp [hc.down x h] at hup

end SysState

/-- One event of the split is one event of `sys`: it leads `c.merged` to `c'.merged`, but for
the order of the outputs waiting when the event hands one over. Outputs of the two shards that
are equal are told apart in the split and not in `sys`. -/
theorem SysState.AtHome.step {c c' : SysState (sys.split hosts)} {ev : Event (splitSig σ)}
    (hc : c.AtHome) (hev : ev.routed sys hosts = true)
    (hstep : c.step (env.split hosts) ev = some c') :
    c'.AtHome ∧ ∃ ev' m, ev.merged? = some ev' ∧ c.merged.step env ev' = some m ∧
      m.outbox.Perm c'.merged.outbox ∧ { m with outbox := c'.merged.outbox } = c'.merged := by
  open SysState in
  cases ev with
  | input y =>
    obtain rfl := step_input.mp hstep
    rcases y with (x | parcel) | (x | parcel)
    · refine ⟨⟨fun e he => ?_, hc.down, hc.outbox⟩, .input x, _, rfl, step_input.mpr rfl, sameBut ?_⟩
      · rcases List.mem_append.mp he with he | he
        · exact hc.net e he
        · obtain rfl := List.mem_singleton.mp he
          simpa [Envelope.atHome, Event.routed] using hev
      · simp [merged, Envelope.merged, Split.msgOf]
    · exact absurd hev (by simp [Event.routed])
    · refine ⟨⟨fun e he => ?_, hc.down, hc.outbox⟩, .input x, _, rfl, step_input.mpr rfl, sameBut ?_⟩
      · rcases List.mem_append.mp he with he | he
        · exact hc.net e he
        · obtain rfl := List.mem_singleton.mp he
          simpa [Envelope.atHome, Event.routed] using hev
      · simp [merged, Envelope.merged, Split.msgOf]
    · exact absurd hev (by simp [Event.routed])
  | deliver e =>
    obtain ⟨hup, hdel, rfl⟩ := step_deliver.mp hstep
    have hx := up_atHome hc hup
    obtain ⟨h₁, h₂⟩ := merged_erase hc (mem_of_deliverable hdel)
    obtain ⟨h₃, h₄⟩ := handle_merged (env := env) h₁ hx e.msg
    rw [h₂] at h₄
    exact ⟨h₃, .deliver e.merged, _, rfl,
      step_deliver.mpr ⟨(merged_up c hx).trans hup, deliverable_merged hc hdel, rfl⟩, sameBut h₄⟩
  | duplicate e =>
    obtain ⟨hup, hdup, hdel, rfl⟩ := step_duplicate.mp hstep
    have hx := up_atHome hc hup
    obtain ⟨h₃, h₄⟩ := handle_merged (env := env) hc hx e.msg
    exact ⟨h₃, .duplicate e.merged, _, rfl,
      step_duplicate.mpr ⟨(merged_up c hx).trans hup, hdup, deliverable_merged hc hdel, rfl⟩,
      sameBut h₄⟩
  | drop e =>
    obtain ⟨hlossy, hmem, rfl⟩ := step_drop.mp hstep
    obtain ⟨h₁, h₂⟩ := merged_erase hc hmem
    exact ⟨h₁, .drop e.merged, _, rfl,
      step_drop.mpr ⟨hlossy, List.mem_map_of_mem hmem, rfl⟩, sameBut h₂⟩
  | timeout x msg =>
    obtain ⟨hup, hmem, rfl⟩ := step_timeout.mp hstep
    have hx := up_atHome hc hup
    obtain ⟨h₃, h₄⟩ := handle_merged (env := env)
      (c := { c with timers := update c.timers x ((c.timers x).erase msg) })
      ⟨hc.net, hc.down, hc.outbox⟩ hx msg
    refine ⟨h₃, .timeout (Split.actorOf x) (Split.msgOf (σ := σ) x msg), _, rfl, ?_, sameBut rfl⟩
    rcases x with i | i
    · have h : hosts i = true := by simpa using hx
      rw [merged_retime_inl c h fun t => t.erase msg] at h₄
      exact step_timeout.mpr ⟨(merged_up c hx).trans hup, merged_timers_inl c h ▸ hmem, h₄⟩
    · have h : hosts i = false := by simpa using hx
      rw [merged_retime_inr c h fun t => t.erase msg] at h₄
      exact step_timeout.mpr ⟨(merged_up c hx).trans hup, merged_timers_inr c h ▸ hmem, h₄⟩
  | output out =>
    obtain ⟨hmem, rfl⟩ := step_output.mp hstep
    obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp (hc.outbox out hmem)
    exact ⟨⟨hc.net, hc.down, fun x hx => hc.outbox x (mem_of_mem_erase hx)⟩, .output o, _,
      by simp [Event.merged?, ho],
      step_output.mpr ⟨List.mem_filterMap.mpr ⟨out, hmem, ho⟩, rfl⟩,
      filterMap_erase_perm hmem ho, rfl⟩
  | crash x =>
    obtain ⟨hup, hcrash, rfl⟩ := step_crash.mp hstep
    have hx := up_atHome hc hup
    obtain ⟨h₁, h₂⟩ := down_merged (env := env) hc hx
    exact ⟨h₁, .crash (Split.actorOf x), _, rfl,
      step_crash.mpr ⟨(merged_up c hx).trans hup, by simpa [EnvModel.split, hx] using hcrash, rfl⟩,
      sameBut h₂⟩
  | start x =>
    obtain ⟨hup, hmail, rfl⟩ := step_start.mp hstep
    have hx : Split.atHome hosts x = true := by
      rcases hmail with hmail | hrestarts
      · obtain ⟨e, he, rfl⟩ : ∃ e ∈ c.net, e.dst = x := by simpa [hasMail] using hmail
        exact Envelope.atHome_dst (hc.net e he)
      · simp only [EnvModel.split, Bool.and_eq_true] at hrestarts
        exact hrestarts.1
    obtain ⟨h₁, h₂⟩ := startActor_merged (env := env) hc hx
    refine ⟨h₁, .start (Split.actorOf x), _, rfl,
      step_start.mpr ⟨(merged_up c hx).trans hup, hmail.imp (fun hmail => ?_) (fun h => ?_), rfl⟩,
      sameBut h₂⟩
    · obtain ⟨e, he, rfl⟩ : ∃ e ∈ c.net, e.dst = x := by simpa [hasMail] using hmail
      simpa [hasMail, merged] using ⟨e, he, rfl⟩
    · simpa [EnvModel.split, hx] using h

end Lanes
