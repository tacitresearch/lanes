/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Actors.World
public import Lanes.Data.Enum

/-!
# Looking at systems: printing, hashing and enumerating

The simulator, the model checker and the trace tools need to list a system's actors and to
print, hash and compare its data. `Signature.Inspect` and `System.Inspect` collect those
requirements, so that tools take one instance argument instead of a dozen.

For a system whose identities and messages derive `Repr` and `Hashable`, both instances are `{}`.

## Main definitions

- `Signature.Inspect σ`, `System.Inspect sys`: the requirements.
- `SysState.candidates`, `SysState.successors`: the events enabled in a state.
- `SysState.compact`: the same state with its per-actor functions rebuilt as tables.
- `SysState.equiv`, `SysState.hash`: equality and hashing that respect the link model.
-/

@[expose] public section

namespace Lanes

/-- A signature whose actors can be listed and whose data can be printed and hashed. -/
class Signature.Inspect (σ : Signature) where
  /-- Every actor identity. Checking runs on instances with finitely many actors. -/
  [enumId : Enum σ.Id]
  /-- Identities can be printed. -/
  [reprId : Repr σ.Id]
  /-- Identities can be hashed. -/
  [hashId : Hashable σ.Id]
  /-- Messages can be printed. -/
  [reprMsg : ∀ i, Repr (σ.Msg i)]
  /-- Messages can be hashed. -/
  [hashMsg : ∀ i, Hashable (σ.Msg i)]
  /-- Inputs can be printed. -/
  [reprIn : Repr σ.In]
  /-- Outputs can be printed. -/
  [reprOut : Repr σ.Out]
  /-- Outputs can be hashed. -/
  [hashOut : Hashable σ.Out]

attribute [instance_reducible, instance] Signature.Inspect.enumId Signature.Inspect.reprId Signature.Inspect.hashId
  Signature.Inspect.reprMsg Signature.Inspect.hashMsg Signature.Inspect.reprIn
  Signature.Inspect.reprOut Signature.Inspect.hashOut

/-- A system whose actor states can be compared, printed and hashed. -/
class System.Inspect {σ : Signature} (sys : System σ) where
  /-- Actor states can be compared. -/
  [beqState : ∀ i, BEq (sys.State i)]
  /-- Actor states can be printed. -/
  [reprState : ∀ i, Repr (sys.State i)]
  /-- Actor states can be hashed. -/
  [hashState : ∀ i, Hashable (sys.State i)]

attribute [instance_reducible, instance] System.Inspect.beqState System.Inspect.reprState System.Inspect.hashState

variable {σ : Signature}

section Show

variable [σ.Inspect]

instance : Hashable (Envelope σ) where
  hash e := mixHash (hash e.src) (mixHash (hash e.dst) (hash e.msg))

/-- Print an envelope as `src → dst: msg`. -/
def Envelope.render (e : Envelope σ) : String :=
  let src := match e.src with
    | some i => toString (repr i)
    | none => "outside"
  s!"{src} → {repr e.dst}: {repr e.msg}"

/-- Print an event on one line. -/
def Event.render : Event σ → String
  | .input x => s!"input {repr x}"
  | .deliver e => s!"deliver {e.render}"
  | .duplicate e => s!"duplicate {e.render}"
  | .drop e => s!"drop {e.render}"
  | .timeout i msg => s!"timeout {repr i}: {repr msg}"
  | .output out => s!"output {repr out}"
  | .crash i => s!"crash {repr i}"
  | .start i => s!"start {repr i}"

/-- The kind of an event, used to group events in coverage reports. -/
def Event.kind : Event σ → String
  | .input _ => "input"
  | .deliver _ => "deliver"
  | .duplicate _ => "duplicate"
  | .drop _ => "drop"
  | .timeout .. => "timeout"
  | .output _ => "output"
  | .crash _ => "crash"
  | .start _ => "start"

/-- Every event kind. -/
def Event.kinds : List String :=
  ["input", "deliver", "duplicate", "drop", "timeout", "output", "crash", "start"]

end Show

namespace SysState

variable {sys : System σ}

/-- The events that might be enabled in `c`, other than inputs. Inputs are the environment's
choice and come from a `Driver`. -/
def candidates [Enum σ.Id] (c : SysState sys) : List (Event σ) :=
  let envelopes := c.net.eraseDups
  let ids := Enum.all (α := σ.Id)
  envelopes.map .deliver ++ envelopes.map .duplicate ++ envelopes.map .drop
    ++ ids.flatMap (fun i => (c.timers i).map (.timeout i))
    ++ c.outbox.eraseDups.map .output
    ++ ids.map .crash ++ ids.map .start

/-- Every enabled event other than an input, with the state it leads to. -/
def successors [Enum σ.Id] (env : EnvModel σ) (c : SysState sys) :
    List (Event σ × SysState sys) :=
  c.candidates.filterMap fun ev => (c.step env ev).map (ev, ·)

/-- Every listed successor is a step of the system: tools that explore with `successors` only
visit states the semantics allows. -/
theorem step_of_mem_successors [Enum σ.Id] {env : EnvModel σ} {c c' : SysState sys}
    {ev : Event σ} (h : (ev, c') ∈ c.successors env) : c.step env ev = some c' := by
  simp only [successors, List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨ev', _, c'', hstep, rfl, rfl⟩ := h
  exact hstep

/--
The same state, with its per-actor functions rebuilt as tables. A long run otherwise builds a
chain of function updates as deep as the run is long.
-/
def compact [Enum σ.Id] (c : SysState sys) : SysState sys :=
  { c with state := Enum.tabulate c.state, up := Enum.tabulate c.up,
           timers := Enum.tabulate c.timers }

@[simp] theorem compact_eq [Enum σ.Id] (c : SysState sys) : c.compact = c := by
  simp [compact]

variable [σ.Inspect] [sys.Inspect]

/--
Whether two message lists are the same traffic under `env`: on an ordered link the messages
must be in the same order, on any other link they must be the same up to order.
-/
def netEquiv (env : EnvModel σ) (a b : List (Envelope σ)) : Bool :=
  a.length == b.length && a.all fun e =>
    let onLinkA := a.filter e.sameLink
    let onLinkB := b.filter e.sameLink
    if (env.link e.src e.dst).ordered then onLinkA == onLinkB else onLinkA.isPerm onLinkB

/-- Whether two states are the same under `env`. Message order only counts where the link model
makes it observable. -/
def equiv (env : EnvModel σ) (a b : SysState sys) : Bool :=
  (Enum.all (α := σ.Id)).all (fun i =>
      a.state i == b.state i && a.up i == b.up i && a.timers i == b.timers i)
    && netEquiv env a.net b.net && a.outbox.isPerm b.outbox

/-- A hash that agrees with `equiv`: it does not depend on the order of messages in flight. -/
def hash (c : SysState sys) : UInt64 :=
  let actors := (Enum.all (α := σ.Id)).foldl (init := 7) fun h i =>
    mixHash h (mixHash (Hashable.hash (c.state i))
      (mixHash (Hashable.hash (c.up i)) (Hashable.hash (c.timers i))))
  let net := c.net.foldl (init := 0) fun h e => h + mixHash 11 (Hashable.hash e)
  let outbox := c.outbox.foldl (init := 0) fun h o => h + mixHash 13 (Hashable.hash o)
  mixHash actors (mixHash net outbox)

/-- Print a state: one line per actor that has started or holds a timer, then the messages in
flight and the pending outputs. -/
def render (c : SysState sys) : String :=
  let actors := (Enum.all (α := σ.Id)).filterMap fun i =>
    let timers := if (c.timers i).isEmpty then "" else s!" timers={repr (c.timers i)}"
    some s!"  {repr i} [{if c.up i then "up" else "down"}] {repr (c.state i)}{timers}"
  let net := c.net.map fun e => s!"  in flight: {e.render}"
  let outbox := c.outbox.map fun o => s!"  pending output: {repr o}"
  "\n".intercalate (actors ++ net ++ outbox)

end SysState

end Lanes
