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
-/

@[expose] public section

namespace Lanes

/-- A system with no inputs or no outputs uses `Empty`, which has nothing to hash. -/
instance (priority := low) : Hashable Empty := ⟨fun x => nomatch x⟩

instance (priority := low) : Repr Empty := ⟨fun x _ => nomatch x⟩

class Signature.Inspect (σ : Signature) where
  [enumId : Enum σ.Id]
  [reprId : Repr σ.Id]
  [hashId : Hashable σ.Id]
  [reprMsg : ∀ i, Repr (σ.Msg i)]
  [hashMsg : ∀ i, Hashable (σ.Msg i)]
  [reprIn : Repr σ.In]
  [hashIn : Hashable σ.In]
  [reprOut : Repr σ.Out]
  [hashOut : Hashable σ.Out]

attribute [instance_reducible, instance] Signature.Inspect.enumId Signature.Inspect.reprId Signature.Inspect.hashId
  Signature.Inspect.reprMsg Signature.Inspect.hashMsg Signature.Inspect.reprIn
  Signature.Inspect.hashIn
  Signature.Inspect.reprOut Signature.Inspect.hashOut

class System.Inspect {σ : Signature} (sys : System σ) where
  [beqState : ∀ i, BEq (sys.State i)]
  [reprState : ∀ i, Repr (sys.State i)]
  [hashState : ∀ i, Hashable (sys.State i)]

attribute [instance_reducible, instance] System.Inspect.beqState System.Inspect.reprState System.Inspect.hashState

variable {σ : Signature}

section Show

variable [σ.Inspect]

instance : Hashable (Envelope σ) where
  hash e := mixHash (hash e.src) (mixHash (hash e.dst) (hash e.msg))

/--
Drop namespace prefixes from printed values: `Examples.Bank.Msg.credit 1` becomes `credit 1`.
Traces are read by people and agents, and the prefixes are noise. Text inside string literals is
kept as it is.
-/
def shortNames (s : String) : String := Id.run do
  let mut out : List Char := []
  let mut word : List Char := []   -- the identifier being read, reversed
  let mut inString := false
  let mut escaped := false
  let flush := fun (out word : List Char) =>
    let w := word.reverse
    match w with
    | c :: _ =>
      if c.isAlpha then (w.splitOn '.').getLastD w |>.reverse |> (· ++ out) else word ++ out
    | [] => out
  for c in s.toList do
    if inString then
      out := c :: out
      if escaped then escaped := false
      else if c == '\\' then escaped := true
      else if c == '"' then inString := false
    else if c.isAlphanum || c == '_' || c == '.' then
      word := c :: word
    else
      out := flush out word
      word := []
      out := c :: out
      if c == '"' then inString := true
  return String.ofList (flush out word).reverse

def brief {α : Type} [Repr α] (a : α) : String :=
  shortNames (toString (repr a))

def Envelope.render (e : Envelope σ) : String :=
  let src := match e.src with
    | some i => brief i
    | none => "outside"
  s!"{src} → {brief e.dst}: {brief e.msg}"

def Event.render : Event σ → String
  | .input x => s!"input {brief x}"
  | .deliver e => s!"deliver {e.render}"
  | .duplicate e => s!"duplicate {e.render}"
  | .drop e => s!"drop {e.render}"
  | .timeout i msg => s!"timeout {brief i}: {brief msg}"
  | .output out => s!"output {brief out}"
  | .crash i => s!"crash {brief i}"
  | .start i => s!"start {brief i}"

def Event.kind : Event σ → String
  | .input _ => "input"
  | .deliver _ => "deliver"
  | .duplicate _ => "duplicate"
  | .drop _ => "drop"
  | .timeout .. => "timeout"
  | .output _ => "output"
  | .crash _ => "crash"
  | .start _ => "start"

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

def successors [Enum σ.Id] (env : EnvModel σ) (c : SysState sys) :
    List (Event σ × SysState sys) :=
  c.candidates.filterMap fun ev => (c.step env ev).map (ev, ·)

/-- Tools that explore with `successors` only visit states the semantics allows. -/
theorem step_of_mem_successors [Enum σ.Id] {env : EnvModel σ} {c c' : SysState sys}
    {ev : Event σ} (h : (ev, c') ∈ c.successors env) : c.step env ev = some c' := by
  simp only [successors, List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨ev', _, c'', hstep, rfl, rfl⟩ := h
  exact hstep

end SysState

/-- One actor of a state: its state, whether it is up and its timers. -/
structure Slot {σ : Signature} (sys : System σ) where
  id : σ.Id
  state : sys.State id
  up : Bool
  timers : List (σ.Msg id)

namespace Slot

variable {sys : System σ}

def of (c : SysState sys) (i : σ.Id) : Slot sys :=
  ⟨i, c.state i, c.up i, c.timers i⟩

def find : (slots : List (Slot sys)) → (i : σ.Id) → i ∈ slots.map (·.id) →
    { s : Slot sys // s.id = i }
  | [], _, h => nomatch h
  | s :: slots, i, h =>
    if hi : s.id = i then ⟨s, hi⟩
    else find slots i (by
      cases h with
      | head => exact absurd rfl hi
      | tail _ h => exact h)

def stateAt {i : σ.Id} (s : { s : Slot sys // s.id = i }) : sys.State i :=
  s.property ▸ s.val.state

def timersAt {i : σ.Id} (s : { s : Slot sys // s.id = i }) : List (σ.Msg i) :=
  s.property ▸ s.val.timers

def same [∀ i, BEq (sys.State i)] (a b : Slot sys) : Bool :=
  if h : a.id = b.id then
    (h ▸ a.state : sys.State b.id) == b.state && a.up == b.up
      && (h ▸ a.timers : List (σ.Msg b.id)) == b.timers
  else false

def allSame [∀ i, BEq (sys.State i)] : List (Slot sys) → List (Slot sys) → Bool
  | [], [] => true
  | a :: as, b :: bs => a.same b && allSame as bs
  | _, _ => false

def hash [∀ i, Hashable (sys.State i)] [∀ i, Hashable (σ.Msg i)] (h : UInt64) (s : Slot sys) :
    UInt64 :=
  mixHash h (mixHash (Hashable.hash s.state)
    (mixHash (Hashable.hash s.up) (Hashable.hash s.timers)))

theorem find_map (c : SysState sys) (l : List σ.Id) (i : σ.Id)
    (h : i ∈ (l.map (of c)).map (·.id)) : (find (l.map (of c)) i h).val = of c i := by
  induction l with
  | nil => nomatch h
  | cons j l ih =>
    simp only [List.map_cons, find]
    split
    · next hi => subst hi; rfl
    · exact ih _

end Slot

/--
The actors of a state as data, one slot each. A state holds them in functions, and a function
built by a long run is a chain of updates as deep as the run is long, which every lookup walks.

`Slots.of` returns data, not a function, so that it is evaluated where it is written: a
definition that returns a function is compiled to one that takes the argument too, and would
build the table again on every lookup.
-/
structure Slots {σ : Signature} (sys : System σ) where
  list : List (Slot sys)
  complete : ∀ i, i ∈ list.map (·.id)

namespace Slots

variable {sys : System σ}

def of [Enum σ.Id] (c : SysState sys) : Slots sys where
  list := (Enum.all (α := σ.Id)).map (Slot.of c)
  complete i := by simpa [Function.comp_def, Slot.of] using Enum.complete i

def state (t : Slots sys) (i : σ.Id) : sys.State i :=
  Slot.stateAt (Slot.find t.list i (t.complete i))

def up (t : Slots sys) (i : σ.Id) : Bool :=
  (Slot.find t.list i (t.complete i)).val.up

def timers (t : Slots sys) (i : σ.Id) : List (σ.Msg i) :=
  Slot.timersAt (Slot.find t.list i (t.complete i))

theorem find_of [Enum σ.Id] (c : SysState sys) (i : σ.Id) :
    (Slot.find (of c).list i ((of c).complete i)).val = Slot.of c i :=
  Slot.find_map c _ i _

@[simp] theorem state_of [Enum σ.Id] (c : SysState sys) : (of c).state = c.state := by
  funext i
  have hval := find_of c i
  change Slot.stateAt (Slot.find (of c).list i ((of c).complete i)) = c.state i
  generalize Slot.find (of c).list i ((of c).complete i) = s at hval
  obtain ⟨s, hs⟩ := s
  subst hval
  rfl

@[simp] theorem up_of [Enum σ.Id] (c : SysState sys) : (of c).up = c.up :=
  funext fun i => congrArg Slot.up (find_of c i)

@[simp] theorem timers_of [Enum σ.Id] (c : SysState sys) : (of c).timers = c.timers := by
  funext i
  have hval := find_of c i
  change Slot.timersAt (Slot.find (of c).list i ((of c).complete i)) = c.timers i
  generalize Slot.find (of c).list i ((of c).complete i) = s at hval
  obtain ⟨s, hs⟩ := s
  subst hval
  rfl

end Slots

namespace SysState

variable {sys : System σ}

/-- `c` with its per-actor functions read from `slots`. -/
def compactWith (c : SysState sys) (slots : Slots sys) : SysState sys :=
  { c with state := slots.state, up := slots.up, timers := slots.timers }

@[simp] theorem compactWith_of [Enum σ.Id] (c : SysState sys) : c.compactWith (.of c) = c := by
  simp [compactWith]

/-- The same state, with its per-actor functions rebuilt from a table of their values. -/
def compact [Enum σ.Id] (c : SysState sys) : SysState sys :=
  c.compactWith (.of c)

@[simp] theorem compact_eq [Enum σ.Id] (c : SysState sys) : c.compact = c :=
  compactWith_of c

variable [σ.Inspect] [sys.Inspect]

/--
Whether two lists of messages in flight are the same traffic. Each message of `a` is matched
with one of `b` and both are taken out: on an ordered link it must be the oldest message of its
link in `b`, on an unordered one any occurrence does. One pass over `a`, and lists in the same
order cost one comparison per message.
-/
def netEquiv (env : EnvModel σ) : List (Envelope σ) → List (Envelope σ) → Bool
  | [], b => b.isEmpty
  | e :: a, b =>
    (if (env.link e.src e.dst).ordered then b.find? e.sameLink == some e else b.contains e)
      && netEquiv env a (b.erase e)

/-- Message order only counts where the link model makes it observable. -/
def equiv (env : EnvModel σ) (a b : SysState sys) : Bool :=
  (Enum.all (α := σ.Id)).all (fun i =>
      a.state i == b.state i && a.up i == b.up i && a.timers i == b.timers i)
    && netEquiv env a.net b.net && a.outbox.isPerm b.outbox

/-- A hash of the messages in flight and the pending outputs that does not depend on their
order. -/
def trafficHash (c : SysState sys) : UInt64 :=
  let net := c.net.foldl (init := 0) fun h e => h + mixHash 11 (Hashable.hash e)
  let outbox := c.outbox.foldl (init := 0) fun h o => h + mixHash 13 (Hashable.hash o)
  mixHash net outbox

/-- A hash that agrees with `equiv`: it does not depend on the order of messages in flight. -/
def hash (c : SysState sys) : UInt64 :=
  let actors := (Enum.all (α := σ.Id)).foldl (init := 7) fun h i =>
    mixHash h (mixHash (Hashable.hash (c.state i))
      (mixHash (Hashable.hash (c.up i)) (Hashable.hash (c.timers i))))
  mixHash actors c.trafficHash

def render (c : SysState sys) : String :=
  let actors := (Enum.all (α := σ.Id)).filterMap fun i =>
    let timers := if (c.timers i).isEmpty then "" else s!" timers={brief (c.timers i)}"
    some s!"  {brief i} [{if c.up i then "up" else "down"}] {brief (c.state i)}{timers}"
  let net := c.net.map fun e => s!"  in flight: {e.render}"
  let outbox := c.outbox.map fun o => s!"  pending output: {brief o}"
  "\n".intercalate (actors ++ net ++ outbox)

end SysState

end Lanes
