/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Runtime.KernelSound
public import Lanes.Runtime.Wave
public import Lanes.Proof.List

/-!
What a shard does with everything it takes from its inbox at once, as a pure function: the
turns it asks of the kernel, and the acts the shell is to perform for them, in order. The shell
(`Lanes.Runtime`) performs them and decides nothing.

A turn is everything the shell asks of the kernel between two looks at its inbox, and the
requests (`Kernel.Op`) it is: what the turn does is what those requests do (`turn_eq_exec`,
`turnAll_eq_exec`). A batch keeps them, as a `work` act the shell performs nothing for, so that
every other act can be tied to the kernel.

Of every batch: the kernel after it is the one its requests lead to (`run_kernel`); every output
those requests produced is handed over and every event recorded, in order (`run_handed`); and a
peek is answered with the states of the kernel the requests so far lead to, once every output
they produced is handed over (`run_sound`). By `Kernel.exec_reachable` that is a run of the
semantics. Who waits for the shard to be idle is answered when the kernel is quiet
(`run_resolved`).

A peek reads the states of some actors and writes nothing. It is answered at the end of its
batch, after every other act, with the states of the kernel the whole batch leaves: it sees every
request before that boundary and none after it (`run_peeks`). A batch with its peeks taken out is
the same batch, act for act (`run_erase_peeks`), so the work and the outputs are those of the
inputs alone.

The reply handles are opaque: `P ids` answers a peek at the actors `ids` and `W` an idle, as `W`
wakes a sleeper in `Mailbox`.
-/

@[expose] public section

namespace Lanes.Batch

variable {σ : Signature}

inductive Command (σ : Signature) (P : List σ.Id → Type) (W : Type) where
  | input (x : σ.In)
  /-- Inputs that arrived together, accepted in order before any work is done for them, so that
  the actors they reach can step in parallel (`turnAll`). -/
  | inputs (xs : List σ.In)
  | idle (timers : Bool) (waiter : W)
  /-- Read the states of the actors `ids`, and of every actor started that `every` holds of, at
  the end of the batch. -/
  | peek (ids : List σ.Id) (every : σ.Id → Bool) (reply : P ids)

/-- The states of the actors `ids`, read together, and those of every actor started that `every`
holds of (`others`): an actor not started has its initial state. -/
structure Peek (sys : System σ) (ids : List σ.Id) where
  states : List ((i : σ.Id) × sys.State i)
  ids_eq : states.map (·.1) = ids
  every : σ.Id → Bool := fun _ => false
  others : List ((i : σ.Id) × sys.State i) := []

inductive Act (sys : System σ) (P : List σ.Id → Type) where
  /-- The requests the kernel was asked since the act before, in order. The shell performs
  nothing for it: it is what ties every other act to the kernel (`run_kernel`, `run_sound`). -/
  | work (ops : Array (Kernel.Op σ))
  | record (events : Array (Event σ))
  | handOver (outputs : Array σ.Out)
  | answer (ids : List σ.Id) (reply : P ids) (peek : Peek sys ids)

structure Config where
  now_ms : Nat
  fuel : Nat
  /-- How the steps of a wave of `inputs` are spread over threads (`Kernel.runWaves`). It does
  not change the batch (`run_spread`). -/
  spread : Kernel.Spread := {}

/-- The shard's part of a batch so far, besides its kernel. -/
structure Scan (sys : System σ) (P : List σ.Id → Type) (W : Type) where
  waiting : Array (Bool × W)
  acts : Array (Act sys P) := #[]
  ops : Array (Kernel.Op σ) := #[]
  events : Array (Event σ) := #[]
  outputs : Array σ.Out := #[]
  worked : Bool := false

structure Result (sys : System σ) [Hashable σ.Id] (P : List σ.Id → Type) (W : Type) where
  kernel : Kernel sys
  acts : Array (Act sys P)
  resolved : Array W
  waiting : Array (Bool × W)

variable {sys : System σ} {P : List σ.Id → Type} {W : Type}

/-- The state of `i` among `states`. -/
def Peek.find : (states : List ((i : σ.Id) × sys.State i)) → (i : σ.Id) →
    i ∈ states.map (·.1) → sys.State i
  | [], _, h => absurd h List.not_mem_nil
  | ⟨j, s⟩ :: rest, i, h =>
    if e : j = i then e ▸ s
    else Peek.find rest i (by
      rw [List.map_cons, List.mem_cons] at h
      exact h.resolve_left fun h' => e h'.symm)

def Peek.get {ids : List σ.Id} (p : Peek sys ids) (i : σ.Id) (h : i ∈ ids) : sys.State i :=
  Peek.find p.states i (by rw [p.ids_eq]; exact h)

theorem Peek.find_map (f : (i : σ.Id) → sys.State i) (ids : List σ.Id) (i : σ.Id)
    (h : i ∈ (ids.map fun j => (⟨j, f j⟩ : (i : σ.Id) × sys.State i)).map (·.1)) :
    Peek.find (ids.map fun j => ⟨j, f j⟩) i h = f i := by
  induction ids with
  | nil => simp at h
  | cons j rest ih =>
    simp only [List.map_cons, Peek.find]
    split
    · next e => subst e; rfl
    · exact ih _

def Command.isPeek : Command σ P W → Bool
  | .peek .. => true
  | _ => false

def Command.peek? : Command σ P W → Option ((ids : List σ.Id) × (σ.Id → Bool) × P ids)
  | .peek ids every reply => some ⟨ids, every, reply⟩
  | _ => none

def put (acts : Array (Act sys P)) (skip : Bool) (act : Act sys P) : Array (Act sys P) :=
  if skip then acts else acts.push act

variable [Hashable σ.Id]

/-- The states of `ids` in kernel `k`, and of every actor of `k` started that `every` holds of. -/
def Peek.of (k : Kernel sys) (ids : List σ.Id) (every : σ.Id → Bool := fun _ => false) :
    Peek sys ids where
  states := ids.map fun i => ⟨i, (k.cell i).state⟩
  ids_eq := by simp [List.map_map, Function.comp_def]
  every := every
  others := k.cells.toList.filterMap fun x => if every x.1 then some ⟨x.1, x.2.state⟩ else none

/-- A peek gives each actor's state in the kernel it was read from. -/
theorem Peek.get_of (k : Kernel sys) (ids : List σ.Id) (every : σ.Id → Bool) (i : σ.Id)
    (h : i ∈ ids) : (Peek.of k ids every).get i h = (k.cell i).state :=
  Peek.find_map (fun j => (k.cell j).state) ids i _

/-- Every state among a peek's others is that actor's state in the kernel it was read from, of
an actor `every` holds of. -/
theorem Peek.others_of {k : Kernel sys} {ids : List σ.Id} {every : σ.Id → Bool}
    {x : (i : σ.Id) × sys.State i} (h : x ∈ (Peek.of k ids every).others) :
    every x.1 = true ∧ x.2 = (k.cell x.1).state := by
  simp only [Peek.of, List.mem_filterMap] at h
  obtain ⟨⟨i, cell⟩, hmem, hx⟩ := h
  split at hx
  · next hp =>
    cases hx
    have hget : k.cells.get? i = some cell := Std.DHashMap.mem_toList_iff_get?_eq_some.mp hmem
    exact ⟨hp, by simp [Kernel.cell, hget]⟩
  · cases hx

/-- An actor `every` holds of that is not among a peek's others has its initial state in the
kernel it was read from: it was never started. -/
theorem Peek.init_of_not_others {k : Kernel sys} {ids : List σ.Id} {every : σ.Id → Bool}
    {i : σ.Id} (hp : every i = true) (h : i ∉ (Peek.of k ids every).others.map (·.1)) :
    (k.cell i).state = (sys.actor i).init := by
  cases hget : k.cells.get? i with
  | none => simp [Kernel.cell, hget]
  | some cell =>
    exfalso
    refine h (List.mem_map.mpr ⟨⟨i, cell.state⟩, ?_, rfl⟩)
    simp only [Peek.of, List.mem_filterMap]
    exact ⟨⟨i, cell⟩, Std.DHashMap.mem_toList_iff_get?_eq_some.mpr hget, by simp [hp]⟩

/-! One turn, as a pure function: everything the shell asks of the kernel between two looks at
its inbox, and the requests that is. -/

structure Turn (sys : System σ) [Hashable σ.Id] where
  kernel : Kernel sys
  events : List (Event σ) := []
  outputs : List σ.Out := []
  ops : List (Kernel.Op σ) := []

/--
Take an input if there is one and do up to `fuel` units of work at time `now_ms`. If there is
no input and nothing to do yet, the kernel is left exactly as it was, clock included, and
nothing is asked of it: so the requests always describe the kernel (`turn_eq_exec`).
-/
def turn (k : Kernel sys) (now_ms : Nat) (input : Option σ.In) (fuel : Nat) : Turn sys :=
  if input.isNone && (k.advance now_ms).wait != .none then { kernel := k }
  else
    let k := k.advance now_ms
    let clock := k.clock_ms
    match input with
    | none =>
      match k.runBatch fuel with
      | { kernel, events, outputs } =>
        { kernel, events, outputs, ops := [.advance clock, .batch fuel] }
    | some x =>
      match k.accept x with
      | { kernel, events := accepted, .. } =>
        match kernel.runBatch fuel with
        | { kernel, events, outputs } =>
          { kernel, events := accepted ++ events, outputs
            ops := [.advance clock, .input x, .batch fuel] }

private theorem advance_clock (k : Kernel sys) (now_ms : Nat) :
    k.advance (k.advance now_ms).clock_ms = k.advance now_ms := by
  simp only [Kernel.advance]
  congr 1
  omega

/-- What a turn does is what its requests do: the same kernel, the same events, the same
outputs. Nothing is assumed of the clock. -/
theorem turn_eq_exec (k : Kernel sys) (now_ms : Nat) (input : Option σ.In) (fuel : Nat) :
    (turn k now_ms input fuel).kernel = (k.exec (turn k now_ms input fuel).ops).kernel
      ∧ (turn k now_ms input fuel).events = (k.exec (turn k now_ms input fuel).ops).events
      ∧ (turn k now_ms input fuel).outputs = (k.exec (turn k now_ms input fuel).ops).outputs := by
  unfold turn
  split
  · exact ⟨rfl, rfl, rfl⟩
  · cases input with
    | none =>
      simp [Kernel.apply, Kernel.exec, advance_clock]
    | some x =>
      simp [Kernel.apply, Kernel.exec, advance_clock, Kernel.accept]

/-- `turn` for inputs that arrived together: each is accepted, in order, and then up to `fuel`
units of work are done, the steps of different actors worked out as `spread` says
(`Kernel.runWaves`, which is `runBatch`). The requests are `advance`, the inputs and one
`batch`. -/
def turnAll (k : Kernel sys) (now_ms : Nat) (inputs : List σ.In) (fuel : Nat)
    (spread : Kernel.Spread) : Turn sys :=
  if inputs.isEmpty && (k.advance now_ms).wait != .none then { kernel := k }
  else
    let k := k.advance now_ms
    let clock := k.clock_ms
    match (k.acceptAll inputs).runWaves spread fuel with
    | { kernel, events, outputs } =>
      { kernel, events := inputs.map .input ++ events, outputs
        ops := .advance clock :: (inputs.map .input ++ [.batch fuel]) }

theorem turnAll_eq_exec (k : Kernel sys) (now_ms : Nat) (inputs : List σ.In) (fuel : Nat)
    (spread : Kernel.Spread) :
    (turnAll k now_ms inputs fuel spread).kernel
        = (k.exec (turnAll k now_ms inputs fuel spread).ops).kernel
      ∧ (turnAll k now_ms inputs fuel spread).events
          = (k.exec (turnAll k now_ms inputs fuel spread).ops).events
      ∧ (turnAll k now_ms inputs fuel spread).outputs
          = (k.exec (turnAll k now_ms inputs fuel spread).ops).outputs := by
  unfold turnAll
  split
  · exact ⟨rfl, rfl, rfl⟩
  · simp only [Kernel.exec_cons, Kernel.exec_append, Kernel.exec_inputs, Kernel.runWaves_eq,
      Kernel.apply, advance_clock]
    simp [Kernel.exec]

/-- How a turn's waves are spread does not change the turn (`Kernel.runWaves_eq`). -/
theorem turnAll_spread (k : Kernel sys) (now_ms : Nat) (inputs : List σ.In) (fuel : Nat)
    (spread : Kernel.Spread) :
    turnAll k now_ms inputs fuel spread = turnAll k now_ms inputs fuel {} := by
  unfold turnAll
  simp only [Kernel.runWaves_eq]

/-! A batch. -/

/-- A turn, kept back to be handed over with the turns after it. -/
def workWith (turn : Kernel sys → Turn sys) :
    Kernel sys × Scan sys P W → Kernel sys × Scan sys P W
  | (k, ⟨waiting, acts, ops, events, outputs, _⟩) =>
    match turn k with
    | { kernel, events := more, outputs := out, ops := new } =>
      (kernel, { waiting, acts, ops := ops ++ new, events := events ++ more
                 outputs := outputs ++ out, worked := true })

def work (c : Config) (input : Option σ.In) : Kernel sys × Scan sys P W → Kernel sys × Scan sys P W :=
  workWith fun k => turn k c.now_ms input c.fuel

/-- The turn of inputs that arrived together, with `fuel` for each. -/
def workAll (c : Config) (xs : List σ.In) : Kernel sys × Scan sys P W → Kernel sys × Scan sys P W :=
  workWith fun k => turnAll k c.now_ms xs (c.fuel * max 1 xs.length) c.spread

/-- Hand over what was kept back. -/
def flush : Kernel sys × Scan sys P W → Kernel sys × Scan sys P W
  | (k, ⟨waiting, acts, ops, events, outputs, worked⟩) =>
    (k, { waiting, worked
          acts := put (put (put acts ops.isEmpty (.work ops)) events.isEmpty (.record events))
            outputs.isEmpty (.handOver outputs) })

def scan (c : Config) (ks : Kernel sys × Scan sys P W) :
    Command σ P W → Kernel sys × Scan sys P W
  | .input x => work c (some x) ks
  | .inputs xs => workAll c xs ks
  | .idle timers waiter =>
    match flush ks with
    | (k, s) => (k, { s with waiting := s.waiting.push (timers, waiter) })
  | .peek .. => ks

/-- The answers to `peeks` from kernel `k`. -/
def answers (k : Kernel sys) (peeks : List ((ids : List σ.Id) × (σ.Id → Bool) × P ids)) :
    List (Act sys P) :=
  peeks.map fun p => .answer p.1 p.2.2 (Peek.of k p.1 p.2.1)

/-- The end of a batch: what is kept back is handed over, and the peeks are answered from the
kernel that leaves. -/
def finish (c : Config) (ks : Kernel sys × Scan sys P W)
    (peeks : List ((ids : List σ.Id) × (σ.Id → Bool) × P ids)) : Result sys P W :=
  match flush (if ks.2.worked then ks else work c none ks) with
  | (k, s) =>
    { kernel := k, acts := s.acts ++ (answers k peeks).toArray
      resolved := (s.waiting.filter fun w => k.quiet w.1).map (·.2)
      waiting := s.waiting.filter fun w => !k.quiet w.1 }

/-- Inputs next to each other as one command, so that they are accepted together, at most `most`
to a command. -/
def group (most : Nat) : List (Command σ P W) → List (Command σ P W)
  | [] => []
  | .input x :: rest =>
    match group most rest with
    | .inputs xs :: more =>
      if xs.length < most then .inputs (x :: xs) :: more else .inputs [x] :: .inputs xs :: more
    | more => .inputs [x] :: more
  | c :: rest => c :: group most rest

/-- The inputs a command carries. -/
def Command.ins : Command σ P W → List σ.In
  | .input x => [x]
  | .inputs xs => xs
  | _ => []

omit [Hashable σ.Id] in
/-- Grouping keeps every input, in order. -/
theorem group_ins (most : Nat) (commands : List (Command σ P W)) :
    (group most commands).flatMap Command.ins = commands.flatMap Command.ins := by
  induction commands with
  | nil => rfl
  | cons c rest ih =>
    cases c with
    | input x =>
      simp only [group]
      split
      · next xs more h =>
        rw [h] at ih
        simp only [List.flatMap_cons, Command.ins] at ih ⊢
        split <;> simp only [List.flatMap_cons, Command.ins, ← ih] <;> rfl
      · simp only [List.flatMap_cons, Command.ins, ← ih]
    | inputs xs => simp only [group, List.flatMap_cons, ih]
    | idle timers waiter => simp only [group, List.flatMap_cons, ih]
    | peek i every reply => simp only [group, List.flatMap_cons, ih]

/-- One batch: a turn for each input, at one time; when no input came, one turn without. Its
peeks are answered at its end. -/
def run (c : Config) (k : Kernel sys) (waiting : Array (Bool × W))
    (commands : List (Command σ P W)) : Result sys P W :=
  finish c (commands.foldl (scan c) (k, { waiting })) (commands.filterMap Command.peek?)

/-! What the acts amount to. -/

def Act.ops : Act sys P → List (Kernel.Op σ)
  | .work ops => ops.toList
  | _ => []

def Act.outputs : Act sys P → List σ.Out
  | .handOver outputs => outputs.toList
  | _ => []

def Act.events : Act sys P → List (Event σ)
  | .record events => events.toList
  | _ => []

/-- The requests the acts asked of the kernel. -/
def requests (acts : List (Act sys P)) : List (Kernel.Op σ) := acts.flatMap Act.ops

def handed (acts : List (Act sys P)) : List σ.Out := acts.flatMap Act.outputs

def recorded (acts : List (Act sys P)) : List (Event σ) := acts.flatMap Act.events

/-- What an act may do after `before`, from kernel `k`: hand over or record exactly what the
requests so far produced and was not yet handed over or recorded, and answer a peek with the
states of the kernel those requests lead to, once every output they produced is handed over. -/
def Act.Sound (k : Kernel sys) (before : List (Act sys P)) : Act sys P → Prop
  | .work _ => True
  | .record events => recorded before ++ events.toList = (k.exec (requests before)).events
  | .handOver outputs =>
    handed before ++ outputs.toList = (k.exec (requests before)).outputs
  | .answer ids _ peek =>
    peek = Peek.of (k.exec (requests before)).kernel ids peek.every
      ∧ handed before = (k.exec (requests before)).outputs

def Sound (k : Kernel sys) (acts : List (Act sys P)) : Prop :=
  ∀ before act after, acts = before ++ act :: after → act.Sound k before

def Command.idle? : Command σ P W → Option (Bool × W)
  | .idle timers waiter => some (timers, waiter)
  | _ => none

private theorem sound_push {k : Kernel sys} {acts : List (Act sys P)} {act : Act sys P}
    (h : Sound k acts) (hact : act.Sound k acts) : Sound k (acts ++ [act]) := by
  intro before b after hb
  rcases append_singleton_eq_append_cons hb with ⟨rfl, rfl, -⟩ | ⟨rest, rfl, -⟩
  · exact hact
  · exact h before b rest rfl

omit [Hashable σ.Id] in
private theorem toList_put (acts : Array (Act sys P)) (skip : Bool) (act : Act sys P) :
    (put acts skip act).toList = if skip then acts.toList else acts.toList ++ [act] := by
  unfold put; split <;> simp

private structure Inv (k0 : Kernel sys) (ks : Kernel sys × Scan sys P W) : Prop where
  kernel : ks.1 = (k0.exec (requests ks.2.acts.toList ++ ks.2.ops.toList)).kernel
  outputs : handed ks.2.acts.toList ++ ks.2.outputs.toList
    = (k0.exec (requests ks.2.acts.toList ++ ks.2.ops.toList)).outputs
  events : recorded ks.2.acts.toList ++ ks.2.events.toList
    = (k0.exec (requests ks.2.acts.toList ++ ks.2.ops.toList)).events
  sound : Sound k0 ks.2.acts.toList

private theorem inv_start (k : Kernel sys) (waiting : Array (Bool × W)) :
    Inv k (k, ({ waiting } : Scan sys P W)) where
  kernel := by simp [requests, Kernel.exec]
  outputs := by simp [handed, requests, Kernel.exec]
  events := by simp [recorded, requests, Kernel.exec]
  sound := fun before act after h => by simp at h

private theorem inv_workWith (turn : Kernel sys → Turn sys)
    (hturn : ∀ k, (turn k).kernel = (k.exec (turn k).ops).kernel
      ∧ (turn k).events = (k.exec (turn k).ops).events
      ∧ (turn k).outputs = (k.exec (turn k).ops).outputs) {k0 : Kernel sys}
    {ks : Kernel sys × Scan sys P W} (h : Inv k0 ks) : Inv k0 (workWith turn ks) := by
  obtain ⟨k, ⟨waiting, acts, ops, events, outputs, worked⟩⟩ := ks
  obtain ⟨hk, ho, he, hs⟩ := h
  obtain ⟨tk, te, to⟩ := hturn k
  simp only at hk ho he hs
  have hexec : ∀ more : List (Kernel.Op σ),
      k0.exec (requests acts.toList ++ (ops.toList ++ more))
        = { kernel := (k.exec more).kernel
            events := (k0.exec (requests acts.toList ++ ops.toList)).events
              ++ (k.exec more).events
            outputs := (k0.exec (requests acts.toList ++ ops.toList)).outputs
              ++ (k.exec more).outputs } := by
    intro more
    rw [← List.append_assoc, Kernel.exec_append, ← hk]
  refine ⟨?_, ?_, ?_, hs⟩ <;>
    simp only [workWith, Array.toList_appendList, hexec, ← tk, ← te, ← to, ← ho, ← he,
      List.append_assoc]

private theorem inv_work (c : Config) (input : Option σ.In) {k0 : Kernel sys}
    {ks : Kernel sys × Scan sys P W} (h : Inv k0 ks) : Inv k0 (work c input ks) :=
  inv_workWith _ (fun k => turn_eq_exec k c.now_ms input c.fuel) h

private theorem inv_workAll (c : Config) (xs : List σ.In) {k0 : Kernel sys}
    {ks : Kernel sys × Scan sys P W} (h : Inv k0 ks) : Inv k0 (workAll c xs ks) :=
  inv_workWith _ (fun k => turnAll_eq_exec k c.now_ms xs _ c.spread) h

private theorem inv_flush {k0 : Kernel sys} {ks : Kernel sys × Scan sys P W} (h : Inv k0 ks) :
    Inv k0 (flush ks) ∧ (flush ks).2.ops = #[] ∧ (flush ks).2.events = #[]
      ∧ (flush ks).2.outputs = #[] := by
  obtain ⟨k, ⟨waiting, acts, ops, events, outputs, worked⟩⟩ := ks
  obtain ⟨hk, ho, he, hs⟩ := h
  simp only at hk ho he hs
  generalize hx : k0.exec (requests acts.toList ++ ops.toList) = x at hk ho he
  let a1 := put acts ops.isEmpty (.work ops)
  let a2 := put a1 events.isEmpty (.record events)
  let a3 := put a2 outputs.isEmpty (.handOver outputs)
  have j1 : requests a1.toList = requests acts.toList ++ ops.toList := by
    simp only [a1, toList_put]; split <;> simp_all [requests, Act.ops]
  have r1 : recorded a1.toList = recorded acts.toList := by
    simp only [a1, toList_put]; split <;> simp [recorded, Act.events]
  have h1 : handed a1.toList = handed acts.toList := by
    simp only [a1, toList_put]; split <;> simp [handed, Act.outputs]
  have s1 : Sound k0 a1.toList := by
    simp only [a1, toList_put]; split
    · exact hs
    · exact sound_push hs trivial
  have j2 : requests a2.toList = requests a1.toList := by
    simp only [a2, toList_put]; split <;> simp [requests, Act.ops]
  have r2 : recorded a2.toList = recorded acts.toList ++ events.toList := by
    simp only [a2, toList_put]; split <;> simp_all [recorded, Act.events]
  have h2 : handed a2.toList = handed acts.toList := by
    rw [← h1]; simp only [a2, toList_put]; split <;> simp [handed, Act.outputs]
  have s2 : Sound k0 a2.toList := by
    simp only [a2, toList_put]; split
    · exact s1
    · exact sound_push s1 (by simp only [Act.Sound, r1, j1, hx, he])
  have j3 : requests a3.toList = requests acts.toList ++ ops.toList := by
    rw [← j1, ← j2]; simp only [a3, toList_put]; split <;> simp [requests, Act.ops]
  have r3 : recorded a3.toList = recorded acts.toList ++ events.toList := by
    rw [← r2]; simp only [a3, toList_put]; split <;> simp [recorded, Act.events]
  have h3 : handed a3.toList = handed acts.toList ++ outputs.toList := by
    simp only [a3, toList_put]; split <;> simp_all [handed, Act.outputs]
  have s3 : Sound k0 a3.toList := by
    simp only [a3, toList_put]; split
    · exact s2
    · exact sound_push s2 (by simp only [Act.Sound, h2, j2, j1, hx, ho])
  have flushed : flush (k, ⟨waiting, acts, ops, events, outputs, worked⟩)
      = (k, { waiting, acts := a3, worked }) := rfl
  rw [flushed]
  refine ⟨⟨?_, ?_, ?_, s3⟩, rfl, rfl, rfl⟩ <;> simp only [List.append_nil, j3, hx]
  · exact hk
  · rw [h3, ho]
  · rw [r3, he]

private theorem inv_scan (c : Config) {k0 : Kernel sys} {ks : Kernel sys × Scan sys P W}
    (h : Inv k0 ks) (command : Command σ P W) : Inv k0 (scan c ks command) := by
  cases command with
  | input x => exact inv_work c (some x) h
  | inputs xs => exact inv_workAll c xs h
  | idle timers waiter =>
    obtain ⟨⟨hk, ho, he, hs⟩, -⟩ := inv_flush h
    exact ⟨hk, ho, he, hs⟩
  | peek ids every reply => exact h

private theorem inv_foldl (c : Config) {k0 : Kernel sys} (commands : List (Command σ P W)) :
    ∀ {ks : Kernel sys × Scan sys P W}, Inv k0 ks → Inv k0 (commands.foldl (scan c) ks) := by
  induction commands with
  | nil => exact id
  | cons command commands ih => exact fun h => ih (inv_scan c h command)

private theorem answers_mem {k : Kernel sys} {peeks : List ((ids : List σ.Id) × (σ.Id → Bool) × P ids)}
    {a : Act sys P} (h : a ∈ answers k peeks) :
    a.ops = [] ∧ a.outputs = [] ∧ a.events = [] := by
  simp only [answers, List.mem_map] at h
  obtain ⟨p, -, rfl⟩ := h
  exact ⟨rfl, rfl, rfl⟩

/-- Answers ask nothing of the kernel, hand nothing over and record nothing. -/
private theorem answers_none (k : Kernel sys) (peeks : List ((ids : List σ.Id) × (σ.Id → Bool) × P ids))
    (acts : List (Act sys P)) :
    requests (acts ++ answers k peeks) = requests acts
      ∧ handed (acts ++ answers k peeks) = handed acts
      ∧ recorded (acts ++ answers k peeks) = recorded acts := by
  simp only [requests, handed, recorded, List.flatMap_append]
  refine ⟨?_, ?_, ?_⟩ <;>
    rw [(List.flatMap_eq_nil_iff (l := answers k peeks)).mpr (fun a ha => by simp [answers_mem ha]),
      List.append_nil]

private theorem sound_answers {k0 k : Kernel sys} (peeks : List ((ids : List σ.Id) × (σ.Id → Bool) × P ids)) :
    ∀ {acts : List (Act sys P)}, Sound k0 acts → k = (k0.exec (requests acts)).kernel →
      handed acts = (k0.exec (requests acts)).outputs → Sound k0 (acts ++ answers k peeks) := by
  induction peeks with
  | nil => intro acts h _ _; simpa [answers] using h
  | cons p peeks ih =>
    intro acts h hk hh
    have hj : requests (acts ++ [Act.answer p.1 p.2.2 (Peek.of k p.1 p.2.1)]) = requests acts := by
      simp [requests, Act.ops]
    have hh' : handed (acts ++ [Act.answer p.1 p.2.2 (Peek.of k p.1 p.2.1)]) = handed acts := by
      simp [handed, Act.outputs]
    have := ih (acts := acts ++ [.answer p.1 p.2.2 (Peek.of k p.1 p.2.1)])
      (sound_push h (by simp only [Act.Sound]; exact ⟨by rw [hk]; rfl, hh⟩)) (by rw [hj]; exact hk)
      (by rw [hj, hh']; exact hh)
    simpa [answers] using this

private theorem inv_finish (c : Config) {k0 : Kernel sys} {ks : Kernel sys × Scan sys P W}
    (peeks : List ((ids : List σ.Id) × (σ.Id → Bool) × P ids)) (h : Inv k0 ks) :
    (finish c ks peeks).kernel = (k0.exec (requests (finish c ks peeks).acts.toList)).kernel
      ∧ handed (finish c ks peeks).acts.toList
          = (k0.exec (requests (finish c ks peeks).acts.toList)).outputs
      ∧ recorded (finish c ks peeks).acts.toList
          = (k0.exec (requests (finish c ks peeks).acts.toList)).events
      ∧ Sound k0 (finish c ks peeks).acts.toList := by
  have hw : Inv k0 (if ks.2.worked then ks else work c none ks) := by
    split
    · exact h
    · exact inv_work c none h
  obtain ⟨⟨hk, ho, he, hs⟩, hops, hevents, houtputs⟩ := inv_flush hw
  simp only [finish]
  generalize flush (if ks.2.worked then ks else work c none ks) = f
    at hk ho he hs hops hevents houtputs
  obtain ⟨k, s⟩ := f
  simp only at hk ho he hs hops hevents houtputs
  rw [hops, Array.toList_empty, List.append_nil] at hk ho he
  rw [houtputs, Array.toList_empty, List.append_nil] at ho
  rw [hevents, Array.toList_empty, List.append_nil] at he
  obtain ⟨hj, hh, hr⟩ := answers_none k peeks s.acts.toList
  simp only [Array.toList_append, hj, hh, hr]
  exact ⟨hk, ho, he, sound_answers peeks hs hk ho⟩

/-- The kernel after a batch is the one its requests lead to. By `Kernel.exec_reachable` that is
a state the semantics reaches by the events they reported. -/
theorem run_kernel (c : Config) (k : Kernel sys) (waiting : Array (Bool × W))
    (commands : List (Command σ P W)) :
    (run c k waiting commands).kernel
      = (k.exec (requests (run c k waiting commands).acts.toList)).kernel :=
  (inv_finish c _ (inv_foldl c commands (inv_start k waiting))).1

/-- By the end of a batch every output its requests produced has been handed over, and every
event recorded. -/
theorem run_handed (c : Config) (k : Kernel sys) (waiting : Array (Bool × W))
    (commands : List (Command σ P W)) :
    handed (run c k waiting commands).acts.toList
        = (k.exec (requests (run c k waiting commands).acts.toList)).outputs
      ∧ recorded (run c k waiting commands).acts.toList
        = (k.exec (requests (run c k waiting commands).acts.toList)).events :=
  let h := inv_finish c _ (inv_foldl c commands (inv_start k waiting))
  ⟨h.2.1, h.2.2.1⟩

/-- Every act of a batch is sound where it falls. So outputs are handed over and events recorded
exactly as the kernel produced them, in order, and a peek is answered with the state of the
kernel the requests so far lead to, after every output they produced. -/
theorem run_sound (c : Config) (k : Kernel sys) (waiting : Array (Bool × W))
    (commands : List (Command σ P W)) : Sound k (run c k waiting commands).acts.toList :=
  (inv_finish c _ (inv_foldl c commands (inv_start k waiting))).2.2.2

private theorem foldl_erase (c : Config) (commands : List (Command σ P W)) :
    ∀ ks : Kernel sys × Scan sys P W,
      (commands.filter (!·.isPeek)).foldl (scan c) ks = commands.foldl (scan c) ks := by
  induction commands with
  | nil => intro _; rfl
  | cons command rest ih =>
    intro ks
    cases command with
    | peek ids every reply =>
      rw [List.filter_cons_of_neg (by simp [Command.isPeek]), List.foldl_cons, ih]
      rfl
    | _ => rw [List.filter_cons_of_pos (by rfl), List.foldl_cons, List.foldl_cons, ih]

omit [Hashable σ.Id] in
private theorem peeks_erase (commands : List (Command σ P W)) :
    (commands.filter (!·.isPeek)).filterMap Command.peek? = [] := by
  induction commands with
  | nil => rfl
  | cons command rest ih =>
    cases command <;> simp_all [Command.isPeek, Command.peek?]

/-- A batch with its peeks taken out is the same batch: the same kernel, the same waiters, and
the same acts but for the answers, which come after all of them. So the work and the outputs are
those of the inputs alone, wherever the peeks fell among them. -/
theorem run_erase_peeks (c : Config) (k : Kernel sys) (waiting : Array (Bool × W))
    (commands : List (Command σ P W)) :
    run c k waiting commands =
      let r := run c k waiting (commands.filter (!·.isPeek))
      { r with acts := r.acts ++ (answers r.kernel (commands.filterMap Command.peek?)).toArray } := by
  simp only [run, foldl_erase, peeks_erase, finish]
  generalize commands.foldl (scan c) (k, { waiting }) = ks
  generalize flush (if ks.2.worked then ks else work c none ks) = f
  obtain ⟨k', s⟩ := f
  simp [answers]

/-- Each peek of a batch is answered at the batch's end, after every other act, with the states
of the kernel that the batch's requests lead to: it sees every request before that boundary and
none after it. The other acts are those of the batch without its peeks. -/
theorem run_peeks (c : Config) (k : Kernel sys) (waiting : Array (Bool × W))
    (commands : List (Command σ P W)) :
    let r := run c k waiting (commands.filter (!·.isPeek))
    (run c k waiting commands).acts.toList
      = r.acts.toList ++ answers (k.exec (requests r.acts.toList)).kernel
          (commands.filterMap Command.peek?) := by
  intro r
  rw [run_erase_peeks]
  simp only [Array.toList_append]
  rw [← run_kernel]

private theorem waiting_work (c : Config) (input : Option σ.In) (ks : Kernel sys × Scan sys P W) :
    (work c input ks).2.waiting = ks.2.waiting := by
  obtain ⟨k, ⟨_, _, _, _, _, _⟩⟩ := ks; rfl

private theorem waiting_flush (ks : Kernel sys × Scan sys P W) :
    (flush ks).2.waiting = ks.2.waiting := by
  obtain ⟨k, ⟨_, _, _, _, _, _⟩⟩ := ks; rfl

private theorem waiting_foldl (c : Config) (commands : List (Command σ P W)) :
    ∀ ks : Kernel sys × Scan sys P W, (commands.foldl (scan c) ks).2.waiting.toList
      = ks.2.waiting.toList ++ commands.filterMap Command.idle? := by
  induction commands with
  | nil => simp
  | cons command commands ih =>
    intro ks
    rw [List.foldl_cons, ih, List.filterMap_cons]
    cases command with
    | input x => simp [scan, Command.idle?, waiting_work]
    | inputs xs =>
      have hw : (workAll c xs ks).2.waiting = ks.2.waiting := by
        obtain ⟨k, ⟨_, _, _, _, _, _⟩⟩ := ks; rfl
      simp [scan, Command.idle?, hw]
    | idle timers waiter => simp [scan, Command.idle?, waiting_flush]
    | peek ids every reply => simp [scan, Command.idle?]

/-- Those waiting for the shard to be idle, from before the batch and from its commands in
order, are answered at its end exactly when the kernel is then quiet, with or without timers as
each asked; the others go on waiting. -/
theorem run_resolved (c : Config) (k : Kernel sys) (waiting : Array (Bool × W))
    (commands : List (Command σ P W)) :
    (run c k waiting commands).resolved.toList
        = ((waiting.toList ++ commands.filterMap Command.idle?).filter
            fun w => (run c k waiting commands).kernel.quiet w.1).map (·.2)
      ∧ (run c k waiting commands).waiting.toList
        = (waiting.toList ++ commands.filterMap Command.idle?).filter
            fun w => !(run c k waiting commands).kernel.quiet w.1 := by
  have hf := waiting_foldl c commands (k, { waiting })
  simp only [run, finish]
  generalize commands.foldl (scan c) (k, { waiting }) = ks at hf
  have hw : (flush (if ks.2.worked then ks else work c none ks)).2.waiting = ks.2.waiting := by
    rw [waiting_flush]; split
    · rfl
    · exact waiting_work c none ks
  generalize flush (if ks.2.worked then ks else work c none ks) = f at hw
  obtain ⟨k', s⟩ := f
  simp only at hw
  constructor <;> simp only [Array.toList_map, Array.toList_filter, hw, hf]

private theorem workAll_spread (c : Config) (spread : Kernel.Spread) :
    workAll (sys := sys) (P := P) (W := W) { c with spread } = workAll c := by
  funext xs ks
  unfold workAll
  congr 1
  funext k
  rw [turnAll_spread, turnAll_spread (spread := c.spread)]

private theorem scan_spread (c : Config) (spread : Kernel.Spread) :
    scan (sys := sys) (P := P) (W := W) { c with spread } = scan c := by
  funext ks command
  cases command with
  | inputs xs => simp only [scan, workAll_spread]
  | _ => rfl

/-- How the waves of a batch are spread over threads changes nothing it does: the same kernel,
the same acts, the same answers (`turnAll_spread`, from `Kernel.runWaves_eq`). So the shell may
choose the spread of each batch as it likes, from its own timing. -/
theorem run_spread (c : Config) (spread : Kernel.Spread) (k : Kernel sys)
    (waiting : Array (Bool × W)) (commands : List (Command σ P W)) :
    run { c with spread } k waiting commands = run c k waiting commands := by
  simp only [run, scan_spread]
  rfl

end Lanes.Batch
