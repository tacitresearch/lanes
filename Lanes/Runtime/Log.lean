/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Runtime.KernelSound
public import Lanes.Runtime.Wave

/-!
The log of a shard: everything it asks of its kernel, in order. The kernel is a pure function
of those requests, so replaying a log gives back the state it describes, and that is how a
shard survives its process (`docs/decisions/` D24).

This file is what an entry is and what it asks of the kernel: `recover` rebuilds the kernel
the entries describe (`recover_kernel`), `resume` does so from a saved kernel
(`resume_eq_recover`), and `turn` is one turn of a shard and the entries it writes
(`turn_eq_exec`). The journal's bytes and files are durability's (`Lanes/Durable/Journal.lean`);
the runtime needs only this part, and runs with no journal at all.
-/

@[expose] public section

namespace Lanes.Journal

variable {σ : Signature}

/-- One thing a shard asked of its kernel: an input, a clock reading, a batch of work, or a
mark. Replaying the entries rebuilds the kernel (`Journal.recover_kernel`). -/
inductive Entry (σ : Signature) where
  | input (x : σ.In)
  | advance (now_ms : Nat)
  | batch (fuel : Nat)
  /-- Every output produced so far has been handed over. After a restart, only the outputs
  after the last such mark are handed over again. -/
  | handed
  /-- The kernel was saved here, `index` entries into the shard's history, and every output
  produced so far had been handed over. The entries before this one are then no longer needed,
  and a journal file may have lost them. -/
  | snapshot (index : Nat)

/-! Recovery: replay the entries through the kernel. -/

variable [Hashable σ.Id]

def Entry.op? : Entry σ → Option (Kernel.Op σ)
  | .input x => some (.input x)
  | .advance now_ms => some (.advance now_ms)
  | .batch fuel => some (.batch fuel)
  | .handed => none
  | .snapshot _ => some .snapshot

/-- Whether the entry says that every output so far has been handed over. -/
def Entry.marks : Entry σ → Bool
  | .handed | .snapshot _ => true
  | _ => false

def ops (entries : List (Entry σ)) : List (Kernel.Op σ) :=
  entries.filterMap Entry.op?

/-- One entry replayed: the kernel after it, and the outputs not yet known to be handed over. -/
def replay1 {sys : System σ} (acc : Kernel sys × List σ.Out) (entry : Entry σ) :
    Kernel sys × List σ.Out :=
  match acc, entry with
  | (k, _), .handed => (k, [])
  | (k, _), .snapshot _ => (k.image.kernel, [])
  | (k, pending), .advance now_ms => (k.advance now_ms, pending)
  | (k, pending), .input x =>
    match k.accept x with
    | { kernel, outputs, .. } => (kernel, pending ++ outputs)
  | (k, pending), .batch fuel =>
    match k.runBatch fuel with
    | { kernel, outputs, .. } => (kernel, pending ++ outputs)

/-- The kernel a journal describes, and the outputs to hand over again: those produced after
the last `handed` mark. -/
def recover (sys : System σ) (past : List (Entry σ)) : Kernel sys × List σ.Out :=
  past.foldl replay1 (Kernel.boot sys)

/-- `recover` from another start than boot: a kernel and the outputs it has not handed over. A
shard whose kernel was migrated from an older system's starts there (`Lanes.Migration`). -/
def replay {sys : System σ} (start : Kernel sys × List σ.Out) (past : List (Entry σ)) :
    Kernel sys × List σ.Out :=
  past.foldl replay1 start

theorem replay1_handed {sys : System σ} (k : Kernel sys) (pending : List σ.Out) :
    replay1 (k, pending) .handed = (k, []) := rfl

theorem replay1_snapshot {sys : System σ} (k : Kernel sys) (pending : List σ.Out) (index : Nat) :
    replay1 (k, pending) (.snapshot index) = (k.image.kernel, []) := rfl

theorem replay1_advance {sys : System σ} (k : Kernel sys) (pending : List σ.Out) (now_ms : Nat) :
    replay1 (k, pending) (.advance now_ms) = (k.advance now_ms, pending) := rfl

theorem replay1_input {sys : System σ} (k : Kernel sys) (pending : List σ.Out) (x : σ.In) :
    replay1 (k, pending) (.input x) = ((k.accept x).kernel, pending ++ (k.accept x).outputs) := rfl

theorem replay1_batch {sys : System σ} (k : Kernel sys) (pending : List σ.Out) (fuel : Nat) :
    replay1 (k, pending) (.batch fuel)
      = ((k.runBatch fuel).kernel, pending ++ (k.runBatch fuel).outputs) := rfl

private theorem foldl_replay1 {sys : System σ} (past : List (Entry σ)) (k : Kernel sys)
    (pending : List σ.Out) :
    (past.foldl replay1 (k, pending)).1 = (k.exec (ops past)).kernel
      ∧ ∃ handed, pending ++ (k.exec (ops past)).outputs
          = handed ++ (past.foldl replay1 (k, pending)).2 := by
  induction past generalizing k pending with
  | nil => exact ⟨rfl, [], by simp [ops, Kernel.exec]⟩
  | cons entry past ih =>
    cases entry with
    | handed =>
      obtain ⟨hk, handed, hout⟩ := ih k []
      rw [List.foldl_cons, replay1_handed]
      refine ⟨hk, pending ++ handed, ?_⟩
      simp only [List.nil_append] at hout
      simp only [ops, List.filterMap_cons, Entry.op?] at hout ⊢
      rw [List.append_assoc, ← hout]
    | snapshot index =>
      obtain ⟨hk, handed, hout⟩ := ih k.image.kernel []
      rw [List.foldl_cons, replay1_snapshot]
      refine ⟨by simpa [ops, Entry.op?, Kernel.exec_cons, Kernel.apply] using hk,
        pending ++ handed, ?_⟩
      simp only [List.nil_append] at hout
      simp only [ops, List.filterMap_cons, Entry.op?, Kernel.exec_cons, Kernel.apply,
        List.nil_append] at hout ⊢
      rw [List.append_assoc, ← hout]
    | advance now_ms =>
      obtain ⟨hk, handed, hout⟩ := ih (k.advance now_ms) pending
      rw [List.foldl_cons, replay1_advance]
      refine ⟨by simpa [ops, Entry.op?, Kernel.exec_cons, Kernel.apply] using hk, handed, ?_⟩
      simpa [ops, Entry.op?, Kernel.exec_cons, Kernel.apply] using hout
    | input x =>
      obtain ⟨hk, handed, hout⟩ := ih (k.accept x).kernel (pending ++ (k.accept x).outputs)
      rw [List.foldl_cons, replay1_input]
      refine ⟨by simpa [ops, Entry.op?, Kernel.exec_cons, Kernel.apply] using hk, handed, ?_⟩
      simpa [ops, Entry.op?, Kernel.exec_cons, Kernel.apply, List.append_assoc] using hout
    | batch fuel =>
      obtain ⟨hk, handed, hout⟩ := ih (k.runBatch fuel).kernel
        (pending ++ (k.runBatch fuel).outputs)
      rw [List.foldl_cons, replay1_batch]
      refine ⟨by simpa [ops, Entry.op?, Kernel.exec_cons, Kernel.apply] using hk, handed, ?_⟩
      simpa [ops, Entry.op?, Kernel.exec_cons, Kernel.apply, List.append_assoc] using hout

/-- Recovery rebuilds exactly the kernel that the journal's requests lead to from boot. By
`Kernel.exec_reachable` that is a state the semantics reaches by the events those requests
reported, with actors at rest released: the run before the crash, continued. -/
theorem recover_kernel (sys : System σ) (past : List (Entry σ)) :
    (recover sys past).1 = ((Kernel.boot sys).1.exec (ops past)).kernel :=
  (foldl_replay1 past (Kernel.boot sys).1 (Kernel.boot sys).2).1

/-- Replaying from any kernel gives the kernel the entries' requests lead to from it. -/
theorem replay_kernel {sys : System σ} (start : Kernel sys × List σ.Out) (past : List (Entry σ)) :
    (replay start past).1 = (start.1.exec (ops past)).kernel :=
  (foldl_replay1 past start.1 start.2).1

/-- What is handed over again after a restart is the tail of what the run produced: nothing is
invented and nothing is out of order. -/
theorem recover_outputs (sys : System σ) (past : List (Entry σ)) :
    ∃ handed, (Kernel.boot sys).2 ++ ((Kernel.boot sys).1.exec (ops past)).outputs
      = handed ++ (recover sys past).2 :=
  (foldl_replay1 past (Kernel.boot sys).1 (Kernel.boot sys).2).2

/-- Replaying entries with no mark among them keeps every output they produce. -/
theorem replay_unmarked {sys : System σ} (k : Kernel sys) (pending : List σ.Out)
    {rest : List (Entry σ)} (h : ∀ entry ∈ rest, entry.marks = false) :
    rest.foldl replay1 (k, pending)
      = ((k.exec (ops rest)).kernel, pending ++ (k.exec (ops rest)).outputs) := by
  induction rest generalizing k pending with
  | nil => simp [ops, Kernel.exec]
  | cons entry rest ih =>
    have hrest := fun e he => h e (List.mem_cons_of_mem _ he)
    cases entry with
    | handed => simpa [Entry.marks] using h .handed List.mem_cons_self
    | snapshot index => simpa [Entry.marks] using h (.snapshot index) List.mem_cons_self
    | advance now_ms =>
      rw [List.foldl_cons, replay1_advance, ih _ _ hrest]
      simp [ops, Entry.op?, Kernel.exec_cons, Kernel.apply]
    | input x =>
      rw [List.foldl_cons, replay1_input, ih _ _ hrest]
      simp [ops, Entry.op?, Kernel.exec_cons, Kernel.apply, List.append_assoc]
    | batch fuel =>
      rw [List.foldl_cons, replay1_batch, ih _ _ hrest]
      simp [ops, Entry.op?, Kernel.exec_cons, Kernel.apply, List.append_assoc]

/-- What is handed over again after a restart is exactly what was produced after the last
`handed` mark: nothing from before it, and everything since. So an output that was produced and
not marked is never lost, and one that was marked is never repeated. -/
theorem recover_handed (sys : System σ) (past : List (Entry σ)) {rest : List (Entry σ)}
    (h : ∀ entry ∈ rest, entry.marks = false) :
    (recover sys (past ++ .handed :: rest)).2
      = ((recover sys past).1.exec (ops rest)).outputs := by
  rw [recover, List.foldl_append, List.foldl_cons, ← recover]
  obtain ⟨k, pending⟩ := recover sys past
  rw [replay1_handed, replay_unmarked k [] h]
  rfl

/-! Recovery from a saved kernel. The snapshot is a memo of the replay up to its mark, and
`resume_eq_recover` is the theorem that says so. -/

def Entry.savedAt : Entry σ → Option Nat
  | .snapshot index => some index
  | _ => none

/-- The entries after the mark of the snapshot taken at `index`. -/
def since (index : Nat) : List (Entry σ) → Option (List (Entry σ))
  | [] => none
  | entry :: rest => if entry.savedAt = some index then some rest else since index rest

/--
The kernel to start with, given the saved kernel if there is one and the entries in the journal
file. `none` means the two do not belong together, and the shard must not start: the file
begins with the mark of a snapshot that is not there, so its earlier entries are gone, or the
snapshot's mark is not in the file.
-/
def resume (sys : System σ) (saved : Option (Nat × Kernel.Image sys)) (past : List (Entry σ)) :
    Option (Kernel sys × List σ.Out) :=
  match saved, past with
  | none, .snapshot (_ + 1) :: _ => none
  | none, past => some (recover sys past)
  | some (index, image), past =>
    (since index past).map fun rest => rest.foldl replay1 (image.kernel, [])

omit [Hashable σ.Id] in
private theorem since_append (index : Nat) {before : List (Entry σ)} (rest : List (Entry σ))
    (h : ∀ entry ∈ before, entry.savedAt ≠ some index) :
    since index (before ++ .snapshot index :: rest) = some rest := by
  induction before with
  | nil => simp [since, Entry.savedAt]
  | cons entry before ih =>
    rw [List.cons_append, since]
    simp only [h entry List.mem_cons_self, ↓reduceIte]
    exact ih fun e he => h e (List.mem_cons_of_mem _ he)

/-- `resume_eq_recover` for a history that starts anywhere: the snapshot holds the kernel as
it was after `before`, replayed from `start`. -/
theorem resume_eq_replay (sys : System σ) (start : Kernel sys × List σ.Out)
    (before rest : List (Entry σ)) (index lost : Nat)
    (h : ∀ entry ∈ before, entry.savedAt ≠ some index) :
    resume sys (some (index, (replay start before).1.image))
        (before.drop lost ++ .snapshot index :: rest)
      = some (replay start (before ++ .snapshot index :: rest)) := by
  have hsince := since_append index (before := before.drop lost) rest fun e he =>
    h e (List.mem_of_mem_drop he)
  simp only [resume, hsince, Option.map_some, replay, List.foldl_append, List.foldl_cons]
  generalize before.foldl replay1 start = acc
  obtain ⟨k, pending⟩ := acc
  rfl

/--
Starting from a snapshot gives exactly what replaying the whole history gives: the same kernel
and the same outputs to hand over again. The history is `before`, the mark, then `rest`; the
snapshot holds the kernel as it was after `before`; and the file may have lost any number of
the entries before the mark, which is what cutting a journal does.
-/
theorem resume_eq_recover (sys : System σ) (before rest : List (Entry σ)) (index lost : Nat)
    (h : ∀ entry ∈ before, entry.savedAt ≠ some index) :
    resume sys (some (index, (recover sys before).1.image))
        (before.drop lost ++ .snapshot index :: rest)
      = some (recover sys (before ++ .snapshot index :: rest)) :=
  resume_eq_replay sys (Kernel.boot sys) before rest index lost h

/-! One turn of a shard, as a pure function: everything the shell asks of the kernel between two
looks at its inbox, and what it must write in the journal for it. -/

structure Turn (sys : System σ) where
  kernel : Kernel sys
  events : List (Event σ) := []
  outputs : List σ.Out := []
  entries : List (Entry σ) := []

/--
Take an input if there is one and do up to `fuel` units of work at time `now_ms`. If there is
no input and nothing to do yet, the kernel is left exactly as it was, clock included, and
nothing is journaled: so the journal always describes the kernel (`turn_eq_exec`).
-/
def turn {sys : System σ} (k : Kernel sys) (now_ms : Nat) (input : Option σ.In) (fuel : Nat) :
    Turn sys :=
  if input.isNone && (k.advance now_ms).wait != .none then { kernel := k }
  else
    let k := k.advance now_ms
    let clock := k.clock_ms
    match input with
    | none =>
      match k.runBatch fuel with
      | { kernel, events, outputs } =>
        { kernel, events, outputs, entries := [.advance clock, .batch fuel] }
    | some x =>
      match k.accept x with
      | { kernel, events := accepted, .. } =>
        match kernel.runBatch fuel with
        | { kernel, events, outputs } =>
          { kernel, events := accepted ++ events, outputs
            entries := [.advance clock, .input x, .batch fuel] }

private theorem advance_clock {sys : System σ} (k : Kernel sys) (now_ms : Nat) :
    k.advance (k.advance now_ms).clock_ms = k.advance now_ms := by
  simp only [Kernel.advance]
  congr 1
  omega

/-- What a turn does is what replaying its journal entries does: the same kernel, the same
events, the same outputs. Nothing is assumed of the clock. -/
theorem turn_eq_exec {sys : System σ} (k : Kernel sys) (now_ms : Nat) (input : Option σ.In)
    (fuel : Nat) :
    (turn k now_ms input fuel).kernel = (k.exec (ops (turn k now_ms input fuel).entries)).kernel
      ∧ (turn k now_ms input fuel).events
          = (k.exec (ops (turn k now_ms input fuel).entries)).events
      ∧ (turn k now_ms input fuel).outputs
          = (k.exec (ops (turn k now_ms input fuel).entries)).outputs := by
  unfold turn
  split
  · exact ⟨rfl, rfl, rfl⟩
  · cases input with
    | none =>
      simp [ops, Entry.op?, Kernel.exec_cons, Kernel.apply, Kernel.exec, advance_clock]
    | some x =>
      simp [ops, Entry.op?, Kernel.exec_cons, Kernel.apply, Kernel.exec, advance_clock,
        Kernel.accept]

/-- `turn` for inputs that arrived together: each is accepted, in order, and then up to `fuel`
units of work are done, the steps of different actors worked out as `spread` says
(`Kernel.runWaves`, which is `runBatch`). The journal has `advance`, the inputs and one `batch`. -/
def turnAll {sys : System σ} (k : Kernel sys) (now_ms : Nat) (inputs : List σ.In)
    (fuel : Nat) (spread : Kernel.Spread) : Turn sys :=
  if inputs.isEmpty && (k.advance now_ms).wait != .none then { kernel := k }
  else
    let k := k.advance now_ms
    let clock := k.clock_ms
    match (k.acceptAll inputs).runWaves spread fuel with
    | { kernel, events, outputs } =>
      { kernel, events := inputs.map .input ++ events, outputs
        entries := .advance clock :: inputs.map .input ++ [.batch fuel] }

theorem turnAll_eq_exec {sys : System σ} (k : Kernel sys) (now_ms : Nat) (inputs : List σ.In)
    (fuel : Nat) (spread : Kernel.Spread) :
    (turnAll k now_ms inputs fuel spread).kernel
        = (k.exec (ops (turnAll k now_ms inputs fuel spread).entries)).kernel
      ∧ (turnAll k now_ms inputs fuel spread).events
          = (k.exec (ops (turnAll k now_ms inputs fuel spread).entries)).events
      ∧ (turnAll k now_ms inputs fuel spread).outputs
          = (k.exec (ops (turnAll k now_ms inputs fuel spread).entries)).outputs := by
  unfold turnAll
  split
  · exact ⟨rfl, rfl, rfl⟩
  · have hops : ∀ c : Nat, ops (.advance c :: inputs.map Entry.input ++ [.batch fuel])
        = .advance c :: (inputs.map Kernel.Op.input ++ [.batch fuel]) := by
      intro c
      simp [ops, Entry.op?, List.filterMap_append, List.filterMap_map, Function.comp_def]
    simp only [hops, Kernel.exec_cons, Kernel.exec_append, Kernel.exec_inputs, Kernel.runWaves_eq,
      Kernel.apply, advance_clock]
    simp [Kernel.exec]

/-- How a turn's waves are spread does not change the turn (`Kernel.runWaves_eq`). -/
theorem turnAll_spread {sys : System σ} (k : Kernel sys) (now_ms : Nat) (inputs : List σ.In)
    (fuel : Nat) (spread : Kernel.Spread) :
    turnAll k now_ms inputs fuel spread = turnAll k now_ms inputs fuel {} := by
  unfold turnAll
  simp only [Kernel.runWaves_eq]

/-- Turn after turn, with the entries each one journals. -/
def turns {sys : System σ} (k : Kernel sys) (fuel : Nat) :
    List (Nat × Option σ.In) → Kernel sys × List (Entry σ)
  | [] => (k, [])
  | (now_ms, input) :: rest =>
    match turn k now_ms input fuel with
    | { kernel, entries, .. } =>
      match turns kernel fuel rest with
      | (kernel, later) => (kernel, entries ++ later)

/-- However many turns a shard takes, at whatever times and with whatever inputs, its kernel is
the one its journal describes. So what `recover` rebuilds after the process dies is the kernel
the shard had when it last finished writing. -/
theorem turns_kernel {sys : System σ} (k : Kernel sys) (fuel : Nat)
    (steps : List (Nat × Option σ.In)) :
    (turns k fuel steps).1 = (k.exec (ops (turns k fuel steps).2)).kernel := by
  induction steps generalizing k with
  | nil => rfl
  | cons step steps ih =>
    obtain ⟨now_ms, input⟩ := step
    have hturn := (turn_eq_exec k now_ms input fuel).1
    show (turns (turn k now_ms input fuel).kernel fuel steps).1
      = (k.exec (ops ((turn k now_ms input fuel).entries
          ++ (turns (turn k now_ms input fuel).kernel fuel steps).2))).kernel
    simp only [ops] at hturn ih ⊢
    rw [ih, List.filterMap_append, Kernel.exec_append, ← hturn]

end Lanes.Journal
