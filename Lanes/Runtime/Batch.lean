/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Durable.OutputId
public import Lanes.Proof.List

/-!
What a shard does with everything it takes from its inbox at once, as a pure function: the
turns it asks of the kernel, and the acts the shell is to perform for them, in order. The shell
(`Lanes.Runtime`) performs them and decides nothing.

Of every batch: the journal describes the kernel (`run_kernel`); an output is handed over only
once the entries that produce it are appended, a save falls where every output produced has
been handed over, and a peek sees the kernel the journal describes (`run_sound`); a peek sees
every input before it and none after (`run_peek`); who waits for the shard to be idle is
answered when the kernel is quiet (`run_resolved`). Each output is handed over with its origin
in the history the batch writes (`run_ids`), however its waves are spread (`run_ids_spread`).

The reply handles are opaque: `P i` answers a peek at actor `i` and `W` an idle, as `W` wakes a
sleeper in `Mailbox`.
-/

@[expose] public section

namespace Lanes.Batch

variable {σ : Signature}

inductive Command (σ : Signature) (P : σ.Id → Type) (W : Type) where
  | input (x : σ.In)
  /-- Inputs that arrived together, accepted in order before any work is done for them, so that
  the actors they reach can step in parallel (`Journal.turnAll`). -/
  | inputs (xs : List σ.In)
  | idle (timers : Bool) (waiter : W)
  | peek (i : σ.Id) (reply : P i)

inductive Act (sys : System σ) (P : σ.Id → Type) where
  | append (entries : Array (Journal.Entry σ))
  | record (events : Array (Event σ))
  /-- Hand these outputs over, each with its origin, then note a `handed` mark. -/
  | handOver (outputs : Array (Journal.Origin × σ.Out))
  /-- Save this image of the kernel. The kernel goes on as the image restores it. -/
  | save (image : Kernel.Image sys)
  | answer (i : σ.Id) (reply : P i) (state : sys.State i)

structure Config where
  now_ms : Nat
  /-- How many entries the shard's history has before the batch, so where the origins of its
  outputs start. -/
  index : Nat := 0
  fuel : Nat
  /-- How many entries to write between two saves, if the journal can save. -/
  snapshotEvery : Option Nat
  /-- How the steps of a wave of `inputs` are spread over threads (`Kernel.runWaves`). It does
  not change the batch (`run_spread`). -/
  spread : Kernel.Spread := {}

/-- The shard's part of a batch so far, besides its kernel. -/
structure Scan (sys : System σ) (P : σ.Id → Type) (W : Type) where
  /-- Entries written since the last save. -/
  written : Nat
  waiting : Array (Bool × W)
  acts : Array (Act sys P) := #[]
  entries : Array (Journal.Entry σ) := #[]
  events : Array (Event σ) := #[]
  outputs : Array (Journal.Origin × σ.Out) := #[]
  worked : Bool := false

structure Result (sys : System σ) [Hashable σ.Id] (P : σ.Id → Type) (W : Type) where
  kernel : Kernel sys
  written : Nat
  acts : Array (Act sys P)
  resolved : Array W
  waiting : Array (Bool × W)

variable {sys : System σ} {P : σ.Id → Type} {W : Type}

def due (c : Config) (written : Nat) : Bool :=
  c.snapshotEvery.any fun n => max 1 n ≤ written

def put (acts : Array (Act sys P)) (skip : Bool) (act : Act sys P) : Array (Act sys P) :=
  if skip then acts else acts.push act

/-- What an act adds to the shard's history, an entry each, as requests of the kernel: the
entries it appends, the `handed` mark the shell notes after a hand-over, the mark of a save. -/
def Act.steps : Act sys P → List (Option (Kernel.Op σ))
  | .append entries => Journal.steps entries.toList
  | .handOver outputs => if outputs.isEmpty then [] else [none]
  | .save _ => [some .snapshot]
  | _ => []

def history (acts : List (Act sys P)) : List (Option (Kernel.Op σ)) := acts.flatMap Act.steps

/-- How many entries an act adds to the history. -/
def Act.grows : Act sys P → Nat
  | .append entries => entries.size
  | .handOver outputs => if outputs.isEmpty then 0 else 1
  | .save _ => 1
  | _ => 0

/-- How many entries acts add to the history: `(history acts).length` (`grown_eq`). -/
def grown (acts : Array (Act sys P)) : Nat :=
  acts.foldl (init := 0) fun n act => n + act.grows

variable [Hashable σ.Id]

/-- A turn, kept back to be written with the turns after it. Its outputs are all its last
entry's (`Journal.turn_placed`), so their origin is where that entry falls in the history. -/
def workWith (index : Nat) (turn : Kernel sys → Journal.Turn sys) :
    Kernel sys × Scan sys P W → Kernel sys × Scan sys P W
  | (k, ⟨written, waiting, acts, entries, events, outputs, _⟩) =>
    match turn k with
    | { kernel, events := more, outputs := out, entries := new } =>
      (kernel, { written, waiting, acts, entries := entries ++ new
                 events := events ++ more
                 outputs := outputs ++ Journal.tag (index + grown acts + entries.size + new.length) out
                 worked := true })

def work (c : Config) (input : Option σ.In) : Kernel sys × Scan sys P W → Kernel sys × Scan sys P W :=
  workWith c.index fun k => Journal.turn k c.now_ms input c.fuel

/-- The turn of inputs that arrived together, with `fuel` for each. -/
def workAll (c : Config) (xs : List σ.In) : Kernel sys × Scan sys P W → Kernel sys × Scan sys P W :=
  workWith c.index fun k => Journal.turnAll k c.now_ms xs (c.fuel * max 1 xs.length) c.spread

/-- Write what was kept back, and save if that many entries are due. -/
def flush (c : Config) : Kernel sys × Scan sys P W → Kernel sys × Scan sys P W
  | (k, ⟨written, waiting, acts, entries, events, outputs, worked⟩) =>
    let written := written + entries.size
    let acts := put (put (put acts entries.isEmpty (.append entries)) events.isEmpty
      (.record events)) outputs.isEmpty (.handOver outputs)
    if due c written then
      match k.image with
      | image => (image.kernel, { written := 0, waiting, acts := acts.push (.save image), worked })
    else (k, { written, waiting, acts, worked })

def scan (c : Config) (ks : Kernel sys × Scan sys P W) :
    Command σ P W → Kernel sys × Scan sys P W
  | .input x =>
    match work c (some x) ks with
    | (k, s) => if due c (s.written + s.entries.size) then flush c (k, s) else (k, s)
  | .inputs xs =>
    match workAll c xs ks with
    | (k, s) => if due c (s.written + s.entries.size) then flush c (k, s) else (k, s)
  | .idle timers waiter =>
    match flush c ks with
    | (k, s) => (k, { s with waiting := s.waiting.push (timers, waiter) })
  | .peek i reply =>
    match flush c ks with
    | (k, s) => (k, { s with acts := s.acts.push (.answer i reply (k.cell i).state) })

def finish (c : Config) (ks : Kernel sys × Scan sys P W) : Result sys P W :=
  match flush c (if ks.2.worked then ks else work c none ks) with
  | (k, s) =>
    { kernel := k, written := s.written, acts := s.acts
      resolved := (s.waiting.filter fun w => k.quiet w.1).map (·.2)
      waiting := s.waiting.filter fun w => !k.quiet w.1 }

/-- Inputs next to each other as one command, so that they are accepted together, at most `most`
to a command: a turn's entries are written together, so a save is put off by at most a turn. -/
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
    | peek i reply => simp only [group, List.flatMap_cons, ih]

/-- One batch: a turn for each input, at one time; when no input came, one turn without. -/
def run (c : Config) (k : Kernel sys) (written : Nat) (waiting : Array (Bool × W))
    (commands : List (Command σ P W)) : Result sys P W :=
  finish c (commands.foldl (scan c) (k, { written, waiting }))

/-! What the acts amount to. A save is written as a `snapshot` mark, whatever its index. -/

def Act.ops : Act sys P → List (Kernel.Op σ)
  | .append entries => Journal.ops entries.toList
  | .save _ => [.snapshot]
  | _ => []

def Act.outputs : Act sys P → List σ.Out
  | .handOver outputs => outputs.toList.map Prod.snd
  | _ => []

def Act.placed : Act sys P → List (Journal.Origin × σ.Out)
  | .handOver outputs => outputs.toList
  | _ => []

def Act.events : Act sys P → List (Event σ)
  | .record events => events.toList
  | _ => []

def journal (acts : List (Act sys P)) : List (Kernel.Op σ) := acts.flatMap Act.ops

def handed (acts : List (Act sys P)) : List σ.Out := acts.flatMap Act.outputs

/-- The outputs handed over, each with its origin. -/
def handedIds (acts : List (Act sys P)) : List (Journal.Origin × σ.Out) := acts.flatMap Act.placed

def recorded (acts : List (Act sys P)) : List (Event σ) := acts.flatMap Act.events

/-- What an act may do after `before`, from kernel `k`: hand over or record exactly what the
journal so far produced and was not yet handed over or recorded, save the kernel the journal
describes once every output it produced is handed over, and answer with that kernel's state. -/
def Act.Sound (k : Kernel sys) (before : List (Act sys P)) : Act sys P → Prop
  | .append _ => True
  | .record events => recorded before ++ events.toList = (k.exec (journal before)).events
  | .handOver outputs =>
    handed before ++ outputs.toList.map Prod.snd = (k.exec (journal before)).outputs
  | .save image =>
    image = (k.exec (journal before)).kernel.image
      ∧ handed before = (k.exec (journal before)).outputs
  | .answer i _ state => state = ((k.exec (journal before)).kernel.cell i).state

def Sound (k : Kernel sys) (acts : List (Act sys P)) : Prop :=
  ∀ before act after, acts = before ++ act :: after → act.Sound k before

def Command.idle? : Command σ P W → Option (Bool × W)
  | .idle timers waiter => some (timers, waiter)
  | _ => none

/-- The commands before a peek, and the acts they leave once what they kept back is written. -/
def settle (c : Config) (k : Kernel sys) (written : Nat) (waiting : Array (Bool × W))
    (before : List (Command σ P W)) : Kernel sys × Scan sys P W :=
  flush c (before.foldl (scan c) (k, { written, waiting }))

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

omit [Hashable σ.Id] in
private theorem ops_empty : Journal.ops (#[] : Array (Journal.Entry σ)).toList = [] := rfl

omit [Hashable σ.Id] in
private theorem ops_nil : Journal.ops ([] : List (Journal.Entry σ)) = [] := rfl

private structure Inv (k0 : Kernel sys) (ks : Kernel sys × Scan sys P W) : Prop where
  kernel : ks.1 = (k0.exec (journal ks.2.acts.toList ++ Journal.ops ks.2.entries.toList)).kernel
  outputs : handed ks.2.acts.toList ++ ks.2.outputs.toList.map Prod.snd
    = (k0.exec (journal ks.2.acts.toList ++ Journal.ops ks.2.entries.toList)).outputs
  events : recorded ks.2.acts.toList ++ ks.2.events.toList
    = (k0.exec (journal ks.2.acts.toList ++ Journal.ops ks.2.entries.toList)).events
  sound : Sound k0 ks.2.acts.toList

private theorem inv_start (k : Kernel sys) (written : Nat) (waiting : Array (Bool × W)) :
    Inv k (k, ({ written, waiting } : Scan sys P W)) where
  kernel := rfl
  outputs := rfl
  events := rfl
  sound := fun before act after h => by simp at h

private theorem inv_workWith (index : Nat) (turn : Kernel sys → Journal.Turn sys)
    (hturn : ∀ k, (turn k).kernel = (k.exec (Journal.ops (turn k).entries)).kernel
      ∧ (turn k).events = (k.exec (Journal.ops (turn k).entries)).events
      ∧ (turn k).outputs = (k.exec (Journal.ops (turn k).entries)).outputs) {k0 : Kernel sys}
    {ks : Kernel sys × Scan sys P W} (h : Inv k0 ks) : Inv k0 (workWith index turn ks) := by
  obtain ⟨k, ⟨written, waiting, acts, entries, events, outputs, worked⟩⟩ := ks
  obtain ⟨hk, ho, he, hs⟩ := h
  obtain ⟨tk, te, to⟩ := hturn k
  simp only at hk ho he hs
  have hexec : ∀ more : List (Journal.Entry σ),
      k0.exec (journal acts.toList ++ Journal.ops (entries.toList ++ more))
        = { kernel := (k.exec (Journal.ops more)).kernel
            events := (k0.exec (journal acts.toList ++ Journal.ops entries.toList)).events
              ++ (k.exec (Journal.ops more)).events
            outputs := (k0.exec (journal acts.toList ++ Journal.ops entries.toList)).outputs
              ++ (k.exec (Journal.ops more)).outputs } := by
    intro more
    rw [Journal.ops, List.filterMap_append, ← List.append_assoc, Kernel.exec_append, ← Journal.ops,
      ← Journal.ops, ← hk]
  refine ⟨?_, ?_, ?_, hs⟩ <;>
    simp only [workWith, Array.toList_appendList, List.map_append,
      Journal.tag_snd, hexec, ← tk, ← te, ← to, ← ho, ← he, List.append_assoc]

private theorem inv_work (c : Config) (input : Option σ.In) {k0 : Kernel sys}
    {ks : Kernel sys × Scan sys P W} (h : Inv k0 ks) : Inv k0 (work c input ks) :=
  inv_workWith _ _ (fun k => Journal.turn_eq_exec k c.now_ms input c.fuel) h

private theorem inv_workAll (c : Config) (xs : List σ.In) {k0 : Kernel sys}
    {ks : Kernel sys × Scan sys P W} (h : Inv k0 ks) : Inv k0 (workAll c xs ks) :=
  inv_workWith _ _ (fun k => Journal.turnAll_eq_exec k c.now_ms xs _ c.spread) h

private theorem inv_flush (c : Config) {k0 : Kernel sys} {ks : Kernel sys × Scan sys P W}
    (h : Inv k0 ks) :
    Inv k0 (flush c ks) ∧ (flush c ks).2.entries = #[] ∧ (flush c ks).2.events = #[]
      ∧ (flush c ks).2.outputs = #[] := by
  obtain ⟨k, ⟨written, waiting, acts, entries, events, outputs, worked⟩⟩ := ks
  obtain ⟨hk, ho, he, hs⟩ := h
  simp only at hk ho he hs
  generalize hx : k0.exec (journal acts.toList ++ Journal.ops entries.toList) = x at hk ho he
  let a1 := put acts entries.isEmpty (.append entries)
  let a2 := put a1 events.isEmpty (.record events)
  let a3 := put a2 outputs.isEmpty (.handOver outputs)
  have j1 : journal a1.toList = journal acts.toList ++ Journal.ops entries.toList := by
    simp only [a1, toList_put]; split <;> simp_all [journal, Act.ops, Journal.ops]
  have r1 : recorded a1.toList = recorded acts.toList := by
    simp only [a1, toList_put]; split <;> simp [recorded, Act.events]
  have h1 : handed a1.toList = handed acts.toList := by
    simp only [a1, toList_put]; split <;> simp [handed, Act.outputs]
  have s1 : Sound k0 a1.toList := by
    simp only [a1, toList_put]; split
    · exact hs
    · exact sound_push hs trivial
  have j2 : journal a2.toList = journal a1.toList := by
    simp only [a2, toList_put]; split <;> simp [journal, Act.ops]
  have r2 : recorded a2.toList = recorded acts.toList ++ events.toList := by
    simp only [a2, toList_put]; split <;> simp_all [recorded, Act.events]
  have h2 : handed a2.toList = handed acts.toList := by
    rw [← h1]; simp only [a2, toList_put]; split <;> simp [handed, Act.outputs]
  have s2 : Sound k0 a2.toList := by
    simp only [a2, toList_put]; split
    · exact s1
    · exact sound_push s1 (by simp only [Act.Sound, r1, j1, hx, he])
  have j3 : journal a3.toList = journal acts.toList ++ Journal.ops entries.toList := by
    rw [← j1, ← j2]; simp only [a3, toList_put]; split <;> simp [journal, Act.ops]
  have r3 : recorded a3.toList = recorded acts.toList ++ events.toList := by
    rw [← r2]; simp only [a3, toList_put]; split <;> simp [recorded, Act.events]
  have h3 : handed a3.toList = handed acts.toList ++ outputs.toList.map Prod.snd := by
    simp only [a3, toList_put]; split <;> simp_all [handed, Act.outputs]
  have s3 : Sound k0 a3.toList := by
    simp only [a3, toList_put]; split
    · exact s2
    · exact sound_push s2 (by simp only [Act.Sound, h2, j2, j1, hx, ho])
  have flushed : flush c (k, ⟨written, waiting, acts, entries, events, outputs, worked⟩)
      = if due c (written + entries.size) then
          (k.image.kernel, { written := 0, waiting, acts := a3.push (.save k.image), worked })
        else (k, { written := written + entries.size, waiting, acts := a3, worked }) := rfl
  have hsave : journal (a3.push (.save k.image)).toList = journal a3.toList ++ [.snapshot] := by
    simp [journal, Act.ops]
  have hsaveh : handed (a3.push (.save k.image)).toList = handed a3.toList := by
    simp [handed, Act.outputs]
  have hsaver : recorded (a3.push (.save k.image)).toList = recorded a3.toList := by
    simp [recorded, Act.events]
  rw [flushed]
  split
  · refine ⟨⟨?_, ?_, ?_, ?_⟩, rfl, rfl, rfl⟩ <;>
      simp only [ops_nil, List.append_nil, hsave, j3]
    · rw [Kernel.exec_append, hx, ← hk]; rfl
    · rw [Kernel.exec_append, hx, ← ho, hsaveh, h3]; simp [Kernel.exec, Kernel.apply]
    · rw [Kernel.exec_append, hx, ← he, hsaver, r3]; simp [Kernel.exec, Kernel.apply]
    · rw [Array.toList_push]
      refine sound_push (act := .save k.image) s3 ?_
      simp only [Act.Sound]
      exact ⟨by rw [j3, hx, hk], by rw [j3, hx, h3, ho]⟩
  · refine ⟨⟨?_, ?_, ?_, s3⟩, rfl, rfl, rfl⟩ <;>
      simp only [ops_nil, List.append_nil, j3, hx]
    · exact hk
    · rw [h3, ho]; simp
    · rw [r3, he]

private theorem inv_scan (c : Config) {k0 : Kernel sys} {ks : Kernel sys × Scan sys P W}
    (h : Inv k0 ks) (command : Command σ P W) : Inv k0 (scan c ks command) := by
  cases command with
  | input x =>
    have hw := inv_work c (some x) h
    simp only [scan]
    generalize work c (some x) ks = w at hw
    obtain ⟨k, s⟩ := w
    split
    · exact (inv_flush c hw).1
    · exact hw
  | inputs xs =>
    have hw := inv_workAll c xs h
    simp only [scan]
    generalize workAll c xs ks = w at hw
    obtain ⟨k, s⟩ := w
    split
    · exact (inv_flush c hw).1
    · exact hw
  | idle timers waiter =>
    obtain ⟨⟨hk, ho, he, hs⟩, -⟩ := inv_flush c h
    exact ⟨hk, ho, he, hs⟩
  | peek i reply =>
    obtain ⟨⟨hk, ho, he, hs⟩, hentries, -⟩ := inv_flush c h
    simp only [scan]
    generalize flush c ks = f at hk ho he hs hentries
    obtain ⟨k, s⟩ := f
    simp only at hk ho he hs hentries
    rw [hentries, ops_empty, List.append_nil] at hk ho he
    have hj : journal (s.acts.toList ++ [Act.answer i reply (k.cell i).state])
        = journal s.acts.toList := by simp [journal, Act.ops]
    have hh : handed (s.acts.toList ++ [Act.answer i reply (k.cell i).state])
        = handed s.acts.toList := by simp [handed, Act.outputs]
    have hr : recorded (s.acts.toList ++ [Act.answer i reply (k.cell i).state])
        = recorded s.acts.toList := by simp [recorded, Act.events]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Array.toList_push, hj, hh, hr, hentries, ops_nil,
      List.append_nil]
    · exact hk
    · exact ho
    · exact he
    · exact sound_push hs (by simp only [Act.Sound, ← hk])

private theorem inv_foldl (c : Config) {k0 : Kernel sys} (commands : List (Command σ P W)) :
    ∀ {ks : Kernel sys × Scan sys P W}, Inv k0 ks → Inv k0 (commands.foldl (scan c) ks) := by
  induction commands with
  | nil => exact id
  | cons command commands ih => exact fun h => ih (inv_scan c h command)

private theorem inv_finish (c : Config) {k0 : Kernel sys} {ks : Kernel sys × Scan sys P W}
    (h : Inv k0 ks) :
    (finish c ks).kernel = (k0.exec (journal (finish c ks).acts.toList)).kernel
      ∧ handed (finish c ks).acts.toList = (k0.exec (journal (finish c ks).acts.toList)).outputs
      ∧ recorded (finish c ks).acts.toList
          = (k0.exec (journal (finish c ks).acts.toList)).events
      ∧ Sound k0 (finish c ks).acts.toList := by
  have hw : Inv k0 (if ks.2.worked then ks else work c none ks) := by
    split
    · exact h
    · exact inv_work c none h
  obtain ⟨⟨hk, ho, he, hs⟩, hentries, hevents, houtputs⟩ := inv_flush c hw
  simp only [finish]
  generalize flush c (if ks.2.worked then ks else work c none ks) = f
    at hk ho he hs hentries hevents houtputs
  obtain ⟨k, s⟩ := f
  simp only at hk ho he hs hentries hevents houtputs
  rw [hentries, ops_empty, List.append_nil] at hk ho he
  rw [houtputs, Array.toList_empty, List.map_nil, List.append_nil] at ho
  rw [hevents, Array.toList_empty, List.append_nil] at he
  exact ⟨hk, ho, he, hs⟩

/-- The journal describes the kernel: the kernel after a batch is the one the entries it
appends and the saves it makes lead to. -/
theorem run_kernel (c : Config) (k : Kernel sys) (written : Nat) (waiting : Array (Bool × W))
    (commands : List (Command σ P W)) :
    (run c k written waiting commands).kernel
      = (k.exec (journal (run c k written waiting commands).acts.toList)).kernel :=
  (inv_finish c (inv_foldl c commands (inv_start k written waiting))).1

/-- By the end of a batch every output its entries produced has been handed over, and every
event recorded. -/
theorem run_handed (c : Config) (k : Kernel sys) (written : Nat) (waiting : Array (Bool × W))
    (commands : List (Command σ P W)) :
    handed (run c k written waiting commands).acts.toList
        = (k.exec (journal (run c k written waiting commands).acts.toList)).outputs
      ∧ recorded (run c k written waiting commands).acts.toList
        = (k.exec (journal (run c k written waiting commands).acts.toList)).events :=
  let h := inv_finish c (inv_foldl c commands (inv_start k written waiting))
  ⟨h.2.1, h.2.2.1⟩

/-- Every act of a batch is sound where it falls. So an output is handed over only after the
entries that produce it are appended, which is what makes it durable; a save falls only where
everything produced has been handed over, as the mark it leaves says; and a peek is answered
with the state of the kernel the journal so far describes. -/
theorem run_sound (c : Config) (k : Kernel sys) (written : Nat) (waiting : Array (Bool × W))
    (commands : List (Command σ P W)) : Sound k (run c k written waiting commands).acts.toList :=
  (inv_finish c (inv_foldl c commands (inv_start k written waiting))).2.2.2

private theorem acts_flush (c : Config) (ks : Kernel sys × Scan sys P W) :
    ks.2.acts.toList <+: (flush c ks).2.acts.toList := by
  obtain ⟨k, ⟨written, waiting, acts, entries, events, outputs, worked⟩⟩ := ks
  have hput : ∀ (a : Array (Act sys P)) skip act, a.toList <+: (put a skip act).toList := by
    intro a skip act
    rw [toList_put]; split
    · exact List.prefix_refl _
    · exact List.prefix_append _ _
  have h3 : acts.toList <+: (put (put (put acts entries.isEmpty (.append entries))
      events.isEmpty (.record events)) outputs.isEmpty (.handOver outputs)).toList :=
    ((hput _ _ _).trans (hput _ _ _)).trans (hput _ _ _)
  simp only [flush]
  split
  · exact h3.trans (by rw [Array.toList_push]; exact List.prefix_append _ _)
  · exact h3

private theorem acts_scan (c : Config) (ks : Kernel sys × Scan sys P W)
    (command : Command σ P W) : ks.2.acts.toList <+: (scan c ks command).2.acts.toList := by
  cases command with
  | input x =>
    have hw : (work c (some x) ks).2.acts = ks.2.acts := by
      obtain ⟨k, ⟨_, _, _, _, _, _, _⟩⟩ := ks; rfl
    simp only [scan]
    rw [← hw]
    generalize work c (some x) ks = w
    obtain ⟨k, s⟩ := w
    split
    · exact acts_flush c (k, s)
    · exact List.prefix_refl _
  | inputs xs =>
    have hw : (workAll c xs ks).2.acts = ks.2.acts := by
      obtain ⟨k, ⟨_, _, _, _, _, _, _⟩⟩ := ks; rfl
    simp only [scan]
    rw [← hw]
    generalize workAll c xs ks = w
    obtain ⟨k, s⟩ := w
    split
    · exact acts_flush c (k, s)
    · exact List.prefix_refl _
  | idle timers waiter => exact acts_flush c ks
  | peek i reply =>
    exact (acts_flush c ks).trans (by simp only [scan, Array.toList_push]; exact List.prefix_append _ _)

private theorem acts_foldl (c : Config) (commands : List (Command σ P W)) :
    ∀ ks : Kernel sys × Scan sys P W,
      ks.2.acts.toList <+: (commands.foldl (scan c) ks).2.acts.toList := by
  induction commands with
  | nil => exact fun _ => List.prefix_refl _
  | cons command commands ih => exact fun ks => (acts_scan c ks command).trans (ih _)

private theorem acts_finish (c : Config) (ks : Kernel sys × Scan sys P W) :
    ks.2.acts.toList <+: (finish c ks).acts.toList := by
  have hw : (if ks.2.worked then ks else work c none ks).2.acts = ks.2.acts := by
    obtain ⟨k, ⟨_, _, _, _, _, _, worked⟩⟩ := ks; cases worked <;> rfl
  have := acts_flush c (if ks.2.worked then ks else work c none ks)
  rw [hw] at this
  exact this

theorem settle_kernel (c : Config) (k : Kernel sys) (written : Nat) (waiting : Array (Bool × W))
    (before : List (Command σ P W)) :
    (settle c k written waiting before).1
      = (k.exec (journal (settle c k written waiting before).2.acts.toList)).kernel := by
  obtain ⟨⟨hk, -⟩, hentries, -⟩ := inv_flush c (inv_foldl c before (inv_start k written waiting))
  rw [settle, hk, hentries, ops_empty, List.append_nil]

/-- A peek is answered after the acts of every command before it, all of them written out,
and before any act of a command after it, with the state of the kernel those leave: by
`settle_kernel`, the kernel the journal so far describes. -/
theorem run_peek (c : Config) (k : Kernel sys) (written : Nat) (waiting : Array (Bool × W))
    (before after : List (Command σ P W)) (i : σ.Id) (reply : P i) :
    ∃ rest, (run c k written waiting (before ++ .peek i reply :: after)).acts.toList
      = (settle c k written waiting before).2.acts.toList
        ++ .answer i reply ((settle c k written waiting before).1.cell i).state :: rest := by
  have hpeek : (scan c (before.foldl (scan c) (k, { written, waiting })) (.peek i reply)).2.acts.toList
      = (settle c k written waiting before).2.acts.toList
        ++ [.answer i reply ((settle c k written waiting before).1.cell i).state] := by
    simp only [scan, settle, Array.toList_push]
  obtain ⟨rest, hrest⟩ := (acts_foldl c after _).trans (acts_finish c _) |>.trans
    (List.prefix_refl _) |> fun h => (hpeek ▸ h : _ <+: _)
  refine ⟨rest, ?_⟩
  rw [run, List.foldl_append, List.foldl_cons, ← hrest, List.append_assoc, List.singleton_append]

private theorem waiting_work (c : Config) (input : Option σ.In) (ks : Kernel sys × Scan sys P W) :
    (work c input ks).2.waiting = ks.2.waiting := by
  obtain ⟨k, ⟨_, _, _, _, _, _, _⟩⟩ := ks; rfl

private theorem waiting_flush (c : Config) (ks : Kernel sys × Scan sys P W) :
    (flush c ks).2.waiting = ks.2.waiting := by
  obtain ⟨k, ⟨_, _, _, _, _, _, _⟩⟩ := ks
  simp only [flush]; split <;> rfl

private theorem waiting_foldl (c : Config) (commands : List (Command σ P W)) :
    ∀ ks : Kernel sys × Scan sys P W, (commands.foldl (scan c) ks).2.waiting.toList
      = ks.2.waiting.toList ++ commands.filterMap Command.idle? := by
  induction commands with
  | nil => simp
  | cons command commands ih =>
    intro ks
    rw [List.foldl_cons, ih, List.filterMap_cons]
    cases command with
    | input x =>
      simp only [scan, Command.idle?]
      have hw := waiting_work c (some x) ks
      generalize work c (some x) ks = w at hw
      obtain ⟨k, s⟩ := w
      split <;> simp [waiting_flush, ← hw]
    | inputs xs =>
      simp only [scan, Command.idle?]
      have hw : (workAll c xs ks).2.waiting = ks.2.waiting := by
        obtain ⟨k, ⟨_, _, _, _, _, _, _⟩⟩ := ks; rfl
      generalize workAll c xs ks = w at hw
      obtain ⟨k, s⟩ := w
      split <;> simp [waiting_flush, ← hw]
    | idle timers waiter => simp [scan, Command.idle?, waiting_flush]
    | peek i reply => simp [scan, Command.idle?, waiting_flush]

/-- Those waiting for the shard to be idle, from before the batch and from its commands in
order, are answered at its end exactly when the kernel is then quiet, with or without timers as
each asked; the others go on waiting. -/
theorem run_resolved (c : Config) (k : Kernel sys) (written : Nat) (waiting : Array (Bool × W))
    (commands : List (Command σ P W)) :
    (run c k written waiting commands).resolved.toList
        = ((waiting.toList ++ commands.filterMap Command.idle?).filter
            fun w => (run c k written waiting commands).kernel.quiet w.1).map (·.2)
      ∧ (run c k written waiting commands).waiting.toList
        = (waiting.toList ++ commands.filterMap Command.idle?).filter
            fun w => !(run c k written waiting commands).kernel.quiet w.1 := by
  have hf := waiting_foldl c commands (k, { written, waiting })
  simp only [run, finish]
  generalize commands.foldl (scan c) (k, { written, waiting }) = ks at hf
  have hw : (flush c (if ks.2.worked then ks else work c none ks)).2.waiting = ks.2.waiting := by
    rw [waiting_flush]; split
    · rfl
    · exact waiting_work c none ks
  generalize flush c (if ks.2.worked then ks else work c none ks) = f at hw
  obtain ⟨k', s⟩ := f
  simp only at hw
  constructor <;> simp only [Array.toList_map, Array.toList_filter, hw, hf]

theorem due_iff (c : Config) (written : Nat) :
    due c written = true ↔ ∃ n, c.snapshotEvery = some n ∧ max 1 n ≤ written := by
  unfold due
  cases c.snapshotEvery <;> simp

/-- Where a save falls: when what is kept back is written and that brings the entries written
since the last save to `max 1 snapshotEvery`, if the journal can save. The count starts again
after it. Kept-back entries are written at an idle, at a peek, at the end of the batch, and
after an input when a save is due. -/
theorem flush_save (c : Config) (k : Kernel sys) (s : Scan sys P W) :
    (flush c (k, s)).2.written
        = (if due c (s.written + s.entries.size) then 0 else s.written + s.entries.size)
      ∧ (flush c (k, s)).2.acts.toList
        = (put (put (put s.acts s.entries.isEmpty (.append s.entries)) s.events.isEmpty
            (.record s.events)) s.outputs.isEmpty (.handOver s.outputs)).toList
          ++ (if due c (s.written + s.entries.size) then [.save k.image] else [])
      ∧ (flush c (k, s)).1 = if due c (s.written + s.entries.size) then k.image.kernel else k := by
  obtain ⟨written, waiting, acts, entries, events, outputs, worked⟩ := s
  simp only [flush]
  split <;> simp_all

private theorem workAll_spread (c : Config) (spread : Kernel.Spread) :
    workAll (sys := sys) (P := P) (W := W) { c with spread } = workAll c := by
  funext xs ks
  unfold workAll
  congr 1
  funext k
  rw [Journal.turnAll_spread, Journal.turnAll_spread (spread := c.spread)]

private theorem scan_spread (c : Config) (spread : Kernel.Spread) :
    scan (sys := sys) (P := P) (W := W) { c with spread } = scan c := by
  funext ks command
  cases command with
  | inputs xs => simp only [scan, workAll_spread]; rfl
  | _ => rfl

/-- How the waves of a batch are spread over threads changes nothing it does: the same kernel,
the same acts, the same answers (`Journal.turnAll_spread`, from `Kernel.runWaves_eq`). So the
shell may choose the spread of each batch as it likes, from its own timing. -/
theorem run_spread (c : Config) (spread : Kernel.Spread) (k : Kernel sys) (written : Nat)
    (waiting : Array (Bool × W)) (commands : List (Command σ P W)) :
    run { c with spread } k written waiting commands = run c k written waiting commands := by
  simp only [run, scan_spread]
  rfl

/-! The origins of the outputs handed over. -/

omit [Hashable σ.Id] in
private theorem steps_grows (act : Act sys P) : act.steps.length = act.grows := by
  cases act with
  | handOver outputs => simp only [Act.steps, Act.grows]; split <;> rfl
  | append entries => simp [Act.steps, Act.grows, Journal.steps]
  | _ => rfl

omit [Hashable σ.Id] in
theorem grown_eq (acts : Array (Act sys P)) : grown acts = (history acts.toList).length := by
  rw [grown, ← Array.foldl_toList]
  suffices h : ∀ (l : List (Act sys P)) n,
      l.foldl (fun n act => n + act.grows) n = n + (history l).length by
    simpa using h acts.toList 0
  intro l
  induction l with
  | nil => simp [history]
  | cons a l ih =>
    intro n
    rw [List.foldl_cons, ih]
    simp [history, List.flatMap_cons, steps_grows, Nat.add_assoc]

omit [Hashable σ.Id] in
/-- The history the acts write asks of the kernel what their journal does. -/
theorem history_ops (acts : List (Act sys P)) : (history acts).filterMap id = journal acts := by
  induction acts with
  | nil => rfl
  | cons act acts ih =>
    rw [history, List.flatMap_cons, List.filterMap_append, ← history, ih]
    show List.filterMap id act.steps ++ journal acts = act.ops ++ journal acts
    congr 1
    cases act with
    | append entries => exact Journal.steps_ops _
    | handOver outputs => simp only [Act.steps, Act.ops]; split <;> rfl
    | _ => rfl

private def IdInv (index : Nat) (k0 : Kernel sys) (ks : Kernel sys × Scan sys P W) : Prop :=
  handedIds ks.2.acts.toList ++ ks.2.outputs.toList
    = Journal.placed k0 index (history ks.2.acts.toList ++ Journal.steps ks.2.entries.toList)

private theorem placed_marks (k : Kernel sys) (index : Nat) {marks : List (Option (Kernel.Op σ))}
    (h : ∀ m ∈ marks, m = none ∨ m = some .snapshot) : Journal.placed k index marks = [] := by
  induction marks generalizing k index with
  | nil => rfl
  | cons m rest ih =>
    rw [Journal.placed, ih _ _ fun m hm => h m (List.mem_cons_of_mem _ hm)]
    rcases h m List.mem_cons_self with rfl | rfl <;> rfl

private theorem idinv_start (index : Nat) (k : Kernel sys) (written : Nat)
    (waiting : Array (Bool × W)) : IdInv index k (k, ({ written, waiting } : Scan sys P W)) :=
  rfl

private theorem idinv_workWith (index : Nat) (turn : Kernel sys → Journal.Turn sys)
    (hplaced : ∀ k i, Journal.placed k i (Journal.steps (turn k).entries)
      = Journal.tag (i + (turn k).entries.length) (turn k).outputs)
    {k0 : Kernel sys} {ks : Kernel sys × Scan sys P W} (h : Inv k0 ks) (hi : IdInv index k0 ks) :
    IdInv index k0 (workWith index turn ks) := by
  obtain ⟨k, ⟨written, waiting, acts, entries, events, outputs, worked⟩⟩ := ks
  have hk := h.kernel
  unfold IdInv at hi ⊢
  simp only at hk hi
  have hops : (history acts.toList ++ Journal.steps entries.toList).filterMap id
      = journal acts.toList ++ Journal.ops entries.toList := by
    rw [List.filterMap_append, history_ops, Journal.steps_ops]
  have hp := hplaced k (index + (history acts.toList ++ Journal.steps entries.toList).length)
  simp only [workWith]
  generalize turn k = t at hp ⊢
  obtain ⟨tk, tev, tout, tent⟩ := t
  simp only [Array.toList_appendList, Journal.steps_append]
  rw [← List.append_assoc (history acts.toList), Journal.placed_append, hops, ← hk, hp, ← hi,
    List.append_assoc, grown_eq]
  simp [Nat.add_assoc]

private theorem flush_empty (c : Config) (ks : Kernel sys × Scan sys P W) :
    (flush c ks).2.entries = #[] ∧ (flush c ks).2.outputs = #[] := by
  obtain ⟨k, ⟨_, _, _, _, _, _, _⟩⟩ := ks
  simp only [flush]; split <;> exact ⟨rfl, rfl⟩

private theorem idinv_flush (c : Config) {index : Nat} {k0 : Kernel sys}
    {ks : Kernel sys × Scan sys P W} (hi : IdInv index k0 ks) : IdInv index k0 (flush c ks) := by
  obtain ⟨k, s⟩ := ks
  obtain ⟨he, ho⟩ := flush_empty c (k, s)
  obtain ⟨-, hacts, -⟩ := flush_save c k s
  unfold IdInv at hi ⊢
  simp only at hi
  rw [he, ho, hacts]
  have hh : handedIds (put (put (put s.acts s.entries.isEmpty (.append s.entries)) s.events.isEmpty
      (.record s.events)) s.outputs.isEmpty (.handOver s.outputs)).toList
        = handedIds s.acts.toList ++ s.outputs.toList := by
    simp only [toList_put]
    cases hE : s.entries.isEmpty <;> cases hV : s.events.isEmpty <;>
      cases hO : s.outputs.isEmpty <;> simp_all [handedIds, Act.placed, Array.isEmpty_iff]
  have hs : history (put (put (put s.acts s.entries.isEmpty (.append s.entries)) s.events.isEmpty
      (.record s.events)) s.outputs.isEmpty (.handOver s.outputs)).toList
        = history s.acts.toList ++ Journal.steps s.entries.toList
          ++ (if s.outputs.isEmpty then [] else [none]) := by
    simp only [toList_put]
    cases hE : s.entries.isEmpty <;> cases hV : s.events.isEmpty <;>
      cases hO : s.outputs.isEmpty <;> simp_all [history, Act.steps, Journal.steps, Array.isEmpty_iff]
  have hsave : ∀ m ∈ history (if due c (s.written + s.entries.size) then [Act.save (P := P) k.image]
      else []), m = none ∨ m = some .snapshot := by
    intro m hm
    split at hm <;> simp_all [history, Act.steps]
  have hout : ∀ m ∈ (if s.outputs.isEmpty then [] else [none] : List (Option (Kernel.Op σ))),
      m = none ∨ m = some .snapshot := by
    intro m hm
    split at hm <;> simp_all
  have hnone : handedIds (if due c (s.written + s.entries.size) then [Act.save (P := P) k.image]
      else []) = [] := by
    split <;> rfl
  simp only [handedIds, history, List.flatMap_append] at hh hs hnone hsave hi ⊢
  rw [hh, hnone, hs, show Journal.steps ([] : List (Journal.Entry σ)) = [] from rfl]
  simp only [List.append_nil]
  rw [Journal.placed_append, placed_marks _ _ hsave, List.append_nil, Journal.placed_append,
    placed_marks _ _ hout, List.append_nil, ← hi]

private theorem idinv_scan (c : Config) {k0 : Kernel sys} {ks : Kernel sys × Scan sys P W}
    (h : Inv k0 ks) (hi : IdInv c.index k0 ks) (command : Command σ P W) :
    IdInv c.index k0 (scan c ks command) := by
  cases command with
  | input x =>
    have hw : IdInv c.index k0 (work c (some x) ks) := idinv_workWith c.index _
      (fun k i => Journal.turn_placed k c.now_ms (some x) c.fuel i) h hi
    simp only [scan]
    generalize work c (some x) ks = w at hw
    obtain ⟨k, s⟩ := w
    split
    · exact idinv_flush c hw
    · exact hw
  | inputs xs =>
    have hw : IdInv c.index k0 (workAll c xs ks) := idinv_workWith c.index _
      (fun k i => Journal.turnAll_placed k c.now_ms xs (c.fuel * max 1 xs.length) c.spread i) h hi
    simp only [scan]
    generalize workAll c xs ks = w at hw
    obtain ⟨k, s⟩ := w
    split
    · exact idinv_flush c hw
    · exact hw
  | idle timers waiter =>
    have hf := idinv_flush c hi
    simp only [scan]
    generalize flush c ks = f at hf
    obtain ⟨k, s⟩ := f
    exact hf
  | peek i reply =>
    have hf := idinv_flush c hi
    simp only [scan]
    generalize flush c ks = f at hf
    obtain ⟨k, s⟩ := f
    unfold IdInv at hf ⊢
    simp only [Array.toList_push, handedIds, history, List.flatMap_append] at hf ⊢
    simpa [Act.placed, Act.steps] using hf

private theorem idinv_foldl (c : Config) {k0 : Kernel sys} (commands : List (Command σ P W)) :
    ∀ {ks : Kernel sys × Scan sys P W}, Inv k0 ks → IdInv c.index k0 ks →
      IdInv c.index k0 (commands.foldl (scan c) ks) := by
  induction commands with
  | nil => exact fun _ hi => hi
  | cons command commands ih => exact fun h hi => ih (inv_scan c h command) (idinv_scan c h hi command)

/-- A batch hands each output over with its origin in the history it writes: the entries it
appends, the `handed` mark the shell notes after each hand-over and the mark of each save, after
the `c.index` entries the history had. With `Journal.ids_append`, that is the origin the whole
history gives the output, which a restart gives it again (`Journal.recoverIds_suffix`). -/
theorem run_ids (c : Config) (k : Kernel sys) (written : Nat) (waiting : Array (Bool × W))
    (commands : List (Command σ P W)) :
    handedIds (run c k written waiting commands).acts.toList
      = Journal.placed k c.index (history (run c k written waiting commands).acts.toList) := by
  have h := inv_foldl c commands (inv_start k written waiting)
  have hi := idinv_foldl c commands (inv_start k written waiting) (idinv_start c.index k written waiting)
  simp only [run, finish]
  generalize commands.foldl (scan c) (k, { written, waiting }) = ks at h hi
  have hw : IdInv c.index k (if ks.2.worked then ks else work c none ks) := by
    split
    · exact hi
    · exact idinv_workWith c.index _ (fun k i => Journal.turn_placed k c.now_ms none c.fuel i) h hi
  have hf := idinv_flush c hw
  obtain ⟨he, ho⟩ := flush_empty c (if ks.2.worked then ks else work c none ks)
  generalize flush c (if ks.2.worked then ks else work c none ks) = f at hf he ho
  obtain ⟨k', s⟩ := f
  unfold IdInv at hf
  simp only at hf he ho ⊢
  rw [he, ho] at hf
  simpa [Journal.steps] using hf

/-- How the waves of a batch are spread changes no output's id (`run_spread`). -/
theorem run_ids_spread (c : Config) (spread : Kernel.Spread) (k : Kernel sys) (written : Nat)
    (waiting : Array (Bool × W)) (commands : List (Command σ P W)) :
    handedIds (run { c with spread } k written waiting commands).acts.toList
      = handedIds (run c k written waiting commands).acts.toList := by
  rw [run_spread]

end Lanes.Batch
