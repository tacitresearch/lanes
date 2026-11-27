/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Durable.Journal
public import Lanes.Proof.List

/-!
What a shard does with everything it takes from its inbox at once, as a pure function: the
turns it asks of the kernel, and the acts the shell is to perform for them, in order. The shell
(`Lanes.Runtime`) performs them and decides nothing.

Of every batch: the journal describes the kernel (`run_kernel`); an output is handed over only
once the entries that produce it are appended, a save falls where every output produced has
been handed over, and a peek sees the kernel the journal describes (`run_sound`); a peek sees
every input before it and none after (`run_peek`); who waits for the shard to be idle is
answered when the kernel is quiet (`run_resolved`).

The reply handles are opaque: `P i` answers a peek at actor `i` and `W` an idle, as `W` wakes a
sleeper in `Mailbox`.
-/

@[expose] public section

namespace Lanes.Batch

variable {σ : Signature}

inductive Command (σ : Signature) (P : σ.Id → Type) (W : Type) where
  | input (x : σ.In)
  | idle (timers : Bool) (waiter : W)
  | peek (i : σ.Id) (reply : P i)

inductive Act (sys : System σ) (P : σ.Id → Type) where
  | append (entries : Array (Journal.Entry σ))
  | record (events : Array (Event σ))
  | handOver (outputs : Array σ.Out)
  /-- Save this image of the kernel. The kernel goes on as the image restores it. -/
  | save (image : Kernel.Image sys)
  | answer (i : σ.Id) (reply : P i) (state : sys.State i)

structure Config where
  now_ms : Nat
  fuel : Nat
  /-- How many entries to write between two saves, if the journal can save. -/
  snapshotEvery : Option Nat

/-- The shard's part of a batch so far, besides its kernel. -/
structure Scan (sys : System σ) (P : σ.Id → Type) (W : Type) where
  /-- Entries written since the last save. -/
  written : Nat
  waiting : Array (Bool × W)
  acts : Array (Act sys P) := #[]
  entries : Array (Journal.Entry σ) := #[]
  events : Array (Event σ) := #[]
  outputs : Array σ.Out := #[]
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

variable [Hashable σ.Id]

/-- A turn, kept back to be written with the turns after it. -/
def work (c : Config) (input : Option σ.In) :
    Kernel sys × Scan sys P W → Kernel sys × Scan sys P W
  | (k, ⟨written, waiting, acts, entries, events, outputs, _⟩) =>
    match Journal.turn k c.now_ms input c.fuel with
    | { kernel, events := more, outputs := out, entries := new } =>
      (kernel, { written, waiting, acts, entries := entries ++ new
                 events := events ++ more, outputs := outputs ++ out
                 worked := true })

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
  | .handOver outputs => outputs.toList
  | _ => []

def Act.events : Act sys P → List (Event σ)
  | .record events => events.toList
  | _ => []

def journal (acts : List (Act sys P)) : List (Kernel.Op σ) := acts.flatMap Act.ops

def handed (acts : List (Act sys P)) : List σ.Out := acts.flatMap Act.outputs

def recorded (acts : List (Act sys P)) : List (Event σ) := acts.flatMap Act.events

/-- What an act may do after `before`, from kernel `k`: hand over or record exactly what the
journal so far produced and was not yet handed over or recorded, save the kernel the journal
describes once every output it produced is handed over, and answer with that kernel's state. -/
def Act.Sound (k : Kernel sys) (before : List (Act sys P)) : Act sys P → Prop
  | .append _ => True
  | .record events => recorded before ++ events.toList = (k.exec (journal before)).events
  | .handOver outputs => handed before ++ outputs.toList = (k.exec (journal before)).outputs
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
  outputs : handed ks.2.acts.toList ++ ks.2.outputs.toList
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

private theorem inv_work (c : Config) (input : Option σ.In) {k0 : Kernel sys}
    {ks : Kernel sys × Scan sys P W} (h : Inv k0 ks) : Inv k0 (work c input ks) := by
  obtain ⟨k, ⟨written, waiting, acts, entries, events, outputs, worked⟩⟩ := ks
  obtain ⟨hk, ho, he, hs⟩ := h
  obtain ⟨tk, te, to⟩ := Journal.turn_eq_exec k c.now_ms input c.fuel
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
    simp only [work, Array.toList_appendList, hexec, ← tk, ← te, ← to, ← ho, ← he,
      List.append_assoc]

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
  have h3 : handed a3.toList = handed acts.toList ++ outputs.toList := by
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
    · rw [h3, ho]
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
  rw [houtputs, Array.toList_empty, List.append_nil] at ho
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

end Lanes.Batch
