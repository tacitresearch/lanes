/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Durable.Journal

/-!
Every output a shard hands over has an id, the same each time it is handed over
(`docs/decisions/D96-runtime-contract.md`, clause 2): the journal's own id, made at random when
the journal is begun, the place in the shard's history of the entry that produced the output,
and the output's place among that entry's outputs. A driver passes it on as the idempotency key.

The place in the history is a function of the history before it (`ids_append`), and replay is
deterministic, so a restart hands an output over again with the id it was first handed over
with (`recoverIds_suffix`, `recoverIds_handed`), from a snapshot too (`resumeIds_eq_recoverIds`).
A turn's outputs are all its last entry's (`turn_placed`, `turnAll_placed`), which is what lets a
batch give each output its id as it goes (`Batch.run_ids`).
-/

@[expose] public section

namespace Lanes.Journal

variable {σ : Signature}

/-- Where in a shard's history an output was produced: `position` is the place of the entry
that produced it, counting from 1, or 0 for the outputs of boot, and `place` is the output's
place among that entry's outputs, from 0. -/
structure Origin where
  position : Nat
  place : Nat
  deriving DecidableEq, Repr, Hashable

/-- Whether `a` comes before `b` in a history. -/
def Origin.before (a b : Origin) : Bool :=
  a.position < b.position || (a.position == b.position && a.place < b.place)

theorem Origin.before_irrefl (a : Origin) : a.before a = false := by
  simp [before]

/-- An output's id: its origin in the history of the journal named `journal`. -/
structure OutputId where
  journal : String
  origin : Origin
  deriving DecidableEq, Repr, Hashable

/-- The id as one string, as an idempotency key carries it. -/
def OutputId.key (id : OutputId) : String :=
  id.journal ++ "-" ++ toString id.origin.position ++ "-" ++ toString id.origin.place

/-- A journal's id written from random bytes, two lowercase hexadecimal digits a byte. -/
def journalId (bytes : ByteArray) : String :=
  String.join (bytes.toList.map fun b =>
    let digits := Nat.toDigits 16 b.toNat
    String.ofList (if digits.length < 2 then '0' :: digits else digits))

/-- The outputs of the entry at `position`, each with its origin, the first at `place`. -/
def tag {α : Type} (position : Nat) : List α → (place : Nat := 0) → List (Origin × α)
  | [], _ => []
  | out :: rest, place => (⟨position, place⟩, out) :: tag position rest (place + 1)

@[simp] theorem tag_nil {α : Type} (position place : Nat) :
    tag position ([] : List α) place = [] := rfl

@[simp] theorem tag_snd {α : Type} (position : Nat) (outputs : List α) (place : Nat) :
    (tag position outputs place).map Prod.snd = outputs := by
  induction outputs generalizing place with
  | nil => rfl
  | cons out rest ih => simp [tag, ih]

variable [Hashable σ.Id] {sys : System σ}

/-- An entry of a history as what it asks of the kernel: `none` for a mark, which asks
nothing. -/
def apply? (k : Kernel sys) : Option (Kernel.Op σ) → Kernel.Step sys
  | some op => k.apply op
  | none => { kernel := k }

/-- The requests of a history's entries, one for each entry, marks included, so that each
keeps its place. -/
def steps (entries : List (Entry σ)) : List (Option (Kernel.Op σ)) :=
  entries.map Entry.op?

omit [Hashable σ.Id] in
@[simp] theorem steps_append (a b : List (Entry σ)) : steps (a ++ b) = steps a ++ steps b :=
  List.map_append

omit [Hashable σ.Id] in
@[simp] theorem length_steps (entries : List (Entry σ)) : (steps entries).length = entries.length :=
  List.length_map _

omit [Hashable σ.Id] in
theorem steps_ops (entries : List (Entry σ)) : (steps entries).filterMap id = ops entries := by
  simp [steps, ops, List.filterMap_map, Function.comp_def]

/-- The outputs that the requests `steps` produce from kernel `k`, each with its origin, when
the history had `index` entries before them. -/
def placed (k : Kernel sys) (index : Nat) : List (Option (Kernel.Op σ)) → List (Origin × σ.Out)
  | [] => []
  | step :: rest =>
    tag (index + 1) (apply? k step).outputs ++ placed (apply? k step).kernel (index + 1) rest

theorem exec_step (k : Kernel sys) (step : Option (Kernel.Op σ))
    (rest : List (Option (Kernel.Op σ))) :
    k.exec ((step :: rest).filterMap id)
      = { kernel := ((apply? k step).kernel.exec (rest.filterMap id)).kernel
          events := (apply? k step).events ++ ((apply? k step).kernel.exec (rest.filterMap id)).events
          outputs := (apply? k step).outputs
            ++ ((apply? k step).kernel.exec (rest.filterMap id)).outputs } := by
  cases step with
  | none => rfl
  | some op => simp only [List.filterMap_cons, id, apply?]; exact Kernel.exec_cons k op _

/-- Without their origins, the outputs are those the requests produce. -/
theorem placed_snd (k : Kernel sys) (index : Nat) (steps : List (Option (Kernel.Op σ))) :
    (placed k index steps).map Prod.snd = (k.exec (steps.filterMap id)).outputs := by
  induction steps generalizing k index with
  | nil => rfl
  | cons step rest ih => rw [exec_step, placed, List.map_append, tag_snd, ih]

theorem placed_eq_nil (k : Kernel sys) (index : Nat) {steps : List (Option (Kernel.Op σ))}
    (h : (k.exec (steps.filterMap id)).outputs = []) : placed k index steps = [] := by
  have := placed_snd k index steps
  rw [h] at this
  exact List.map_eq_nil_iff.mp this

/-- An output's origin depends only on the history before it: the outputs of a history, with
their origins, are those of its first part and then those of the rest, from the kernel the
first part leads to and at its length. -/
theorem placed_append (k : Kernel sys) (index : Nat) (a b : List (Option (Kernel.Op σ))) :
    placed k index (a ++ b)
      = placed k index a ++ placed (k.exec (a.filterMap id)).kernel (index + a.length) b := by
  induction a generalizing k index with
  | nil => rfl
  | cons step rest ih =>
    rw [List.cons_append, placed, placed, ih, exec_step, List.append_assoc, List.length_cons,
      Nat.add_right_comm, Nat.add_assoc]

/-! A turn writes its outputs' entry last. -/

private theorem advance_clock (k : Kernel sys) (now_ms : Nat) :
    k.advance (k.advance now_ms).clock_ms = k.advance now_ms := by
  simp only [Kernel.advance]
  congr 1
  omega

/-- Every output of a turn is its last entry's, which is the `batch` it writes, so it is at
the turn's last place. -/
theorem turn_placed (k : Kernel sys) (now_ms : Nat) (input : Option σ.In) (fuel index : Nat) :
    placed k index (steps (turn k now_ms input fuel).entries)
      = tag (index + (turn k now_ms input fuel).entries.length)
          (turn k now_ms input fuel).outputs := by
  unfold turn
  split
  · rfl
  · cases input with
    | none =>
      simp [steps, placed, apply?, Entry.op?, Kernel.apply, advance_clock]
    | some x =>
      simp [steps, placed, apply?, Entry.op?, Kernel.apply, advance_clock, Kernel.accept]

/-- The same of a turn of inputs that arrived together, however its waves are spread. -/
theorem turnAll_placed (k : Kernel sys) (now_ms : Nat) (inputs : List σ.In) (fuel : Nat)
    (spread : Kernel.Spread) (index : Nat) :
    placed k index (steps (turnAll k now_ms inputs fuel spread).entries)
      = tag (index + (turnAll k now_ms inputs fuel spread).entries.length)
          (turnAll k now_ms inputs fuel spread).outputs := by
  unfold turnAll
  split
  · rfl
  · have hin : (steps (inputs.map Entry.input)).filterMap id = inputs.map Kernel.Op.input := by
      rw [steps_ops]; simp [ops, Entry.op?, List.filterMap_map, Function.comp_def]
    have hsteps : ∀ c, steps (Entry.advance c :: inputs.map Entry.input ++ [Entry.batch fuel])
        = some (.advance c) :: (steps (inputs.map Entry.input) ++ [some (.batch fuel)]) := by
      intro c; simp [steps, Entry.op?]
    simp only [hsteps, placed, apply?, Kernel.apply]
    rw [placed_append, placed_eq_nil _ _ (by rw [hin, Kernel.exec_inputs]), hin,
      Kernel.exec_inputs]
    simp [placed, apply?, Kernel.apply, advance_clock, Kernel.runWaves_eq, steps,
      Nat.add_assoc, Nat.add_comm 1]

/-! Replay, with each output owed kept with its origin. -/

/-- `replay1`, with the length of the history so far and the origin of each output owed. -/
def replayIds1 (acc : Kernel sys × Nat × List (Origin × σ.Out)) (entry : Entry σ) :
    Kernel sys × Nat × List (Origin × σ.Out) :=
  match acc with
  | (k, index, pending) =>
    match apply? k entry.op? with
    | { kernel, outputs, .. } =>
      (kernel, index + 1, (if entry.marks then [] else pending) ++ tag (index + 1) outputs)

/-- Every output of boot and of a history `past`, with its origin. -/
def ids (sys : System σ) (past : List (Entry σ)) : List (Origin × σ.Out) :=
  tag 0 (Kernel.boot sys).2 ++ placed (Kernel.boot sys).1 0 (steps past)

/-- `recover` with origins: the kernel, the length of the history, and the outputs to hand
over again, each with its origin. -/
def recoverIds (sys : System σ) (past : List (Entry σ)) :
    Kernel sys × Nat × List (Origin × σ.Out) :=
  past.foldl replayIds1 ((Kernel.boot sys).1, 0, tag 0 (Kernel.boot sys).2)

/-- `resume` with origins. `none` exactly when `resume` refuses (`resumeIds_erase`). -/
def resumeIds (sys : System σ) (saved : Option (Nat × Kernel.Image sys)) (past : List (Entry σ)) :
    Option (Kernel sys × Nat × List (Origin × σ.Out)) :=
  match saved, past with
  | none, .snapshot (_ + 1) :: _ => none
  | none, past => some (recoverIds sys past)
  | some (index, image), past =>
    (since index past).map fun rest => rest.foldl replayIds1 (image.kernel, index + 1, [])

/-- Forget the origins. -/
def erase (acc : Kernel sys × Nat × List (Origin × σ.Out)) : Kernel sys × List σ.Out :=
  (acc.1, acc.2.2.map Prod.snd)

theorem replayIds1_erase (acc : Kernel sys × Nat × List (Origin × σ.Out)) (entry : Entry σ) :
    erase (replayIds1 acc entry) = replay1 (erase acc) entry
      ∧ (replayIds1 acc entry).2.1 = acc.2.1 + 1 := by
  obtain ⟨k, index, pending⟩ := acc
  cases entry <;> simp [replayIds1, replay1, erase, apply?, Entry.op?, Entry.marks, Kernel.apply]

theorem replayIds_erase (acc : Kernel sys × Nat × List (Origin × σ.Out)) (past : List (Entry σ)) :
    erase (past.foldl replayIds1 acc) = past.foldl replay1 (erase acc)
      ∧ (past.foldl replayIds1 acc).2.1 = acc.2.1 + past.length := by
  induction past generalizing acc with
  | nil => simp
  | cons entry rest ih =>
    obtain ⟨h1, h2⟩ := replayIds1_erase acc entry
    obtain ⟨h3, h4⟩ := ih (replayIds1 acc entry)
    simp only [List.foldl_cons, h3, h1, h4, h2, List.length_cons]
    exact ⟨by simp, by omega⟩

/-- Without the origins, `recoverIds` is `recover`; and it counts the history. -/
theorem recoverIds_erase (sys : System σ) (past : List (Entry σ)) :
    erase (recoverIds sys past) = recover sys past ∧ (recoverIds sys past).2.1 = past.length := by
  have := replayIds_erase ((Kernel.boot sys).1, 0, tag 0 (Kernel.boot sys).2) past
  simp only [erase, tag_snd, Nat.zero_add] at this
  exact ⟨this.1, this.2⟩

theorem resumeIds_erase (sys : System σ) (saved : Option (Nat × Kernel.Image sys))
    (past : List (Entry σ)) :
    (resumeIds sys saved past).map erase = resume sys saved past := by
  unfold resumeIds resume
  split
  · rfl
  · simp only [Option.map_some, (recoverIds_erase sys _).1]
  · simp only [Option.map_map]
    congr 1
    funext rest
    exact (replayIds_erase _ rest).1

/-- What replay owes at the end is a tail of what it owed at the start and every output of
the entries replayed, with the origins the history gives them. -/
theorem replayIds_suffix (k : Kernel sys) (index : Nat) (pending : List (Origin × σ.Out))
    (past : List (Entry σ)) :
    (past.foldl replayIds1 (k, index, pending)).2.2 <:+ pending ++ placed k index (steps past) := by
  induction past generalizing k index pending with
  | nil => simp [steps, placed]
  | cons entry rest ih =>
    simp only [List.foldl_cons, replayIds1, steps, List.map_cons, placed]
    generalize apply? k entry.op? = r
    obtain ⟨kernel, events, outputs⟩ := r
    refine (ih kernel (index + 1) _).trans ?_
    generalize hx : (if entry.marks then [] else pending) = x
    have hsuffix : x <:+ pending := by
      rw [← hx]
      split
      · exact List.nil_suffix
      · exact List.suffix_refl _
    obtain ⟨t, ht⟩ := hsuffix
    exact ⟨t, by rw [← ht]; simp [steps, List.append_assoc]⟩

/-- A restart hands over again only outputs of the history, each with the origin the history
gave it when it was first produced, so the id it was first handed over with. -/
theorem recoverIds_suffix (sys : System σ) (past : List (Entry σ)) :
    (recoverIds sys past).2.2 <:+ ids sys past :=
  replayIds_suffix _ _ _ past

/-- An output's id depends only on the history before it: the ids of a history are those of
its first part, then those its rest gives from the kernel the first part leads to, at the
first part's length. So an output a batch hands over at the end of `a` has the id the whole
history gives it. -/
theorem ids_append (sys : System σ) (a b : List (Entry σ)) :
    ids sys (a ++ b) = ids sys a ++ placed (recover sys a).1 a.length (steps b) := by
  rw [ids, ids, steps, List.map_append, ← steps, ← steps, placed_append, List.append_assoc,
    steps_ops, recover_kernel]
  simp [steps]

private theorem replayIds_unmarked (k : Kernel sys) (index : Nat) (pending : List (Origin × σ.Out))
    {rest : List (Entry σ)} (h : ∀ entry ∈ rest, entry.marks = false) :
    (rest.foldl replayIds1 (k, index, pending)).2.2 = pending ++ placed k index (steps rest) := by
  induction rest generalizing k index pending with
  | nil => simp [steps, placed]
  | cons entry rest ih =>
    simp only [List.foldl_cons, replayIds1, steps, List.map_cons, placed]
    generalize apply? k entry.op? = r
    obtain ⟨kernel, events, outputs⟩ := r
    rw [ih _ _ _ fun e he => h e (List.mem_cons_of_mem _ he), h entry List.mem_cons_self]
    simp [steps]

/-- What a restart hands over again after a `handed` mark is exactly what the entries after it
produced, each with the id it had when they produced it. -/
theorem recoverIds_handed (sys : System σ) (past : List (Entry σ)) {rest : List (Entry σ)}
    (h : ∀ entry ∈ rest, entry.marks = false) :
    (recoverIds sys (past ++ .handed :: rest)).2.2
      = placed (recover sys past).1 (past.length + 1) (steps rest) := by
  have he := recoverIds_erase sys past
  rw [recoverIds, List.foldl_append, List.foldl_cons, ← recoverIds]
  generalize hr : recoverIds sys past = r at he
  obtain ⟨k, index, pending⟩ := r
  simp only [erase] at he
  obtain ⟨hk, hindex⟩ := he
  rw [replayIds1]
  simp only [apply?, Entry.op?, Entry.marks, ite_true, tag_nil, List.append_nil]
  rw [replayIds_unmarked _ _ _ h, List.nil_append, ← hindex, ← congrArg Prod.fst hk]

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

/-- A snapshot is a memo of replay for ids too: starting from one gives what replaying the
whole history gives, ids included, when its mark is at its place in the history. -/
theorem resumeIds_eq_recoverIds (sys : System σ) (before rest : List (Entry σ)) (lost : Nat)
    (h : ∀ entry ∈ before, entry.savedAt ≠ some before.length) :
    resumeIds sys (some (before.length, (recover sys before).1.image))
        (before.drop lost ++ .snapshot before.length :: rest)
      = some (recoverIds sys (before ++ .snapshot before.length :: rest)) := by
  have hsince := since_append before.length (before := before.drop lost) rest fun e he =>
    h e (List.mem_of_mem_drop he)
  have he := recoverIds_erase sys before
  simp only [resumeIds, hsince, Option.map_some, recoverIds, List.foldl_append, List.foldl_cons]
  rw [← recoverIds]
  generalize hr : recoverIds sys before = r at he
  obtain ⟨k, index, pending⟩ := r
  simp only [erase] at he
  obtain ⟨hk, hindex⟩ := he
  simp only [replayIds1, apply?, Entry.op?, Kernel.apply, Entry.marks, ite_true, tag_nil,
    List.append_nil, ← hindex, ← congrArg Prod.fst hk]

end Lanes.Journal
