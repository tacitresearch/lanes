/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Durable.Ship
public import Lanes.Durable.OutputId
public import Lanes.Lib.Time.Format

/-!
A restore from what `Lanes.Journal.Ship` uploaded: pick a point, then the newest snapshot at or
before it and the segments after it (`plan`), read them (`piece?`), and stitch them into the
entries of a journal file (`journal`). The file ends with a `handed` mark and the restore
writes no id, so its first start hands nothing over and takes a new id: a restored copy is a
restore under D105, with no effects.

The planner only chooses: `journal` checks that the pieces it is given join, so what is proved
of it holds of any choice. `journal_resumeIds` is the theorem: if every piece holds the entries
of the history at its positions, which is what the shipper puts (`Ship.Holds.put`), and the
snapshot is the one the shard saved at its mark, a start from the restored files gives the
kernel the local journal had after those entries (`resumeIds_eq_recoverIds`), and owes
nothing.
-/

@[expose] public section

namespace Lanes.Journal.Restore

open Ship (Slice)

variable {σ : Signature}

/-- An object of a journal in the store, as its name gives it. -/
inductive Object where
  /-- Entries at positions `first` to `stop`, not including `stop`. -/
  | segment (first stop : Nat) (sum : String)
  | snapshot (index : Nat) (sum : String)
  deriving DecidableEq, Repr

/-- The object a name under a journal's prefix is (`Ship.Upload.object`). -/
def Object.parse? (name : String) : Option Object :=
  match name.splitOn "/" with
  | ["segment", rest] =>
    match rest.splitOn "-" with
    | [a, b, sum] => do
      let first ← a.toNat?
      let stop ← b.toNat?
      if first < stop then some (.segment first stop sum) else none
    | _ => none
  | ["snapshot", rest] =>
    match rest.splitOn "-" with
    | [a, sum] => do return .snapshot (← a.toNat?) sum
    | _ => none
  | _ => none

/-- An object in a listing of the store: its journal, its name under the journal, what the
name says, and when the store last wrote it, in nanoseconds from the epoch. -/
structure Listed where
  journal : String
  name : String
  object : Object
  modified : Option Int := none
  deriving Repr

/-- Reads a key of a listing of `keyPrefix`, with the last-modified time the store gave it
(RFC 3339, as S3 gives it). Keys that are not a journal's objects are left out. -/
def listed? (keyPrefix key modified : String) : Option Listed := do
  let rest ← (key.dropPrefix? keyPrefix).map (·.toString)
  match rest.splitOn "/" with
  | journal :: parts =>
    let name := "/".intercalate parts
    let object ← Object.parse? name
    let modified := (TimeFormat.parseRfc3339 modified).map fun t => t.toUnix * 1000000000 + (t.nanos.val : Int)
    return { journal, name, object, modified }
  | [] => none

inductive Point where
  /-- As far as the objects in the store go. -/
  | latest
  /-- The history's first `n` entries. -/
  | position (n : Nat)
  /-- As far as the objects stored by this instant go, in nanoseconds from the epoch. -/
  | time (at_ns : Int)
  deriving Repr

/-- The journal whose newest object is newest: the one a lost machine was writing. -/
def newest (objects : List Listed) : Option String :=
  (objects.foldl (fun (best : Option (String × Int)) o =>
    let t := o.modified.getD 0
    match best with
    | some (_, b) => if b < t then some (o.journal, t) else best
    | none => some (o.journal, t)) none).map (·.1)

structure Plan where
  journal : String
  /-- The snapshot to start from: the position of its mark, and its name. -/
  snapshot : Option (Nat × String) := none
  /-- The segments to read, in order: name, first position, stop. -/
  segments : List (String × Nat × Nat) := []
  /-- How many entries of the history the restore holds. -/
  point : Nat
  deriving Repr

/-- Of the segments that hold position `cur`, the one that reaches furthest. -/
def best (segments : List (String × Nat × Nat)) (cur : Nat) : Option (String × Nat × Nat) :=
  segments.foldl (fun acc s =>
    if s.2.1 ≤ cur ∧ cur < s.2.2 ∧ acc.all (·.2.2 < s.2.2) then some s else acc) none

/-- From `cur`, segments that carry on from each other, up to `stop`, and where they reach. -/
def chain (segments : List (String × Nat × Nat)) (cur stop : Nat) :
    (fuel : Nat) → List (String × Nat × Nat) × Nat
  | 0 => ([], cur)
  | fuel + 1 =>
    if stop ≤ cur then ([], cur)
    else match best segments cur with
      | some s =>
        let (rest, reached) := chain segments (min s.2.2 stop) stop fuel
        (s :: rest, reached)
      | none => ([], cur)

/-- The objects to read for `point` from the objects of `journal`: from the newest snapshot
with an unbroken run of segments after it to the point; for `latest`, the start that reaches
furthest, the newest of those that reach as far. `none` if the point cannot be reached. -/
def plan (objects : List Listed) (journal : String) (point : Point) : Option Plan :=
  let mine := objects.filter fun o => o.journal == journal && match point with
    | .time t => o.modified.any (· ≤ t)
    | _ => true
  let segments := mine.filterMap fun o => match o.object with
    | .segment first stop _ => some (o.name, first, stop)
    | _ => none
  let snapshots := (mine.filterMap fun o => match o.object with
    | .snapshot index _ => some (index, o.name)
    | _ => none).mergeSort (fun a b => b.1 ≤ a.1)
  let starts : List (Option (Nat × String)) := snapshots.map some ++ [none]
  let fuel := segments.length + 1
  let from_ (start : Option (Nat × String)) : Nat := (start.map (·.1 + 1)).getD 0
  let stopAll := segments.foldl (fun m s => max m s.2.2) 0
  if mine.isEmpty then none
  else match point with
    | .position n =>
      starts.findSome? fun start =>
        if start.all (·.1 < n) then
          let (chosen, reached) := chain segments (from_ start) n fuel
          if n ≤ reached then some { journal, snapshot := start, segments := chosen, point := n }
          else none
        else none
    | _ =>
      let plans := starts.map fun start =>
        let (chosen, reached) := chain segments (from_ start) stopAll fuel
        ({ journal, snapshot := start, segments := chosen, point := reached } : Plan)
      plans.foldl (fun (acc : Option Plan) p =>
        match acc with
        | some a => if a.point < p.point then some p else acc
        | none => some p) none

/-- A segment read back: its first position and its entries. -/
structure Piece (σ : Signature) where
  first : Nat
  entries : List (Entry σ)

/-- A segment's bytes as a piece: a whole journal file of `system`, with `count` entries. -/
def piece? (input : Codec σ.In) (system : String) (first count : Nat) (bytes : ByteArray) :
    Option (Piece σ) :=
  match open? input system bytes with
  | .ok (entries, size) =>
    if size = bytes.size ∧ entries.length = count then some ⟨first, entries⟩ else none
  | .error _ => none

/-- The entries of the pieces from position `cur` to `stop`, each piece carrying on from where
the one before it stopped. -/
def stitch (cur stop : Nat) : List (Piece σ) → Option (List (Entry σ))
  | [] => if cur = stop then some [] else none
  | p :: rest =>
    if p.first ≤ cur ∧ cur < p.first + p.entries.length ∧ cur < stop then
      let hi := min (p.first + p.entries.length) stop
      (stitch hi stop rest).map ((p.entries.drop (cur - p.first)).take (hi - cur) ++ ·)
    else none

/-- The entries of the restored journal file: the snapshot's mark, if it starts from one, the
entries after it to `point`, and a `handed` mark, so that a start of it owes nothing. -/
def journal (snapshot : Option Nat) (point : Nat) (pieces : List (Piece σ)) :
    Option (List (Entry σ)) :=
  match snapshot with
  | some index =>
    if index < point then (stitch (index + 1) point pieces).map (.snapshot index :: · ++ [.handed])
    else none
  | none => (stitch 0 point pieces).map (· ++ [.handed])

/-! ## A restore is the local journal at its point -/

/-- A segment the shipper put reads back as the piece it was. -/
theorem piece?_file (input : Codec σ.In) {system : String} {entries : List (Entry σ)}
    (hsystem : preludeFits input system = true)
    (h : ∀ entry ∈ entries, Entry.fits input entry = true) (first : Nat) :
    piece? input system first entries.length (file input system entries)
      = some ⟨first, entries⟩ := by
  simp [piece?, open?_file input hsystem h]

theorem slice_drop_take {history entries : List (Entry σ)} {first cur hi : Nat}
    (h : Slice history first entries) (hcur : first ≤ cur) (hhi : hi ≤ first + entries.length) :
    (entries.drop (cur - first)).take (hi - cur) = (history.drop cur).take (hi - cur) := by
  unfold Slice at h
  rw [h, List.drop_take, List.take_take, List.drop_drop, Nat.add_sub_cancel' hcur]
  congr 1
  omega

/-- Stitched pieces of a history are the history between the two positions. -/
theorem stitch_slice {history : List (Entry σ)} :
    ∀ (pieces : List (Piece σ)) (cur stop : Nat) {past : List (Entry σ)},
    (∀ p ∈ pieces, Slice history p.first p.entries) → stitch cur stop pieces = some past →
    cur ≤ stop ∧ past = (history.drop cur).take (stop - cur)
  | [], cur, stop, past, _, h => by
    unfold stitch at h
    split at h
    · cases h
      subst cur
      simp
    · cases h
  | p :: rest, cur, stop, past, hpieces, h => by
    unfold stitch at h
    split at h
    · next hguard =>
      obtain ⟨hfirst, hcur, hstop⟩ := hguard
      generalize hhi : min (p.first + p.entries.length) stop = hi at h
      dsimp only at h
      cases hrest : stitch hi stop rest with
      | none => rw [hrest] at h; cases h
      | some more =>
        rw [hrest] at h
        cases h
        obtain ⟨hle, hmore⟩ := stitch_slice rest hi stop
          (fun q hq => hpieces q (List.mem_cons_of_mem _ hq)) hrest
        have hp := hpieces p List.mem_cons_self
        refine ⟨by omega, ?_⟩
        rw [slice_drop_take hp hfirst (by omega), hmore,
          show stop - cur = (hi - cur) + (stop - hi) by omega, List.take_add, List.drop_drop,
          show cur + (hi - cur) = hi by omega]
    · cases h

/-- The history up to `point` is the history up to the mark at `index`, the mark, and the
entries between. -/
theorem take_mark {history : List (Entry σ)} {index point : Nat}
    (hmark : history[index]? = some (Entry.snapshot index)) (hlt : index < point) :
    history.take point
      = history.take index ++ .snapshot index :: (history.drop (index + 1)).take (point - (index + 1)) := by
  have hlen := (List.getElem?_eq_some_iff.mp hmark).1
  have hsplit : history.drop index = .snapshot index :: history.drop (index + 1) := by
    rw [List.drop_eq_getElem_cons hlen]
    congr
    exact (List.getElem?_eq_some_iff.mp hmark).2
  rw [show point = index + (point - index) by omega, List.take_add, hsplit,
    show point - index = (point - (index + 1)) + 1 by omega, List.take_succ_cons]
  congr 3
  omega

/-- No entry before the mark at `index` is that mark, since a mark carries its place. -/
theorem before_mark {history : List (Entry σ)} {index : Nat}
    (hplaced : ∀ i index, history[i]? = some (Entry.snapshot index) → index = i)
    (hlen : index ≤ history.length) :
    ∀ entry ∈ history.take index, entry.savedAt ≠ some (history.take index).length := by
  intro entry hentry hsaved
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hentry
  rw [List.getElem?_take] at hi
  split at hi
  · next hlt =>
    cases entry <;> simp only [Entry.savedAt, Option.some.injEq, reduceCtorEq] at hsaved
    rw [List.length_take, Nat.min_eq_left hlen] at hsaved
    subst hsaved
    have := hplaced i _ hi
    omega
  · cases hi

theorem resumeIds_none (sys : System σ) [Hashable σ.Id] (past : List (Entry σ))
    (h : ∀ n tail, past ≠ .snapshot (n + 1) :: tail) :
    resumeIds sys none past = some (recoverIds sys past) := by
  cases past with
  | nil => rfl
  | cons e tail =>
    cases e with
    | snapshot k =>
      cases k with
      | zero => rfl
      | succ n => exact absurd rfl (h n tail)
    | _ => rfl

/-- The snapshot a restore starts from, as the shard saved it at its mark. -/
def saved (sys : System σ) [Hashable σ.Id] (history : List (Entry σ)) (snapshot : Option Nat) :
    Option (Nat × Kernel.Image sys) :=
  snapshot.map fun index => (index, (recover sys (history.take index)).1.image)

/--
A start from a restore gives what the local journal gives at the point: if every piece holds
the entries of the history at its positions and the snapshot is the kernel saved at its mark,
the restored journal resumes exactly as the history's first `point` entries and a `handed`
mark recover, ids included (`resumeIds_eq_recoverIds`).
-/
theorem journal_resumeIds (sys : System σ) [Hashable σ.Id] {history : List (Entry σ)}
    (hplaced : ∀ i index, history[i]? = some (Entry.snapshot index) → index = i)
    {snapshot : Option Nat} {point : Nat} {pieces : List (Piece σ)} {past : List (Entry σ)}
    (hpieces : ∀ p ∈ pieces, Slice history p.first p.entries)
    (hmark : ∀ index, snapshot = some index → history[index]? = some (Entry.snapshot index))
    (h : journal snapshot point pieces = some past) :
    resumeIds sys (saved sys history snapshot) past
      = some (recoverIds sys (history.take point ++ [.handed])) := by
  cases snapshot with
  | some index =>
    simp only [journal] at h
    split at h
    · next hlt =>
      cases hrest : stitch (index + 1) point pieces with
      | none => rw [hrest] at h; cases h
      | some rest =>
        rw [hrest] at h
        cases h
        have hm := hmark index rfl
        have hlen := (List.getElem?_eq_some_iff.mp hm).1
        obtain ⟨_, hslice⟩ := stitch_slice pieces (index + 1) point hpieces hrest
        have hbefore := before_mark hplaced (Nat.le_of_lt hlen)
        have htake : (history.take index).length = index := by
          rw [List.length_take]; omega
        have key := resumeIds_eq_recoverIds sys (history.take index) (rest ++ [.handed]) index
          hbefore
        rw [htake, List.drop_eq_nil_of_le (by omega), List.nil_append] at key
        rw [take_mark hm hlt, ← hslice]
        simpa [saved] using key
    · cases h
  | none =>
    simp only [journal] at h
    cases hrest : stitch 0 point pieces with
    | none => rw [hrest] at h; cases h
    | some rest =>
      rw [hrest] at h
      cases h
      obtain ⟨_, hslice⟩ := stitch_slice pieces 0 point hpieces hrest
      simp only [List.drop_zero, Nat.sub_zero] at hslice
      subst hslice
      simp only [saved, Option.map_none]
      apply resumeIds_none
      intro n tail hpast
      cases hpt : history.take point with
      | nil => rw [hpt] at hpast; cases hpast
      | cons e more =>
        rw [hpt] at hpast
        simp only [List.cons_append, List.cons.injEq] at hpast
        have h0 : history[0]? = some (Entry.snapshot (n + 1)) := by
          have := congrArg (·[0]?) hpt
          simp only [List.getElem?_take, List.getElem?_cons_zero] at this
          split at this
          · rw [this, hpast.1]
          · cases this
        have := hplaced 0 _ h0
        omega

/-- What that start owes and holds: nothing to hand over again, and the kernel the history's
first `point` entries lead to. -/
theorem recoverIds_handed_end (sys : System σ) [Hashable σ.Id] (past : List (Entry σ)) :
    (recoverIds sys (past ++ [.handed])).1 = (recover sys past).1
      ∧ (recoverIds sys (past ++ [.handed])).2.2 = [] := by
  constructor
  · have he := congrArg Prod.fst (recoverIds_erase sys (past ++ [.handed])).1
    simp only [erase] at he
    rw [he, recover, List.foldl_append, ← recover]
    generalize recover sys past = acc
    obtain ⟨k, pending⟩ := acc
    rfl
  · have := recoverIds_handed sys past (rest := []) (by simp)
    simpa [steps, placed] using this

/-- A restore at `point` starts with the kernel the local journal had after its first `point`
entries, and hands nothing over. -/
theorem journal_restores (sys : System σ) [Hashable σ.Id] {history : List (Entry σ)}
    (hplaced : ∀ i index, history[i]? = some (Entry.snapshot index) → index = i)
    {snapshot : Option Nat} {point : Nat} {pieces : List (Piece σ)} {past : List (Entry σ)}
    (hpieces : ∀ p ∈ pieces, Slice history p.first p.entries)
    (hmark : ∀ index, snapshot = some index → history[index]? = some (Entry.snapshot index))
    (h : journal snapshot point pieces = some past) :
    ∃ length, resumeIds sys (saved sys history snapshot) past
      = some ((recover sys (history.take point)).1, length, []) := by
  rw [journal_resumeIds sys hplaced hpieces hmark h]
  obtain ⟨hk, howed⟩ := recoverIds_handed_end sys (history.take point)
  exact ⟨_, by rw [← hk, ← howed]⟩

end Lanes.Journal.Restore
