/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Durable.Disk
public import Lanes.Lib.Crypto.Native

/-!
Shipping a journal to an object store, after Litestream. The journal is written and synced on
the local disk as before, and nothing waits for the store. What is written is sealed into
segments, by size, by age and at each save, and each segment and each snapshot is uploaded once,
under a key that names the journal, the positions it holds and the SHA-256 of its bytes, with a
put that writes only where nothing is (`If-None-Match: *`). A restore from them is
`Lanes/Durable/Restore.lean`.

Every decision is here, as pure functions of a `State`: what to seal and when, which upload to
put next, the wait before a retry, and what is dropped at the bound. The adapter only performs
them (`Lanes/Durable/IO/Ship.lean`, rule 3.9).

At the bound (`Config.maxPending`), sealing one more drops the oldest upload not being put. The
journal on the disk keeps everything it kept before, and a restore picks the newest snapshot
with an unbroken run of segments after it, so a drop loses points to restore to, never the
state. `Holds.step` is the theorem: every segment the shipper puts holds the entries of the
history at the positions its key names.
-/

@[expose] public section

namespace Lanes.Journal.Ship

variable {σ : Signature}

/-- How a journal is shipped. Every bound is here (rule 2.6). -/
structure Config where
  /-- A segment is sealed once this many entries wait. -/
  segmentEntries : Nat := 4096
  /-- Or once its first entry has waited this long: on a lost disk, at most this much of what
  was written before it is gone. -/
  segmentAge_ms : Nat := 10000
  /-- Uploads sealed and not yet stored, segments and snapshots, at least two. Sealing one
  more drops the oldest that is not being put. -/
  maxPending : Nat := 256
  /-- The wait after a put that failed; it doubles with each failure of the same upload, up to
  `retryMax_ms`. -/
  retryBase_ms : Nat := 200
  retryMax_ms : Nat := 60000
  /-- How long closing the journal waits for what is pending to be stored. -/
  close_ms : Nat := 5000
  deriving Repr

/-- What is uploaded. -/
inductive Upload (σ : Signature) where
  /-- The entries at positions `first`, `first + 1`, … of the shard's history. -/
  | segment (first : Nat) (entries : List (Entry σ))
  /-- A snapshot file whose mark is at position `index`. -/
  | snapshot (index : Nat) (bytes : ByteArray)

/-- How a put ended. -/
inductive Outcome where
  | stored
  /-- Something is at the key already. The key holds the SHA-256 of the bytes, so it is these. -/
  | present
  /-- No answer, or a refusal: it is tried again. -/
  | failed
  deriving DecidableEq, Repr

/-- A number with 20 digits, so that keys sort as the positions they name. -/
def digits (n : Nat) : String :=
  let s := toString n
  String.ofList (List.replicate (20 - s.length) '0') ++ s

def sum (bytes : ByteArray) : String := Bytes.hex (Sha256.hash bytes)

/-- The name of an upload under its journal's prefix, and its bytes. A segment is a journal file
of its entries, so it reads with `open?` (`Restore.piece?_file`). -/
def Upload.object (input : Codec σ.In) (system : String) : Upload σ → String × ByteArray
  | .segment first entries =>
    let body := file input system entries
    (s!"segment/{digits first}-{digits (first + entries.length)}-{sum body}", body)
  | .snapshot index bytes => (s!"snapshot/{digits index}-{sum bytes}", bytes)

/-- The snapshot file among a journal's writes. -/
def snapshotOf? : List Write → Option ByteArray
  | [] => none
  | .putSnapshot bytes :: _ => some bytes
  | _ :: rest => snapshotOf? rest

/-- What a save puts in the snapshot file is what is uploaded. -/
theorem snapshotOf?_saveWrites (input : Codec σ.In) {sys : System σ} (c : Kernel.Image.Codecs sys)
    (system : String) (index : Nat) (image : Kernel.Image sys) :
    snapshotOf? (saveWrites input c system index image) = some (saved c system index image) :=
  rfl

structure State (σ : Signature) where
  /-- The position in the history of the first entry waiting. -/
  next : Nat
  /-- The entries durable in the journal and not sealed, newest first. -/
  waitingRev : List (Entry σ) := []
  /-- How many are waiting. -/
  count : Nat := 0
  /-- Entries after those, written without a sync: they may be lost with the process, so they
  wait until a write that syncs makes them durable. -/
  noted : List (Entry σ) := []
  /-- When the oldest waiting entry became durable. -/
  since_ms : Option Nat := none
  /-- Sealed and not yet stored, oldest first. -/
  pending : List (Upload σ) := []
  /-- The first pending upload is being put. -/
  busy : Bool := false
  /-- Puts of the first pending upload that failed. -/
  failures : Nat := 0
  /-- The first pending upload is not tried again before this. -/
  retryAt_ms : Nat := 0
  /-- Every entry before this position is in a segment stored. -/
  storedTo : Nat := 0
  sealed : Nat := 0
  stored : Nat := 0
  /-- Uploads dropped at the bound. -/
  dropped : Nat := 0

/-- The shipper of a journal at a start: `past` is what the journal file holds, from position
`next`, `snapshot` the snapshot file with the position of its mark, and `shipped` how far the
segments stored before reached, as far as this process was told (`storedTo`), or `0`. The
snapshot is uploaded again, which changes nothing if it is there, and the entries from
`shipped` on. -/
def start (next : Nat) (past : List (Entry σ)) (snapshot : Option (Nat × ByteArray))
    (now_ms : Nat) (shipped : Nat := 0) : State σ :=
  let skip := min (shipped - next) past.length
  let rest := past.drop skip
  { next := next + skip, waitingRev := rest.reverse, count := rest.length
    since_ms := if rest.isEmpty then none else some now_ms
    pending := snapshot.toList.map fun (index, bytes) => .snapshot index bytes
    storedTo := next + skip }

/-- What happens to a journal: entries written, flushed and synced when `durable`, which makes
those written before durable too; a save, whose mark has just been written; a put ended. -/
inductive Event (σ : Signature) where
  | wrote (entries : List (Entry σ)) (durable : Bool)
  | saved (index : Nat) (bytes : ByteArray)
  | put (outcome : Outcome)
  /-- The journal is closing: seal what waits. -/
  | closing

/-- The pending uploads with the oldest not being put taken out. -/
def shed {α : Type} : Bool → List α → List α
  | true, head :: _ :: rest => head :: rest
  | true, pending => pending
  | false, _ :: rest => rest
  | false, [] => []

theorem shed_sublist {α : Type} (busy : Bool) (l : List α) : (shed busy l).Sublist l := by
  match busy, l with
  | true, _ :: _ :: _ => exact (List.Sublist.cons _ (List.Sublist.refl _)).cons_cons _
  | true, [] | true, [_] => exact List.Sublist.refl _
  | false, _ :: _ => exact List.Sublist.cons _ (List.Sublist.refl _)
  | false, [] => exact List.Sublist.refl _

/-- Add an upload, dropping the oldest not being put when `pending` is full. -/
def enqueue (cfg : Config) (st : State σ) (u : Upload σ) : State σ :=
  if st.pending.length < max 2 cfg.maxPending then { st with pending := st.pending ++ [u] }
  else
    let kept := shed st.busy st.pending
    { st with pending := kept ++ [u], dropped := st.dropped + (st.pending.length - kept.length)
              failures := if st.busy then st.failures else 0
              retryAt_ms := if st.busy then st.retryAt_ms else 0 }

/-- Seal the waiting entries into a segment. -/
def sealWaiting (cfg : Config) (st : State σ) : State σ :=
  if st.count = 0 then st
  else
    { enqueue cfg st (.segment st.next st.waitingRev.reverse) with
      next := st.next + st.count, waitingRev := [], count := 0, since_ms := none
      sealed := st.sealed + 1 }

def wrote (cfg : Config) (now_ms : Nat) (entries : List (Entry σ)) (durable : Bool)
    (st : State σ) : State σ :=
  if durable then
    let moved := st.noted ++ entries
    let st := { st with
      waitingRev := moved.reverse ++ st.waitingRev, count := st.count + moved.length, noted := []
      since_ms := st.since_ms.or (if moved.isEmpty then none else some now_ms) }
    if max 1 cfg.segmentEntries ≤ st.count then sealWaiting cfg st else st
  else { st with noted := st.noted ++ entries }

/-- The wait after the `failures`th failure of an upload. -/
def backoff (cfg : Config) (failures : Nat) : Nat :=
  min cfg.retryMax_ms (cfg.retryBase_ms * 2 ^ min (failures - 1) 20)

def answer (cfg : Config) (now_ms : Nat) (outcome : Outcome) (st : State σ) : State σ :=
  if !st.busy then st
  else match outcome with
    | .stored | .present =>
      { st with pending := st.pending.tail, busy := false, failures := 0, retryAt_ms := 0
                stored := st.stored + 1
                storedTo := match st.pending with
                  | .segment first entries :: _ =>
                    if first ≤ st.storedTo then max st.storedTo (first + entries.length)
                    else st.storedTo
                  | _ => st.storedTo }
    | .failed =>
      { st with busy := false, failures := st.failures + 1
                retryAt_ms := now_ms + backoff cfg (st.failures + 1) }

def step (cfg : Config) (now_ms : Nat) (st : State σ) : Event σ → State σ
  | .wrote entries durable => wrote cfg now_ms entries durable st
  | .saved index bytes => enqueue cfg (sealWaiting cfg st) (.snapshot index bytes)
  | .put outcome => answer cfg now_ms outcome st
  | .closing => sealWaiting cfg st

/-- What the adapter does next: put an upload, then tell the shipper how it ended; or wait,
at most the time given, or until told something. -/
inductive Act (σ : Signature) where
  | put (u : Upload σ)
  | wait (ms : Option Nat)

def soonest : Option Nat → Option Nat → Option Nat
  | some a, some b => some (min a b)
  | a, b => a.or b

/-- When the waiting entries are sealed by age. -/
def sealAt (cfg : Config) (st : State σ) : Option Nat :=
  st.since_ms.map (· + cfg.segmentAge_ms)

/-- The waiting entries sealed if they have waited long enough. -/
def ripen (cfg : Config) (now_ms : Nat) (st : State σ) : State σ :=
  if (sealAt cfg st).any (· ≤ now_ms) then sealWaiting cfg st else st

def choose (cfg : Config) (now_ms : Nat) (st : State σ) : State σ × Act σ :=
  if st.busy then (st, .wait none)
  else match st.pending with
    | u :: _ =>
      if st.retryAt_ms ≤ now_ms then ({ st with busy := true }, .put u)
      else (st, .wait (soonest ((sealAt cfg st).map (· - now_ms)) (some (st.retryAt_ms - now_ms))))
    | [] => (st, .wait ((sealAt cfg st).map (· - now_ms)))

def take (cfg : Config) (now_ms : Nat) (st : State σ) : State σ × Act σ :=
  choose cfg now_ms (ripen cfg now_ms st)

/-- Nothing waits and nothing is pending. -/
def State.idle (st : State σ) : Bool := st.count == 0 && st.pending.isEmpty

/-! ## What is shipped is the history -/

/-- The entries of `history` from position `first` on, as many as `entries` has. -/
def Slice (history : List (Entry σ)) (first : Nat) (entries : List (Entry σ)) : Prop :=
  entries = (history.drop first).take entries.length

theorem Slice.append {history entries : List (Entry σ)} {first : Nat}
    (h : Slice history first entries) (more : List (Entry σ)) :
    Slice (history ++ more) first entries := by
  unfold Slice at *
  have hle : entries.length ≤ (history.drop first).length := by
    have := congrArg List.length h
    rw [List.length_take] at this
    omega
  rw [List.drop_append, List.take_append_of_le_length hle]
  exact h

/-- What the shipper holds of a shard whose history is `history`: the waiting and the noted
entries are its tail from `next`, and every pending segment is a slice of it. -/
structure Holds (history : List (Entry σ)) (st : State σ) : Prop where
  next_le : st.next ≤ history.length
  tail : st.waitingRev.reverse ++ st.noted = history.drop st.next
  count : st.count = st.waitingRev.length
  slices : ∀ first entries, .segment first entries ∈ st.pending → Slice history first entries

theorem Holds.start {before past : List (Entry σ)} (snapshot : Option (Nat × ByteArray))
    (now_ms shipped : Nat) :
    Holds (before ++ past) (start before.length past snapshot now_ms shipped) where
  next_le := by simp [Ship.start]; omega
  tail := by
    show (past.drop _).reverse.reverse ++ [] = _
    rw [List.reverse_reverse, List.append_nil, List.drop_append,
      List.drop_eq_nil_of_le (as := before) (by simp [Ship.start]), List.nil_append]
    simp [Ship.start]
  count := by simp [Ship.start]
  slices := by
    intro first entries h
    cases snapshot <;> simp [Ship.start] at h

theorem enqueue_mem (cfg : Config) (st : State σ) (u : Upload σ) :
    ∀ x ∈ (enqueue cfg st u).pending, x ∈ st.pending ∨ x = u := by
  intro x hx
  unfold enqueue at hx
  split at hx
  · simpa using hx
  · simp only [List.mem_append, List.mem_singleton] at hx
    exact hx.imp_left fun hm => (shed_sublist _ _).subset hm

theorem Holds.enqueue {history : List (Entry σ)} {st : State σ} (h : Holds history st)
    (cfg : Config) {u : Upload σ}
    (hu : ∀ first entries, u = .segment first entries → Slice history first entries) :
    Holds history (enqueue cfg st u) := by
  have hsame : (Ship.enqueue cfg st u).next = st.next ∧ (Ship.enqueue cfg st u).waitingRev
      = st.waitingRev ∧ (Ship.enqueue cfg st u).noted = st.noted
      ∧ (Ship.enqueue cfg st u).count = st.count := by
    unfold Ship.enqueue; split <;> exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨h1, h2, h3, h4⟩ := hsame
  refine ⟨h1 ▸ h.next_le, h1 ▸ h2 ▸ h3 ▸ h.tail, h4 ▸ h2 ▸ h.count, ?_⟩
  intro first entries hmem
  rcases enqueue_mem cfg st u _ hmem with hmem | rfl
  · exact h.slices first entries hmem
  · exact hu first entries rfl

theorem Holds.sealWaiting {history : List (Entry σ)} {st : State σ} (h : Holds history st)
    (cfg : Config) : Holds history (sealWaiting cfg st) := by
  unfold Ship.sealWaiting
  split
  · exact h
  · have hslice : Slice history st.next st.waitingRev.reverse := by
      unfold Slice
      rw [← h.tail, List.take_left' (by simp)]
    have he := h.enqueue cfg (u := .segment st.next st.waitingRev.reverse) (by
      intro first entries hu
      cases hu
      exact hslice)
    have hlen := congrArg List.length h.tail
    simp only [List.length_append, List.length_reverse, List.length_drop] at hlen
    refine ⟨?_, ?_, rfl, he.slices⟩
    · simp only
      rw [h.count]
      have := h.next_le
      omega
    · simp only [List.reverse_nil, List.nil_append]
      have hnoted : (Ship.enqueue cfg st (.segment st.next st.waitingRev.reverse)).noted
          = st.noted := by
        unfold Ship.enqueue; split <;> rfl
      rw [hnoted, h.count]
      calc st.noted = (st.waitingRev.reverse ++ st.noted).drop st.waitingRev.reverse.length :=
            (List.drop_left' rfl).symm
        _ = (history.drop st.next).drop st.waitingRev.length := by rw [h.tail, List.length_reverse]
        _ = history.drop (st.next + st.waitingRev.length) := by rw [List.drop_drop]

theorem Holds.wrote {history : List (Entry σ)} {st : State σ} (h : Holds history st)
    (cfg : Config) (now_ms : Nat) (entries : List (Entry σ)) (durable : Bool) :
    Holds (history ++ entries) (wrote cfg now_ms entries durable st) := by
  have hdrop : (history ++ entries).drop st.next = history.drop st.next ++ entries :=
    List.drop_append_of_le_length h.next_le
  have hslices : ∀ first entries', .segment first entries' ∈ st.pending →
      Slice (history ++ entries) first entries' :=
    fun first entries' hmem => (h.slices first entries' hmem).append entries
  unfold Ship.wrote
  cases durable with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨by simp; have := h.next_le; omega, ?_, h.count, hslices⟩
    simp only [← List.append_assoc, h.tail, hdrop]
  | true =>
    simp only [↓reduceIte]
    have hmoved : Holds (history ++ entries) { st with
        waitingRev := (st.noted ++ entries).reverse ++ st.waitingRev
        count := st.count + (st.noted ++ entries).length, noted := []
        since_ms := st.since_ms.or
          (if (st.noted ++ entries).isEmpty then none else some now_ms) } :=
      ⟨by simp; have := h.next_le; omega,
       by simp only [List.reverse_append, List.reverse_reverse, List.append_nil,
         List.append_assoc]; rw [← List.append_assoc, h.tail, hdrop],
       by simp [h.count]; omega, hslices⟩
    split
    · exact hmoved.sealWaiting cfg
    · exact hmoved

theorem Holds.answer {history : List (Entry σ)} {st : State σ} (h : Holds history st)
    (cfg : Config) (now_ms : Nat) (outcome : Outcome) :
    Holds history (answer cfg now_ms outcome st) := by
  unfold Ship.answer
  split
  · exact h
  · cases outcome
    · exact ⟨h.next_le, h.tail, h.count, fun f e hm => h.slices f e (List.mem_of_mem_tail hm)⟩
    · exact ⟨h.next_le, h.tail, h.count, fun f e hm => h.slices f e (List.mem_of_mem_tail hm)⟩
    · exact ⟨h.next_le, h.tail, h.count, h.slices⟩

/-- The shipper keeps what it holds a slice of the history, through every event: a write
extends the history by its entries, and nothing else changes it. -/
theorem Holds.step {history : List (Entry σ)} {st : State σ} (h : Holds history st)
    (cfg : Config) (now_ms : Nat) (e : Event σ) :
    Holds (match e with | .wrote entries _ => history ++ entries | _ => history)
      (step cfg now_ms st e) := by
  cases e with
  | wrote entries durable => exact h.wrote cfg now_ms entries durable
  | saved index bytes => exact (h.sealWaiting cfg).enqueue cfg (by intro _ _ hu; cases hu)
  | put outcome => exact h.answer cfg now_ms outcome
  | closing => exact h.sealWaiting cfg

theorem Holds.ripen {history : List (Entry σ)} {st : State σ} (h : Holds history st)
    (cfg : Config) (now_ms : Nat) : Holds history (ripen cfg now_ms st) := by
  unfold Ship.ripen
  split
  · exact h.sealWaiting cfg
  · exact h

theorem Holds.take {history : List (Entry σ)} {st : State σ} (h : Holds history st)
    (cfg : Config) (now_ms : Nat) : Holds history (take cfg now_ms st).1 := by
  have hs := h.ripen cfg now_ms
  unfold Ship.take
  generalize Ship.ripen cfg now_ms st = s at hs
  unfold choose
  split
  · exact hs
  · split
    · split
      · exact ⟨hs.next_le, hs.tail, hs.count, hs.slices⟩
      · exact hs
    · exact hs

/-- Every segment the shipper puts is a slice of the history: it holds the entries at the
positions its key names. -/
theorem Holds.put {history : List (Entry σ)} {st : State σ} (h : Holds history st)
    (cfg : Config) (now_ms : Nat) {first : Nat} {entries : List (Entry σ)}
    (hput : (Ship.take cfg now_ms st).2 = .put (.segment first entries)) :
    Slice history first entries := by
  have hs := h.ripen cfg now_ms
  unfold Ship.take at hput
  generalize Ship.ripen cfg now_ms st = s at hs hput
  unfold choose at hput
  split at hput
  · cases hput
  · split at hput
    · next u rest hpending =>
      split at hput
      · cases hput
        exact hs.slices first entries (by rw [hpending]; exact List.mem_cons_self)
      · cases hput
    · cases hput

end Lanes.Journal.Ship
