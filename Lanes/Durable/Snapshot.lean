/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Durable.Journal

/-!
A snapshot file: a kernel's image and the index of its mark in the journal, as bytes, in format 2
(`Lanes/Durable/Format.lean`): the prelude, then the two as one body. The schema is built from the
application's codecs for an identity, a state and a message, so its law comes with it, and an
image written under an older schema is read by name. A snapshot is written whole and renamed into
place, so nothing is repaired when one is read: a file that does not read back entirely is
refused.
-/

@[expose] public section

namespace Lanes

variable {σ : Signature}

namespace Kernel

def Due.codec : Codec Due :=
  (Codec.pair .nat .nat).map (fun due => (due.deadline_ms, due.token))
    (fun (deadline_ms, token) => some ⟨deadline_ms, token⟩) (fun _ => rfl)

/-- How the actors of a system are written down. -/
structure Image.Codecs (sys : System σ) where
  id : Codec σ.Id
  state : ∀ i, Codec (sys.State i)
  msg : ∀ i, Codec (σ.Msg i)

namespace Image.Codecs

variable {sys : System σ} (c : Codecs sys)

def cell (i : σ.Id) : Codec (Cell sys i) :=
  (Codec.pair (c.state i) (Codec.pair .bool (Codec.list (Codec.pair (c.msg i) Due.codec)))).map
    (fun cell => (cell.state, cell.up, cell.timers))
    (fun (state, up, timers) => some { state, up, timers }) (fun _ => rfl)

def envelope : Codec (Envelope σ) :=
  (Codec.pair (Codec.option c.id) (Codec.sigma c.id c.msg)).map
    (fun e => (e.src, ⟨e.dst, e.msg⟩)) (fun (src, ⟨dst, msg⟩) => some ⟨src, dst, msg⟩)
    (fun _ => rfl)

def image : Codec (Image sys) :=
  (Codec.pair (Codec.list (Codec.sigma c.id c.cell)) (Codec.pair (Codec.list c.envelope)
    (Codec.pair (Codec.list (Codec.pair Due.codec (Codec.sigma c.id c.msg)))
      (Codec.pair .nat (Codec.pair .nat .bool))))).map
    (fun image => (image.cells, image.queue, image.agenda, image.nextToken, image.clock_ms,
      image.timerTurn))
    (fun (cells, queue, agenda, nextToken, clock_ms, timerTurn) =>
      some { cells, queue, agenda, nextToken, clock_ms, timerTurn })
    (fun _ => rfl)

end Image.Codecs

end Kernel

namespace Journal

open Kernel (Image)

variable {sys : System σ}

/-- What a snapshot file holds: the index of the mark and the image. -/
def savedOf (c : Image.Codecs sys) : Schema.Of (Nat × Image sys) :=
  (Codec.pair .nat c.image).toOf

def savedBody (c : Image.Codecs sys) (index : Nat) (image : Image sys) :
    Except Codec.Error ByteArray :=
  Body.encode Kind.snapshot.limits (savedOf c) (index, image)

/-- The frames of a snapshot file: the prelude, then the index of the mark and the image as one
body. -/
def savedRecords (c : Image.Codecs sys) (system : String) (index : Nat) (image : Image sys) :
    List ByteArray :=
  Prelude.frames .snapshot system (savedOf c).schema ++ [okBytes (savedBody c index image)]

/-- Whether the snapshot can be written: its prelude, and its body within the bounds of a
snapshot and of a frame. -/
def savedFits (c : Image.Codecs sys) (system : String) (index : Nat) (image : Image sys) : Bool :=
  Prelude.fits .snapshot system (savedOf c).schema
    && match savedBody c index image with
      | .ok bytes => Frame.fits bytes
      | .error _ => false

def saved (c : Image.Codecs sys) (system : String) (index : Nat) (image : Image sys) :
    ByteArray :=
  Frame.encode (savedRecords c system index image)

/-- What a snapshot file holds, or why it is refused. A snapshot is written whole and renamed
into place, so it is exactly four frames and nothing after; a body that does not read through
the plan is refused with the error that names where. -/
def savedOpen? (c : Image.Codecs sys) (system : String) (bytes : ByteArray) :
    Except Refusal (Nat × Image sys) :=
  match Frame.decode bytes with
  | [first, manifest, schema, body] =>
    if Frame.span [first, manifest, schema, body] = bytes.size then
      match Prelude.check .snapshot system (savedOf c).schema first manifest schema with
      | .error (.foreign _) => .error .snapshot
      | .error refusal => .error refusal
      | .ok (writer, plan) =>
        match Body.decodeWith Kind.snapshot.limits writer plan (savedOf c) body with
        | .ok found => .ok found
        | .error e => .error (.schema e)
    else .error .snapshot
  | _ => if Kind.snapshot.formerly bytes then .error (.format 1) else .error .snapshot

def saved? (c : Image.Codecs sys) (system : String) (bytes : ByteArray) :
    Option (Nat × Image sys) :=
  (savedOpen? c system bytes).toOption

private theorem savedBody_ok {c : Image.Codecs sys} {system : String} {index : Nat}
    {image : Image sys} (h : savedFits c system index image = true) :
    Prelude.fits .snapshot system (savedOf c).schema = true
      ∧ savedBody c index image = .ok (okBytes (savedBody c index image))
      ∧ Frame.fits (okBytes (savedBody c index image)) = true := by
  simp only [savedFits, Bool.and_eq_true] at h
  obtain ⟨hp, hb⟩ := h
  split at hb
  · next bytes hbody => exact ⟨hp, by rw [hbody]; rfl, by rw [hbody]; exact hb⟩
  · cases hb

private theorem decode_saved {c : Image.Codecs sys} {system : String} {index : Nat}
    {image : Image sys} (h : savedFits c system index image = true) :
    Frame.decode (saved c system index image) = savedRecords c system index image := by
  obtain ⟨hp, -, hb⟩ := savedBody_ok h
  refine Frame.decode_encode fun p hp' => ?_
  rcases List.mem_append.mp hp' with hp' | hp'
  · exact Prelude.fits_frames hp p hp'
  · rw [List.mem_singleton.mp hp']
    exact Frame.fits_iff.mp hb

/-- A snapshot of another system, or of another version of this one, is refused. -/
theorem saved?_other {τ : Signature} {other : System τ} (c₀ : Image.Codecs other)
    (c : Image.Codecs sys) {named system : String} (hne : named ≠ system) (index : Nat)
    (image : Image other) (h : savedFits c₀ named index image = true) :
    saved? c system (saved c₀ named index image) = none := by
  obtain ⟨hp, -, -⟩ := savedBody_ok h
  simp only [saved?, savedOpen?, decode_saved h]
  simp [savedRecords, Prelude.frames, saved, Frame.span, Prelude.check_other hp hne,
    Except.toOption]

theorem savedOpen?_saved (c : Image.Codecs sys) (system : String) (index : Nat)
    (image : Image sys) (h : savedFits c system index image = true) :
    savedOpen? c system (saved c system index image) = .ok (index, image) := by
  obtain ⟨hp, hbody, -⟩ := savedBody_ok h
  simp only [savedOpen?, decode_saved h]
  simp [savedRecords, Prelude.frames, saved, Frame.span, Prelude.check_frames hp,
    Body.decodeWith_same, Body.decode_encode hbody]

theorem saved?_saved (c : Image.Codecs sys) (system : String) (index : Nat) (image : Image sys)
    (h : savedFits c system index image = true) :
    saved? c system (saved c system index image) = some (index, image) := by
  simp [saved?, savedOpen?_saved c system index image h, Except.toOption]

end Journal

end Lanes
