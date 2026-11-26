/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Actors.Journal

/-!
A snapshot file: a kernel's image and the index of its mark in the journal, as bytes. The
codec is built from the application's codecs for an identity, a state and a message, so its
round-trip law comes with it. A snapshot is written whole and renamed into place, so nothing is
repaired when one is read: a file that does not read back entirely is refused.
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

def savedHeader (system : String) : ByteArray :=
  ("lanes snapshot 1\n" ++ system).toUTF8

def savedRecords (c : Image.Codecs sys) (system : String) (index : Nat) (image : Image sys) :
    List ByteArray :=
  savedHeader system :: (Codec.pair .nat c.image).write (index, image)

/-- A snapshot file: the header, the index of the mark, the image, a frame per record. -/
def saved (c : Image.Codecs sys) (system : String) (index : Nat) (image : Image sys) :
    ByteArray :=
  Frame.encode (savedRecords c system index image)

def saved? (c : Image.Codecs sys) (system : String) (bytes : ByteArray) :
    Option (Nat × Image sys) :=
  match Frame.decode bytes with
  | first :: records =>
    if first = savedHeader system ∧ Frame.span (first :: records) = bytes.size then
      match (Codec.pair .nat c.image).read records with
      | some (found, []) => some found
      | _ => none
    else none
  | [] => none

theorem saved?_saved (c : Image.Codecs sys) (system : String) (index : Nat) (image : Image sys)
    (h : (savedRecords c system index image).all Frame.fits = true) :
    saved? c system (saved c system index image) = some (index, image) := by
  have hsound := (Codec.pair .nat c.image).sound (index, image) []
  rw [List.append_nil] at hsound
  simp only [saved?, saved, savedRecords] at h ⊢
  rw [Frame.decode_encode (Frame.all_fits_iff.mp h)]
  simp only [Frame.size_encode, hsound, and_self, ↓reduceIte]

end Journal

end Lanes
