/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Web.S3.Basic

/-!
A multipart upload, for an object too large for one request or one that should survive a part
lost: S3 takes up to 10,000 parts of 5 MiB to 5 GiB each, the last of any size, and makes the
object of the parts a CompleteMultipartUpload lists, in order.

`Plan` cuts a body into parts S3 takes: every part but the last of the part size, at least
5 MiB, no more than 10,000, and together the whole body in order (`Plan.count_le`,
`Plan.range_full`, `Plan.range_next`, `Plan.range_last`). `Flow` is an upload from the server, a
pure machine: what to send next (`Flow.next`) and what an answer, or none, does (`Flow.answer`).
It retries each call up to `maxAttempts`, aborts an upload it gives up on, and when a Complete
whose answer was lost is then refused because the upload is gone, asks the object's `HEAD`
rather than guess. `S3.upload` (`Lanes/Web/IO/S3.lean`) only performs it. It is model-checked
against `Lanes.Multipart`'s model of the store (`Tests/Multipart.lean`).
-/

@[expose] public section

namespace Lanes.S3.Multipart

def minPart_bytes : Nat := 5 * 1024 ^ 2

def maxPart_bytes : Nat := 5 * 1024 ^ 3

def maxParts : Nat := 10000

/-- The largest object S3 holds: 5 TiB. -/
def maxObject_bytes : Nat := 5 * 1024 ^ 4

abbrev PartSize := {n : Nat // minPart_bytes ≤ n ∧ n ≤ maxPart_bytes}

/-- A body of `size` bytes, cut in parts of `partSize` bytes, the last what is left. -/
structure Plan where
  size : Nat
  partSize : PartSize
  fits : size ≤ maxParts * partSize.val
  deriving DecidableEq, Repr, Hashable

namespace Plan

/-- How many parts: one for an empty body. -/
def count (p : Plan) : Nat := max 1 ((p.size + p.partSize.val - 1) / p.partSize.val)

/-- The bytes of part `i`, from 0: from the first, to before the second. -/
def range (p : Plan) (i : Nat) : Nat × Nat :=
  (i * p.partSize.val, min p.size ((i + 1) * p.partSize.val))

def of? (size : Nat) (partSize : PartSize) : Option Plan :=
  if h : size ≤ maxParts * partSize.val then some ⟨size, partSize, h⟩ else none

/-- The smallest part size, in whole MiB and at least 5 MiB, that cuts `size` bytes into at most
10,000 parts. -/
def auto (size : Nat) (h : size ≤ maxObject_bytes) : Plan :=
  { size, partSize := ⟨max minPart_bytes (((size + 9999) / 10000 + 1048575) / 1048576 * 1048576), by
      simp only [maxObject_bytes, minPart_bytes, maxPart_bytes] at *; omega⟩
    fits := by simp only [maxParts, minPart_bytes] at *; omega }

private theorem ceil_spec (size ps : Nat) (hps : 0 < ps) :
    size ≤ (size + ps - 1) / ps * ps ∧ (size + ps - 1) / ps * ps < size + ps := by
  have h := Nat.div_add_mod (size + ps - 1) ps
  have hr := Nat.mod_lt (size + ps - 1) hps
  rw [Nat.mul_comm] at h
  omega

theorem partSize_pos (p : Plan) : 0 < p.partSize.val :=
  Nat.lt_of_lt_of_le (by decide) p.partSize.property.1

/-- At most 10,000 parts, as S3 takes. -/
theorem count_le (p : Plan) : p.count ≤ maxParts := by
  have hps := partSize_pos p
  have ⟨_, hlt⟩ := ceil_spec p.size p.partSize.val hps
  have hfits := p.fits
  have : (p.size + p.partSize.val - 1) / p.partSize.val < maxParts + 1 := by
    refine Nat.lt_of_mul_lt_mul_right (a := p.partSize.val) ?_
    rw [Nat.add_mul, Nat.one_mul]
    omega
  simp only [count, maxParts] at *
  omega

/-- Every part but the last is of the part size, so at least 5 MiB, as S3 requires. -/
theorem range_full (p : Plan) {i : Nat} (h : i + 1 < p.count) :
    (p.range i).2 - (p.range i).1 = p.partSize.val ∧ minPart_bytes ≤ p.partSize.val := by
  have hps := partSize_pos p
  have ⟨_, hlt⟩ := ceil_spec p.size p.partSize.val hps
  have hc : i + 2 ≤ (p.size + p.partSize.val - 1) / p.partSize.val := by
    simp only [count] at h; omega
  have hle := Nat.mul_le_mul_right p.partSize.val hc
  rw [Nat.add_mul] at hle
  refine ⟨?_, p.partSize.property.1⟩
  simp only [range, Nat.add_mul, Nat.one_mul]
  omega

/-- Each part begins where the one before ended. -/
theorem range_next (p : Plan) (i : Nat) (h : i + 1 < p.count) :
    (p.range i).2 = (p.range (i + 1)).1 := by
  have hps := partSize_pos p
  have ⟨_, hlt⟩ := ceil_spec p.size p.partSize.val hps
  have hc : i + 2 ≤ (p.size + p.partSize.val - 1) / p.partSize.val := by
    simp only [count] at h; omega
  have hle := Nat.mul_le_mul_right p.partSize.val hc
  rw [Nat.add_mul] at hle
  simp only [range, Nat.add_mul, Nat.one_mul]
  omega

/-- The first part begins the body and the last ends it. -/
theorem range_last (p : Plan) : (p.range 0).1 = 0 ∧ (p.range (p.count - 1)).2 = p.size := by
  have hps := partSize_pos p
  have ⟨hge, _⟩ := ceil_spec p.size p.partSize.val hps
  refine ⟨by simp [range], ?_⟩
  simp only [range]
  apply Nat.min_eq_left
  have hc : (p.size + p.partSize.val - 1) / p.partSize.val ≤ p.count - 1 + 1 := by
    simp only [count]; omega
  exact Nat.le_trans hge (Nat.mul_le_mul_right _ hc)

end Plan

/-- What the flow sends next. -/
inductive Step where
  | create
  /-- Part `number`, the bytes from `first` to before `stop`. -/
  | part (uploadId : String) (number : PartNumber) (first stop : Nat)
  | complete (uploadId : String) (manifest : Manifest)
  | abort (uploadId : String)
  /-- After a Complete whose answer was lost, refused as no such upload: is the object there? -/
  | check
  deriving DecidableEq, Repr, Hashable

inductive Phase where
  | creating
  /-- The parts answered so far, from the first, with their ETags. -/
  | uploading (uploadId : String) (done : List (PartNumber × String))
  /-- `lost`: a Complete was sent and its answer lost, so it may have taken effect. -/
  | completing (uploadId : String) (manifest : Manifest) (lost : Bool)
  | checking
  | aborting (uploadId : String) (why : String)
  | done (etag : Option String)
  | failed (why : String)
  deriving DecidableEq, Repr, Hashable

structure Flow where
  key : Key
  plan : Plan
  contentType : Option String := none
  /-- How many times a call is made before the flow gives up on it. -/
  maxAttempts : Nat := 3
  phase : Phase := .creating
  /-- Of the call now due, how many were made. -/
  attempts : Nat := 0
  deriving DecidableEq, Repr, Hashable

namespace Flow

def next (f : Flow) : Option Step :=
  match f.phase with
  | .creating => some .create
  | .uploading id done =>
    (PartNumber.of? (done.length + 1)).map fun n =>
      let (first, stop) := f.plan.range done.length
      .part id n first stop
  | .completing id m _ => some (.complete id m)
  | .checking => some .check
  | .aborting id _ => some (.abort id)
  | .done _ | .failed _ => none

def op (f : Flow) (body : ByteArray) : Step → Op
  | .create => .createUpload f.key f.contentType
  | .part id n first stop => .uploadPart f.key id n (body.extract first stop)
  | .complete id m => .completeUpload f.key id m
  | .abort id => .abortUpload f.key id
  | .check => .head f.key

/-- The call now due failed: made again, or given up on, to `otherwise`. -/
def retry (f : Flow) (otherwise : Phase) : Flow :=
  if f.attempts + 1 < f.maxAttempts then { f with attempts := f.attempts + 1 }
  else { f with phase := otherwise, attempts := 0 }

def moveTo (f : Flow) (phase : Phase) : Flow := { f with phase, attempts := 0 }

/-- An error S3 may give for a call that may succeed if made again. -/
def transient : Answer → Bool
  | .refused status code => status == 200 || 500 ≤ status || code == "SlowDown"
    || code == "RequestTimeout"
  | .unreadable => true
  | _ => false

def uploaded (f : Flow) (id : String) (done : List (PartNumber × String)) : Flow :=
  if done.length < f.plan.count then f.moveTo (.uploading id done)
  else match Manifest.of? done with
    | some m => f.moveTo (.completing id m false)
    | none => f.moveTo (.aborting id "the parts are out of order")

def onComplete (f : Flow) (id : String) (lost : Bool) : Option Answer → Flow
  | some (.completed etag) => f.moveTo (.done etag)
  | some (.refused _ "NoSuchUpload") =>
    f.moveTo (if lost then .checking else .failed "the upload is gone")
  | some a =>
    if transient a then
      markLost lost (f.retry (if lost then .checking else .aborting id "Complete was refused"))
    else f.moveTo (.aborting id "Complete was refused")
  | none => markLost true (f.retry .checking)
where
  markLost (lost : Bool) (g : Flow) : Flow :=
    match g.phase with
    | .completing id m was => { g with phase := .completing id m (was || lost) }
    | _ => g

/-- What the flow does with the answer to the call `next` gave, or with none by its deadline. -/
def answer (f : Flow) (a : Option Answer) : Flow :=
  match f.phase, a with
  | .creating, some (.started id) => f.moveTo (.uploading id [])
  | .creating, _ => f.retry (.failed "the upload could not begin")
  | .uploading id done, some (.stored (some etag)) =>
    match PartNumber.of? (done.length + 1) with
    | some n => f.uploaded id (done ++ [(n, etag)])
    | none => f.moveTo (.aborting id "too many parts")
  | .uploading id _, _ => f.retry (.aborting id "a part could not be uploaded")
  | .completing id _ lost, a => f.onComplete id lost a
  | .checking, some (.found info) =>
    f.moveTo (if info.size == f.plan.size then .done info.etag else .failed "another object is there")
  | .checking, some .missing => f.moveTo (.failed "the upload did not complete")
  | .checking, _ => f.retry (.failed "the object could not be checked")
  | .aborting _ why, some .deleted => f.moveTo (.failed why)
  | .aborting _ why, some (.refused _ "NoSuchUpload") => f.moveTo (.failed why)
  | .aborting _ why, _ => f.retry (.failed (why ++ "; the abort was not confirmed"))
  | .done _, _ | .failed _, _ => f

/-- An upload of `size` bytes to `key`, cut as `Plan.auto` cuts it. -/
def start (key : Key) (plan : Plan) (contentType : Option String := none)
    (maxAttempts : Nat := 3) : Flow :=
  { key, plan, contentType, maxAttempts }

/-- How many calls the flow makes at most: each part, the create, the complete, a check and an
abort, each up to `maxAttempts` times. -/
def bound (f : Flow) : Nat := (f.plan.count + 4) * (f.maxAttempts + 1)

end Flow

end Lanes.S3.Multipart
