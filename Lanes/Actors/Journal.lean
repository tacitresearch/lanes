/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Actors.Kernel
public import Lanes.Data.Codec

/-!
The journal of a shard: everything it asks of its kernel, in order. The kernel is a pure
function of those requests, so replaying a journal gives back the state it describes, and that
is how a shard survives its process (`DECISIONS.md` D24).

This file is the pure part: what an entry is, how entries become records, and that reading
records back gives the entries, or the entries before a cut if the records were cut short.
-/

@[expose] public section

namespace Lanes.Journal

variable {σ : Signature}

inductive Entry (σ : Signature) where
  | input (x : σ.In)
  | advance (now_ms : Nat)
  | batch (fuel : Nat)

/-- An entry is two records: which kind it is, then what it carries. -/
def Entry.records (codec : Codec σ.In) : Entry σ → List ByteArray
  | .input x => [Codec.nat.encode 0, codec.encode x]
  | .advance now_ms => [Codec.nat.encode 1, Codec.nat.encode now_ms]
  | .batch fuel => [Codec.nat.encode 2, Codec.nat.encode fuel]

def Entry.read (codec : Codec σ.In) (kind payload : ByteArray) : Option (Entry σ) :=
  match Codec.nat.decode kind with
  | some 0 => (codec.decode payload).map .input
  | some 1 => (Codec.nat.decode payload).map .advance
  | some 2 => (Codec.nat.decode payload).map .batch
  | _ => none

def write (codec : Codec σ.In) (entries : List (Entry σ)) : List ByteArray :=
  entries.flatMap (·.records codec)

/-- The entries at the start of `records`, up to the first that is incomplete or unreadable. -/
def read (codec : Codec σ.In) : List ByteArray → List (Entry σ)
  | kind :: payload :: rest =>
    match Entry.read codec kind payload with
    | some entry => entry :: read codec rest
    | none => []
  | _ => []

theorem Entry.read_records (codec : Codec σ.In) (entry : Entry σ) (rest : List ByteArray) :
    Journal.read codec (entry.records codec ++ rest) = entry :: Journal.read codec rest := by
  cases entry <;> simp [Entry.records, Journal.read, Entry.read, Codec.sound]

theorem read_write (codec : Codec σ.In) (entries : List (Entry σ)) :
    read codec (write codec entries) = entries := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    simp only [write, List.flatMap_cons] at ih ⊢
    rw [Entry.read_records, ih]

/-- Records cut short anywhere, even inside an entry, read back as the entries before the cut:
never a wrong entry and never one out of order. -/
theorem read_prefix (codec : Codec σ.In) (entries : List (Entry σ)) (records : List ByteArray)
    (h : records <+: write codec entries) : read codec records <+: entries := by
  induction entries generalizing records with
  | nil =>
    have : records = [] := List.eq_nil_of_prefix_nil h
    subst this
    exact List.nil_prefix
  | cons entry entries ih =>
    have hwrite : write codec (entry :: entries)
        = entry.records codec ++ write codec entries := by simp [write]
    rw [hwrite] at h
    obtain ⟨kind, payload, hrecords⟩ : ∃ kind payload, entry.records codec = [kind, payload] := by
      cases entry <;> exact ⟨_, _, rfl⟩
    rw [hrecords] at h
    match records, h with
    | [], _ => exact List.nil_prefix
    | [_], _ => exact List.nil_prefix
    | k :: p :: rest, h =>
      simp only [List.cons_append, List.nil_append, List.cons_prefix_cons] at h
      obtain ⟨hk, hp, h⟩ := h
      have := Entry.read_records codec entry rest
      rw [hrecords] at this
      simp only [List.cons_append, List.nil_append] at this
      rw [hk, hp, this]
      exact List.cons_prefix_cons.mpr ⟨rfl, ih rest h⟩

end Lanes.Journal
