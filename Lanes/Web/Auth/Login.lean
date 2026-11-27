/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Lib.Crypto.Sodium
public import Lanes.Data.Declare

/-!
What an actor that lets users log in keeps, as pure data: the digest of a password, the count of
failed attempts that locks an account, and the bounded list of a user's sessions.

A password never enters a system. Its digest (`Password.digest`, Argon2id) is derived where the
request arrives, on the task that reads it and not in the shard, so the journal, which records
what the system was asked, holds digests only. The salt is derived from the user's name and a
secret of the deployment, because the digest of a log-in is computed before the system, which
could hold a random salt, has seen it.
-/

@[expose] public section

namespace Lanes.Auth

/-- A password digest. Two are compared in time that does not depend on where they differ, so
`if d = stored` in a step function does not leak the stored digest byte by byte. -/
structure Digest where
  bytes : ByteArray

instance : DecidableEq Digest := fun a b =>
  if h : Bytes.same a.bytes b.bytes then
    isTrue (by cases a; cases b; exact congrArg _ ((Bytes.same_iff _ _).mp h))
  else isFalse (by intro heq; exact h ((Bytes.same_iff _ _).mpr (heq ▸ rfl)))

instance : Hashable Digest := ⟨fun d => hash d.bytes⟩

instance : Repr Digest := ⟨fun d _ => s!"<digest {(Bytes.hex d.bytes).take 8}>"⟩

def Digest.codec : Codec Digest :=
  Codec.bytes.map (·.bytes) (fun b => some ⟨b⟩) (fun _ => rfl)

instance : Codable Digest := ⟨Digest.codec⟩

/-- A digest as text, so that a request prepared where it arrives can carry it into the bridge
in place of the password. -/
def Digest.hex (d : Digest) : String := Bytes.hex d.bytes

def Digest.ofHex? (s : String) : Option Digest := (Bytes.unhex? s).map (⟨·⟩)

theorem Digest.ofHex?_hex (d : Digest) : ofHex? d.hex = some d := by
  simp [ofHex?, hex, Bytes.unhex?_hex]

structure Password where
  cost : Argon2id
  /-- A secret of the deployment, kept with its key; changing it changes every digest. -/
  pepper : ByteArray

def Password.salt (config : Password) (user : String) : ByteArray :=
  (hmac config.pepper ("salt\x00" ++ user).toUTF8).extract 0 16

theorem Password.size_salt (config : Password) (user : String) : (config.salt user).size = 16 := by
  simp [Password.salt, Hmac.size_hmac]

def Password.digest (config : Password) (user password : String) : Digest :=
  ⟨config.cost.hash password.toUTF8 (config.salt user) (config.size_salt user)⟩

/-- Failed log-ins since the account was last unlocked. At `limit` the account locks, and stays
locked until the application unlocks it, by a timer or by hand. -/
lanes_data structure Attempts where
  failures : Nat := 0
  locked : Bool := false
  deriving DecidableEq, Repr, Hashable, Codable

namespace Attempts

def fail (a : Attempts) (limit : Nat) : Attempts :=
  let failures := a.failures + 1
  { failures := min failures limit, locked := a.locked || limit ≤ failures }

def succeed (a : Attempts) : Attempts :=
  { a with failures := 0 }

def unlock : Attempts := {}

/-- What a run of log-ins can do: never more than `limit` failures are counted, and an account
with that many is locked. -/
def Bounded (limit : Nat) (a : Attempts) : Prop :=
  a.failures ≤ limit ∧ (a.failures = limit → 0 < limit → a.locked)

theorem bounded_fail (limit : Nat) (a : Attempts) : Bounded limit (a.fail limit) := by
  simp only [Bounded, fail]
  refine ⟨Nat.min_le_right .., fun heq hpos => ?_⟩
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  omega

theorem bounded_succeed (limit : Nat) (a : Attempts) : Bounded limit a.succeed := by
  simp only [Bounded, succeed]
  omega

/-- `n + 1` failures in a row: the count stops at `limit`, and the account is locked from the
failure that brings it there. -/
theorem fail_repeat (limit : Nat) (a : Attempts) (n : Nat) :
    Nat.repeat (·.fail limit) (n + 1) a
      = { failures := min (a.failures + n + 1) limit,
          locked := a.locked || decide (limit ≤ a.failures + n + 1) } := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.repeat, ih]
    simp only [fail, mk.injEq]
    refine ⟨by omega, ?_⟩
    apply Bool.eq_iff_iff.mpr
    cases a.locked <;> simp <;> omega

/-- From `unlock`, an account is locked exactly once it has failed `limit` times in a row, and at
least once. -/
theorem locked_unlock_repeat (limit n : Nat) :
    (Nat.repeat (·.fail limit) n unlock).locked = (decide (0 < n) && decide (limit ≤ n)) := by
  cases n with
  | zero => rfl
  | succ n =>
    rw [fail_repeat limit unlock n]
    simp [unlock, Nat.add_comm]

/-- Only `unlock` unlocks an account. -/
theorem locked_stays {a : Attempts} (h : a.locked) (limit : Nat) :
    (a.fail limit).locked ∧ a.succeed.locked := by
  simp [fail, succeed, h]

end Attempts

/-- A user's open sessions, newest first, at most `limit` of them: opening one more closes the
oldest. A session is named by a number the application never uses twice. -/
lanes_data structure Sessions where
  ids : List Nat := []
  deriving DecidableEq, Repr, Hashable, Codable

namespace Sessions

/-- The sessions after `id` is opened, and those it closed. -/
def start (s : Sessions) (limit id : Nat) : Sessions × List Nat :=
  let ids := id :: s.ids
  (⟨ids.take limit⟩, ids.drop limit)

def close (s : Sessions) (id : Nat) : Sessions :=
  ⟨s.ids.erase id⟩

def live (s : Sessions) (id : Nat) : Bool :=
  s.ids.contains id

theorem length_start_le (s : Sessions) (limit id : Nat) : (s.start limit id).1.ids.length ≤ limit :=
  List.length_take_le ..

theorem live_open (s : Sessions) {limit : Nat} (id : Nat) (h : 0 < limit) :
    (s.start limit id).1.live id := by
  cases limit with
  | zero => omega
  | succ n => simp [start, live]

/-- Opening a session keeps the newest `limit`, the new one first, and closes the others, the
oldest; it closes none while there is room. -/
theorem start_kept_closed (s : Sessions) (limit id : Nat) :
    (s.start limit id).1.ids ++ (s.start limit id).2 = id :: s.ids
      ∧ (s.start limit id).1.ids.length = min (s.ids.length + 1) limit := by
  simp [start, List.take_append_drop, Nat.min_comm]

/-- After any run of log-ins from at most `limit` sessions, the sessions are the `limit` newest. -/
theorem ids_starts (limit : Nat) (ids : List Nat) {s : Sessions} (h : s.ids.length ≤ limit) :
    (ids.foldl (fun s id => (s.start limit id).1) s).ids = (ids.reverse ++ s.ids).take limit := by
  induction ids generalizing s with
  | nil => simp [List.take_of_length_le h]
  | cons id ids ih =>
    rw [List.foldl_cons, ih (length_start_le s limit id)]
    simp only [start, List.reverse_cons, List.append_assoc, List.singleton_append,
      List.take_append, List.take_take]
    congr 2
    omega

/-- A closed session is not live, and closing one leaves the others as they were, when no
session is named twice. -/
theorem live_close {s : Sessions} (h : s.ids.Nodup) (id id' : Nat) :
    (s.close id).live id' = (s.live id' && id' != id) := by
  apply Bool.eq_iff_iff.mpr
  simp only [close, live, List.contains_iff_mem, Bool.and_eq_true, bne_iff_ne, ne_eq,
    h.mem_erase_iff]
  exact and_comm

end Sessions

end Lanes.Auth
