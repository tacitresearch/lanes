/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Data.Hmac
public import Lanes.Data.Declare

/-!
What an actor that lets users log in keeps, as pure data: the digest of a password, the count of
failed attempts that locks an account, and the bounded list of a user's sessions.

A password never enters a system. The bridge derives its digest where the request arrives
(`Password.digest`), so the journal, which records what the system was asked, holds digests
only. The salt is derived from the user's name and a secret of the deployment, because the
bridge has to compute the digest of a log-in before the system, which could hold a random salt,
has seen it.
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

/-- The cost of a digest is `2 * iterations` SHA-256 blocks. -/
structure Password where
  iterations : Nat
  /-- A secret of the deployment, kept with its key; changing it changes every digest. -/
  pepper : ByteArray

def Password.salt (config : Password) (user : String) : ByteArray :=
  hmac config.pepper ("salt\x00" ++ user).toUTF8

def Password.digest (config : Password) (user password : String) : Digest :=
  ⟨pbkdf2 password.toUTF8 (config.salt user) config.iterations 32⟩

/-- Failed log-ins since the account was last unlocked. At `limit` the account locks, and stays
locked until the application unlocks it, by a timer or by hand. -/
lanes_data structure Attempts where
  failures : Nat
  locked : Bool
  deriving DecidableEq, Repr, Hashable, Codable

namespace Attempts

def none : Attempts := ⟨0, false⟩

def fail (a : Attempts) (limit : Nat) : Attempts :=
  let failures := a.failures + 1
  { failures := min failures limit, locked := a.locked || limit ≤ failures }

def succeed (a : Attempts) : Attempts :=
  { a with failures := 0 }

def unlock : Attempts := none

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

end Attempts

/-- A user's open sessions, newest first, at most `limit` of them: opening one more closes the
oldest. A session is named by a number the application never uses twice. -/
lanes_data structure Sessions where
  ids : List Nat
  deriving DecidableEq, Repr, Hashable, Codable

namespace Sessions

def none : Sessions := ⟨[]⟩

/-- The sessions after `id` is opened, and those it closed. -/
def start (s : Sessions) (limit id : Nat) : Sessions × List Nat :=
  let ids := id :: s.ids
  (⟨ids.take limit⟩, ids.drop limit)

def close (s : Sessions) (id : Nat) : Sessions :=
  ⟨s.ids.erase id⟩

def live (s : Sessions) (id : Nat) : Bool :=
  s.ids.contains id

theorem length_startle (s : Sessions) (limit id : Nat) : (s.start limit id).1.ids.length ≤ limit :=
  List.length_take_le ..

theorem live_open (s : Sessions) {limit : Nat} (id : Nat) (h : 0 < limit) :
    (s.start limit id).1.live id := by
  cases limit with
  | zero => omega
  | succ n => simp [start, live]

end Sessions

end Lanes.Auth
