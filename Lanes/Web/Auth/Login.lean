/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Web.Auth.Password
public import Lanes.Data.Declare

/-!
The policies of logging in, as pure data: the count of failed attempts that locks an account,
and the bounded list of a user's sessions with their lifetimes. A password's hash or digest is
`Lanes.Web.Auth.Password`'s.

Kept in an actor, they last as long as the process and are known only to it: a restart signs
everyone out and forgets failed attempts, and another instance knows none of them. An
application that runs as more than one process, or must keep them across a restart, keeps them
as rows (`Lanes/Web/Auth/Rows.lean`), which apply `Attempts` in each transaction.
-/

@[expose] public section

namespace Lanes.Auth

/-- Failed log-ins since the account was last unlocked. At `limit` the account locks, and stays
locked until the application unlocks it, by a timer or by hand. -/
structure Attempts where
  failures : Nat := 0
  locked : Bool := false
  deriving DecidableEq, Repr, Hashable

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

/-- How long a session lasts, in seconds: `idle_s` after it was last used, `absolute_s` after it
began. `none` is no limit, and `{}` a session that lasts until it is closed. -/
structure Lifetime where
  idle_s : Option Nat := none
  absolute_s : Option Nat := none
  deriving DecidableEq, Repr

/-- A session: its number, when it began and when it was last used, in seconds. -/
structure Session where
  id : Nat
  started_s : Nat := 0
  used_s : Nat := 0
  deriving DecidableEq, Repr, Hashable

/-- Whether the session is over at `now_s`. Once over, it stays over: `Session.expired_mono`. -/
def Session.expired (life : Lifetime) (now_s : Nat) (e : Session) : Bool :=
  life.idle_s.any (e.used_s + · ≤ now_s) || life.absolute_s.any (e.started_s + · ≤ now_s)

theorem Session.expired_mono {life : Lifetime} {t t' : Nat} {e : Session} (h : t ≤ t')
    (he : e.expired life t = true) : e.expired life t' = true := by
  simp only [expired, Bool.or_eq_true, Option.any_eq_true, decide_eq_true_eq] at he ⊢
  rcases he with ⟨x, hx, hle⟩ | ⟨x, hx, hle⟩
  · exact .inl ⟨x, hx, by omega⟩
  · exact .inr ⟨x, hx, by omega⟩

theorem Session.expired_none {now_s : Nat} {e : Session} : e.expired {} now_s = false := by
  simp [expired]

/-- A user's open sessions, newest first, at most `limit` of them: opening one more closes the
oldest. A session is named by a number the application never uses twice. Time is what the
application passes, the time a request arrived; `seen_s`, the latest it passed to a write, is the
earliest time expiry is judged at, so a clock that steps back does not bring a session back. -/
structure Sessions where
  entries : List Session := []
  seen_s : Nat := 0
  deriving DecidableEq, Repr, Hashable

namespace Sessions

/-- The numbers of the open sessions, newest first. -/
def ids (s : Sessions) : List Nat := s.entries.map (·.id)

/-- The time expiry is judged at for a request of `now_s`. -/
def at_s (s : Sessions) (now_s : Nat) : Nat := max s.seen_s now_s

/-- The sessions not over at `now_s`, and those that are, which it closes. -/
def sweep (s : Sessions) (life : Lifetime) (now_s : Nat) : Sessions × List Nat :=
  let t := s.at_s now_s
  (⟨s.entries.filter (!·.expired life t), t⟩, ((s.entries.filter (·.expired life t)).map (·.id)))

/-- The sessions after `id` is opened at `now_s`, and those it closed: the ones over by then,
and the oldest beyond `limit`. Without a time or a lifetime, no session is ever over. -/
def start (s : Sessions) (limit id : Nat) (now_s : Nat := 0) (life : Lifetime := {}) :
    Sessions × List Nat :=
  let (kept, over) := s.sweep life now_s
  let entries := ⟨id, kept.seen_s, kept.seen_s⟩ :: kept.entries
  (⟨entries.take limit, kept.seen_s⟩, over ++ (entries.drop limit).map (·.id))

def close (s : Sessions) (id : Nat) : Sessions :=
  { s with entries := s.entries.filter (·.id != id) }

/-- Whether `id` is open, whatever the time: for an application whose sessions do not expire. -/
def live (s : Sessions) (id : Nat) : Bool :=
  s.ids.contains id

/-- Whether a request of `now_s` is let in by session `id`: open, and not over then. -/
def accepts (s : Sessions) (life : Lifetime) (id : Nat) (now_s : Nat) : Bool :=
  s.entries.any fun e => e.id == id && !e.expired life (s.at_s now_s)

/-- The sessions after `id` was used at `now_s`: swept, and `id` used then if it is still open. -/
def touch (s : Sessions) (life : Lifetime) (id : Nat) (now_s : Nat) : Sessions :=
  let kept := (s.sweep life now_s).1
  { kept with entries := kept.entries.map fun e =>
      if e.id == id then { e with used_s := kept.seen_s } else e }

theorem ids_length (s : Sessions) : s.ids.length = s.entries.length := List.length_map ..

theorem length_start_le (s : Sessions) (limit id : Nat) (now_s : Nat := 0) (life : Lifetime := {}) :
    (s.start limit id now_s life).1.ids.length ≤ limit := by
  simp only [start, ids_length]
  exact List.length_take_le ..

theorem length_close_le (s : Sessions) (id : Nat) : (s.close id).ids.length ≤ s.ids.length := by
  simp only [close, ids_length]
  exact List.length_filter_le ..

theorem live_open (s : Sessions) {limit : Nat} (id : Nat) (h : 0 < limit) (now_s : Nat := 0)
    (life : Lifetime := {}) : (s.start limit id now_s life).1.live id := by
  cases limit with
  | zero => omega
  | succ n => simp [start, live, ids]

theorem sweep_none (s : Sessions) (now_s : Nat) :
    (s.sweep {} now_s).1.entries = s.entries ∧ (s.sweep {} now_s).2 = [] := by
  simp [sweep, Session.expired_none]

/-- Opening a session with no lifetime keeps the newest `limit`, the new one first, and closes
the others, the oldest; it closes none while there is room. -/
theorem start_kept_closed (s : Sessions) (limit id : Nat) (now_s : Nat := 0) :
    (s.start limit id now_s).1.ids ++ (s.start limit id now_s).2 = id :: s.ids
      ∧ (s.start limit id now_s).1.ids.length = min (s.ids.length + 1) limit := by
  have h := sweep_none s now_s
  simp only [start, ids, h.1, h.2, List.nil_append, ← List.map_append, List.take_append_drop,
    List.map_cons, List.length_map, List.length_take, List.length_cons, Nat.min_comm]
  constructor <;> simp

/-- After any run of log-ins from at most `limit` sessions, with no lifetime, the sessions are
the `limit` newest. -/
theorem ids_starts (limit : Nat) (ids : List Nat) {s : Sessions} (h : s.ids.length ≤ limit) :
    (ids.foldl (fun s id => (s.start limit id).1) s).ids = (ids.reverse ++ s.ids).take limit := by
  induction ids generalizing s with
  | nil => simp [List.take_of_length_le h]
  | cons id ids ih =>
    rw [List.foldl_cons, ih (length_start_le s limit id)]
    have hs := sweep_none s 0
    simp only [start, Sessions.ids, hs.1, List.map_take, List.map_cons, List.reverse_cons,
      List.append_assoc, List.singleton_append, List.take_append, List.take_take]
    congr 2
    omega

/-- A closed session is not live, and closing one leaves the others as they were. -/
theorem live_close (s : Sessions) (id id' : Nat) :
    (s.close id).live id' = (s.live id' && id' != id) := by
  apply Bool.eq_iff_iff.mpr
  simp only [close, live, ids, List.contains_iff_mem, List.mem_map, List.mem_filter,
    Bool.and_eq_true, bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨e, ⟨he, hne⟩, rfl⟩
    exact ⟨⟨e, he, rfl⟩, hne⟩
  · rintro ⟨⟨e, he, rfl⟩, hne⟩
    exact ⟨e, ⟨he, hne⟩, rfl⟩

/-- A session is let in only while it is open and not over, at the time of the request and at
every time a write was told of before it. -/
theorem accepts_iff {s : Sessions} {life : Lifetime} {id now_s : Nat} :
    s.accepts life id now_s = true
      ↔ ∃ e ∈ s.entries, e.id = id ∧ e.expired life (max s.seen_s now_s) = false := by
  simp [accepts, at_s]

/-- Session `id` is over for good: every entry of it is over at the latest time written. -/
def Ended (s : Sessions) (life : Lifetime) (id : Nat) : Prop :=
  ∀ e ∈ s.entries, e.id = id → e.expired life s.seen_s = true

theorem Ended.refused {s : Sessions} {life : Lifetime} {id : Nat} (h : s.Ended life id)
    (now_s : Nat) : s.accepts life id now_s = false := by
  apply Bool.eq_false_iff.mpr
  intro ha
  obtain ⟨e, he, rfl, hx⟩ := accepts_iff.mp ha
  have := Session.expired_mono (Nat.le_max_left _ now_s) (h e he rfl)
  simp_all

theorem Ended.sweep {s : Sessions} {life : Lifetime} {id : Nat} (h : s.Ended life id)
    (now_s : Nat) : (s.sweep life now_s).1.Ended life id := by
  intro e he hid
  simp only [Sessions.sweep, List.mem_filter, Bool.not_eq_true'] at he
  exact Session.expired_mono (Nat.le_max_left _ _) (h e he.1 hid)

/-- After a sweep, a session the sweep's time does not let in has ended. -/
theorem sweep_ended (s : Sessions) (life : Lifetime) (id now_s : Nat)
    (h : (s.sweep life now_s).1.accepts life id now_s = false) :
    (s.sweep life now_s).1.Ended life id := by
  intro e he hid
  simp only [Sessions.sweep, List.mem_filter, Bool.not_eq_true'] at he
  have : (s.sweep life now_s).1.accepts life id now_s = true := by
    refine accepts_iff.mpr ⟨e, ?_, hid, ?_⟩
    · simp [Sessions.sweep, he.1, he.2]
    · show Session.expired life (max (max s.seen_s now_s) now_s) e = false
      have hmax : max (max s.seen_s now_s) now_s = max s.seen_s now_s := by omega
      rw [hmax]
      exact he.2
  simp_all

/-- What can be done to a user's sessions, each at the time given. -/
inductive Op where
  | start (limit id now_s : Nat)
  | touch (id now_s : Nat)
  | close (id : Nat)
  | sweep (now_s : Nat)

def Op.apply (life : Lifetime) (s : Sessions) : Op → Sessions
  | .start limit id now_s => (s.start limit id now_s life).1
  | .touch id now_s => s.touch life id now_s
  | .close id => s.close id
  | .sweep now_s => (s.sweep life now_s).1

/-- Whether the operation opens session `id`, which an application never does twice. -/
def Op.opens (id : Nat) : Op → Bool
  | .start _ id' _ => id' == id
  | _ => false

theorem Ended.apply {s : Sessions} {life : Lifetime} {id : Nat} (h : s.Ended life id) (op : Op)
    (hop : op.opens id = false) : (op.apply life s).Ended life id := by
  cases op with
  | start limit id' now_s =>
    intro e he hid
    simp only [Op.apply, start] at he ⊢
    rcases List.mem_cons.mp (List.mem_of_mem_take he) with rfl | he
    · simp_all [Op.opens]
    · exact h.sweep now_s e he hid
  | touch id' now_s =>
    intro e he hid
    simp only [Op.apply, touch, List.mem_map] at he ⊢
    obtain ⟨e', he', rfl⟩ := he
    have hid' : e'.id = id := by split at hid <;> exact hid
    have hover := h.sweep now_s e' he' hid'
    simp only [Sessions.sweep, List.mem_filter] at he' hover
    simp_all
  | close id' =>
    intro e he hid
    simp only [Op.apply, close, List.mem_filter] at he ⊢
    exact h e he.1 hid
  | sweep now_s => exact h.sweep now_s

/-- An expired session is never let in again: once it has ended, no run of operations that does
not open it again lets in any request of it, at any time. -/
theorem Ended.run {s : Sessions} {life : Lifetime} {id : Nat} (h : s.Ended life id)
    (ops : List Op) (hops : ∀ op ∈ ops, op.opens id = false) (now_s : Nat) :
    (ops.foldl (Op.apply life) s).accepts life id now_s = false := by
  induction ops generalizing s with
  | nil => exact h.refused now_s
  | cons op ops ih =>
    exact ih (h.apply op (hops op (by simp))) fun o ho => hops o (by simp [ho])

end Sessions

end Lanes.Auth
