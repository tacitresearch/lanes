/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
# When to fetch credentials that expire

Credentials of a role (an instance's, a container's) come with an expiry and must be fetched
again before it. This is the policy, as a pure machine: when to fetch, what an answer or a
timeout does, and which credentials may be handed out now. The edge
(`Aws/IO/Credentials.lean`) reads the clock, ticks the machine at the time it asks for, makes the
fetch it says and tells it the answer; it decides nothing.

The time is in every message, as the clock read it in milliseconds, so the machine needs no
clock of its own. A fetch is a call with an id and a deadline (`Rpc.Call`), answered with the
credentials or `unknown`, as a model of the service sees it (`Lanes.Rpc`).

- Credentials are handed out only while more than `skew_ms` is left before they expire
  (`current_fresh`), and only credentials an answer gave are held (`held_answered`).
- Credentials are fetched again `margin_ms` before they expire, and up to `jitter_ms` earlier, so
  a fetch answered within its deadline replaces them while they are still handed out
  (`refresh_in_time`).
- A fetch that fails is tried again after a wait that doubles from `backoff_ms` up to
  `maxBackoff_ms` (`backoff_le`, `retry_within`), while the credentials held last and after.
-/

namespace Aws.Refresh

open Lanes

structure Config where
  /-- Credentials are fetched again this long before they expire. -/
  margin_ms : Nat := 300000
  /-- And up to this much earlier still, by a jitter the edge draws, so that many processes do
  not fetch at once. -/
  jitter_ms : Nat := 60000
  /-- Credentials this close to their expiry are not handed out: a request signed with them must
  still reach the service before they expire. -/
  skew_ms : Nat := 60000
  /-- How long a fetch may take before it counts as failed. -/
  deadline_ms : Nat := 10000
  /-- The wait after the first failure; it doubles with each failure after it. -/
  backoff_ms : Nat := 1000
  maxBackoff_ms : Nat := 60000
  deriving DecidableEq, Repr, Hashable

/-- A configuration in which the refresh can win the race: a fetch started at the margin and
answered by its deadline arrives while the credentials held are still handed out, and a failure
waits at least a millisecond. -/
def Config.Valid (cfg : Config) : Prop :=
  cfg.deadline_ms + cfg.skew_ms < cfg.margin_ms ∧ 0 < cfg.backoff_ms ∧ cfg.backoff_ms ≤ cfg.maxBackoff_ms

instance (cfg : Config) : Decidable cfg.Valid := by unfold Config.Valid; infer_instance

/-- Credentials and when they expire, in milliseconds since the epoch. -/
structure Held (C : Type) where
  creds : C
  expires_ms : Nat
  deriving DecidableEq, Repr, Hashable

inductive Phase where
  /-- Nothing in flight; the next fetch at `wake_ms`. -/
  | waiting (wake_ms : Nat)
  /-- Fetch `call` in flight, given up at `giveUp_ms`. -/
  | fetching (call : Nat) (giveUp_ms : Nat)
  deriving DecidableEq, Repr, Hashable

structure State (C : Type) where
  held : Option (Held C) := none
  phase : Phase := .waiting 0
  /-- The wait after the last failure, `0` after a success. -/
  backoff_ms : Nat := 0
  nextCall : Nat := 0
  deriving DecidableEq, Repr, Hashable

inductive Msg (C : Type) where
  /-- The clock reads `now_ms`. -/
  | tick (now_ms : Nat)
  /-- Fetch `call` is answered at `now_ms`, with `jitter_ms` drawn by the edge, which is taken
  only up to `Config.jitter_ms`. -/
  | reply (now_ms : Nat) (call : Nat) (reply : Rpc.Reply (Held C)) (jitter_ms : Nat)
  deriving DecidableEq, Repr, Hashable

variable {C : Type} (cfg : Config)

/-- The wait after one more failure. -/
def nextBackoff (backoff_ms : Nat) : Nat :=
  min cfg.maxBackoff_ms (if backoff_ms = 0 then cfg.backoff_ms else 2 * backoff_ms)

/-- A fetch failed at `now`: wait, longer each time. What is held is kept. -/
def failed (s : State C) (now : Nat) : State C :=
  let wait := nextBackoff cfg s.backoff_ms
  { s with phase := .waiting (now + wait), backoff_ms := wait }

/-- When credentials `h` are to be fetched again, with jitter `jitter`. -/
def due (h : Held C) (jitter : Nat) : Nat :=
  h.expires_ms - cfg.margin_ms - min jitter cfg.jitter_ms

/-- An answer with `h` at `now`. Credentials not good for more than `skew_ms` are a failure.
Credentials good for less than the margin are held, but the next fetch waits as after a failure,
so a service that keeps giving them is not asked in a loop. -/
def accept (s : State C) (now : Nat) (h : Held C) (jitter : Nat) : State C :=
  if now + cfg.skew_ms < h.expires_ms then
    if now < due cfg h jitter then { s with held := some h, phase := .waiting (due cfg h jitter), backoff_ms := 0 }
    else failed cfg { s with held := some h } now
  else failed cfg s now

def step (s : State C) : Msg C → State C × Option (Rpc.Call Unit)
  | .tick now =>
    match s.phase with
    | .waiting wake =>
      if wake ≤ now then
        ({ s with phase := .fetching s.nextCall (now + cfg.deadline_ms), nextCall := s.nextCall + 1 },
          some ⟨s.nextCall, cfg.deadline_ms, ()⟩)
      else (s, none)
    | .fetching _ giveUp => if giveUp ≤ now then (failed cfg s now, none) else (s, none)
  | .reply now call reply jitter =>
    match s.phase with
    | .fetching c _ =>
      if c = call then
        match reply with
        | .answer h => (accept cfg s now h jitter, none)
        | .unknown => (failed cfg s now, none)
      else (s, none)
    | .waiting _ => (s, none)

/-- The credentials to sign with at `now`, if any may be. -/
def current (s : State C) (now : Nat) : Option C :=
  s.held.bind fun h => if now + cfg.skew_ms < h.expires_ms then some h.creds else none

/-- When the machine wants its next tick. -/
def State.wake (s : State C) : Nat :=
  match s.phase with
  | .waiting wake => wake
  | .fetching _ giveUp => giveUp

/-- The state after `msgs`, from `s`. -/
def run (s : State C) (msgs : List (Msg C)) : State C :=
  msgs.foldl (fun s msg => (step cfg s msg).1) s

/-- The credentials the answers among `msgs` gave. -/
def answers (msgs : List (Msg C)) : List (Held C) :=
  msgs.filterMap fun
    | .reply _ _ (.answer h) _ => some h
    | _ => none

/-! ## What is proved -/

/-- What is handed out is held, and good for more than `skew_ms` after `now`. -/
theorem current_fresh {s : State C} {now : Nat} {c : C} (h : current cfg s now = some c) :
    ∃ held, s.held = some held ∧ held.creds = c ∧ now + cfg.skew_ms < held.expires_ms := by
  unfold current at h
  cases hs : s.held with
  | none => simp [hs] at h
  | some held =>
    simp only [hs, Option.bind_some] at h
    split at h
    · exact ⟨held, rfl, Option.some.inj h, by assumption⟩
    · simp at h

/-- And what is held and good for more than `skew_ms` is handed out. -/
theorem current_of_fresh {s : State C} {now : Nat} {held : Held C} (hs : s.held = some held)
    (h : now + cfg.skew_ms < held.expires_ms) : current cfg s now = some held.creds := by
  simp [current, hs, h]

theorem nextBackoff_le (b : Nat) : nextBackoff cfg b ≤ cfg.maxBackoff_ms := Nat.min_le_left _ _

theorem nextBackoff_pos (hv : cfg.Valid) (b : Nat) : 0 < nextBackoff cfg b := by
  obtain ⟨-, hb, hmax⟩ := hv
  unfold nextBackoff
  split <;> omega

theorem step_held (s : State C) (msg : Msg C) :
    (step cfg s msg).1.held = s.held ∨ ∃ now call h j, msg = .reply now call (.answer h) j ∧
      (step cfg s msg).1.held = some h := by
  cases msg with
  | tick now =>
    left
    simp only [step]
    split
    · split <;> rfl
    · split <;> rfl
  | reply now call reply jitter =>
    simp only [step]
    split
    · split
      · cases reply with
        | answer h =>
          simp only [accept, failed]
          split
          · split
            · exact .inr ⟨now, call, h, jitter, by subst_vars; rfl, rfl⟩
            · exact .inr ⟨now, call, h, jitter, by subst_vars; rfl, rfl⟩
          · exact .inl rfl
        | unknown => exact .inl rfl
      · exact .inl rfl
    · exact .inl rfl

/-- Only credentials an answer gave are ever held. -/
theorem held_answered (s : State C) (msgs : List (Msg C)) {h : Held C}
    (hheld : (run cfg s msgs).held = some h) : s.held = some h ∨ h ∈ answers msgs := by
  induction msgs generalizing s with
  | nil => exact .inl hheld
  | cons msg rest ih =>
    rcases ih _ hheld with h1 | h1
    · rcases step_held cfg s msg with h2 | ⟨now, call, h', j, rfl, h2⟩
      · exact .inl (h2 ▸ h1)
      · rw [h2] at h1
        obtain rfl := Option.some.inj h1
        exact .inr (by simp [answers])
    · exact .inr (by
        simp only [answers, List.filterMap_cons] at h1 ⊢
        split <;> simp_all)

/-- From the start, every credential ever handed out was given by an answer. -/
theorem current_answered (msgs : List (Msg C)) {now : Nat} {c : C}
    (h : current cfg (run cfg {} msgs) now = some c) :
    ∃ held ∈ answers msgs, held.creds = c ∧ now + cfg.skew_ms < held.expires_ms := by
  obtain ⟨held, hs, hc, hf⟩ := current_fresh cfg h
  rcases held_answered cfg {} msgs hs with h0 | hm
  · simp at h0
  · exact ⟨held, hm, hc, hf⟩

theorem step_backoff (s : State C) (msg : Msg C) :
    (step cfg s msg).1.backoff_ms = s.backoff_ms ∨ (step cfg s msg).1.backoff_ms = 0 ∨
      (step cfg s msg).1.backoff_ms = nextBackoff cfg s.backoff_ms := by
  cases msg with
  | tick now =>
    simp only [step]
    split
    · split
      · exact .inl rfl
      · exact .inl rfl
    · split
      · exact .inr (.inr rfl)
      · exact .inl rfl
  | reply now call reply jitter =>
    simp only [step]
    split
    · split
      · cases reply with
        | answer h =>
          simp only [accept, failed]
          split
          · split
            · exact .inr (.inl rfl)
            · exact .inr (.inr rfl)
          · exact .inr (.inr rfl)
        | unknown => exact .inr (.inr rfl)
      · exact .inl rfl
    · exact .inl rfl

/-- The wait between failed fetches never passes `maxBackoff_ms`. -/
theorem backoff_le (msgs : List (Msg C)) : (run cfg {} msgs).backoff_ms ≤ cfg.maxBackoff_ms := by
  suffices ∀ (s : State C), s.backoff_ms ≤ cfg.maxBackoff_ms →
      (run cfg s msgs).backoff_ms ≤ cfg.maxBackoff_ms from this {} (Nat.zero_le _)
  induction msgs with
  | nil => exact fun _ h => h
  | cons msg rest ih =>
    intro s hs
    apply ih
    rcases step_backoff cfg s msg with h | h | h <;> rw [h]
    · exact hs
    · exact Nat.zero_le _
    · exact nextBackoff_le cfg _

/-- A fetch given up at its deadline, or answered `unknown`, is tried again within
`maxBackoff_ms`, and not at once. -/
theorem retry_within (hv : cfg.Valid) {s : State C} {now : Nat} {msg : Msg C}
    (hmsg : (∃ call giveUp, s.phase = .fetching call giveUp ∧ giveUp ≤ now ∧ msg = .tick now) ∨
      (∃ call giveUp j, s.phase = .fetching call giveUp ∧ msg = .reply now call .unknown j)) :
    ∃ wait, (step cfg s msg).1.phase = .waiting (now + wait) ∧ 0 < wait ∧
      wait ≤ cfg.maxBackoff_ms ∧ (step cfg s msg).1.held = s.held := by
  refine ⟨nextBackoff cfg s.backoff_ms, ?_, nextBackoff_pos cfg hv _, nextBackoff_le cfg _, ?_⟩ <;>
  rcases hmsg with ⟨call, giveUp, hp, hu, rfl⟩ | ⟨call, giveUp, j, hp, rfl⟩
  all_goals first
    | simp [step, hp, failed, hu]
    | simp [step, hp, failed]

/-- A tick before the wake changes nothing. -/
theorem tick_early {s : State C} {w now : Nat} (hp : s.phase = .waiting w) (h : now < w) :
    step cfg s (.tick now) = (s, none) := by
  simp [step, hp, Nat.not_le.mpr h]

/-- Credentials accepted with more than the margin left are fetched again no later than the
margin before they expire, and not at once. -/
theorem accept_due (hv : cfg.Valid) {s : State C} {now j : Nat} {h : Held C}
    (hlong : now + cfg.margin_ms + min j cfg.jitter_ms < h.expires_ms) :
    ∃ w, accept cfg s now h j = { s with held := some h, phase := .waiting w, backoff_ms := 0 } ∧
      now < w ∧ w + cfg.margin_ms ≤ h.expires_ms := by
  obtain ⟨hmargin, -, -⟩ := hv
  have hdue : now < due cfg h j := by unfold due; omega
  have hs : now + cfg.skew_ms < h.expires_ms := by omega
  exact ⟨due cfg h j, by simp [accept, hs, hdue], hdue, by unfold due; omega⟩

/-- The refresh wins the race. Credentials `h` held, the next fetch due at `w` no later than the
margin before they expire: ticked at `w`, the machine fetches; until that fetch's deadline `h` is
handed out; and an answer by then, with credentials that have more than the margin left, is
handed out from that moment, and leaves the machine as it was, with the new credentials. So
while the edge ticks when asked and the service answers in time, credentials are never missing. -/
theorem refresh_in_time (hv : cfg.Valid) {s : State C} {h : Held C} {w : Nat}
    (hheld : s.held = some h) (hphase : s.phase = .waiting w)
    (hdue : w + cfg.margin_ms ≤ h.expires_ms) :
    (∀ t, t ≤ w + cfg.deadline_ms → current cfg s t = some h.creds) ∧
    (step cfg s (.tick w)).2 = some ⟨s.nextCall, cfg.deadline_ms, ()⟩ ∧
    ∀ t, w ≤ t → t ≤ w + cfg.deadline_ms →
      current cfg (step cfg s (.tick w)).1 t = some h.creds ∧
      ∀ h' j, t + cfg.margin_ms + min j cfg.jitter_ms < h'.expires_ms →
        let s₂ := (step cfg (step cfg s (.tick w)).1 (.reply t s.nextCall (.answer h') j)).1
        current cfg s₂ t = some h'.creds ∧
          ∃ w', s₂.held = some h' ∧ s₂.phase = .waiting w' ∧ t < w' ∧
            w' + cfg.margin_ms ≤ h'.expires_ms := by
  have hm := hv.1
  have hstep : step cfg s (.tick w) =
      ({ s with phase := .fetching s.nextCall (w + cfg.deadline_ms), nextCall := s.nextCall + 1 },
        some ⟨s.nextCall, cfg.deadline_ms, ()⟩) := by
    simp [step, hphase]
  refine ⟨fun t ht => current_of_fresh cfg hheld (by omega), by rw [hstep], fun t _ ht => ?_⟩
  rw [hstep]
  refine ⟨current_of_fresh cfg (s := { s with phase := _, nextCall := _ }) hheld (by omega),
    fun h' j hlong => ?_⟩
  obtain ⟨w', hacc, hw', hdue'⟩ := accept_due cfg hv (s := { s with
    phase := .fetching s.nextCall (w + cfg.deadline_ms), nextCall := s.nextCall + 1 }) hlong
  simp only [step, hacc]
  exact ⟨current_of_fresh cfg rfl (by have := hv.1; omega), w', rfl, rfl, hw', hdue'⟩

end Aws.Refresh
