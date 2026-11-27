/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Behaviours.Schedule.Basic
public import Lanes.Proof.Deed
public import Lanes.Proof.JoinSound
public import Lanes.Proof.Lift
public import Lanes.Core.Run

/-!
What the scheduler does, in every run and every environment, crashes and duplicating links
included:

- *No attempt too early.* An attempt is dispatched only when its job's `due` timer fires, for a
  job that waits, stamped with the scheduler's time then, which is no earlier than the time the
  job was due (`Schedule.dispatch_due`). After a failed attempt the job is due again the backoff
  after the time the failure was known (`Schedule.retry_waits`). The time never goes back
  (`Schedule.now_le_step`).
- *No more attempts than allowed.* Every job is within its attempts (`Schedule.attempts`), and no
  key is called more often than `max 1 maxAttempts` times for each scheduling of it handled
  (`Schedule.calls_le_scheduled`).
- *One attempt out per id.* No id is held twice and the jobs stay within `maxJobs`
  (`Schedule.within`); an attempt is dispatched only for a job with none out
  (`Schedule.dispatch_due`), and an attempt out ends only with its answer or, abandoned, with
  the end of its wait (`Schedule.attempt_ends`).
- While it is up, the timer each job waits on is armed (`Schedule.armed`).

`Lanes.Semantics.Schedule` builds the liveness proof on the facts about one job here.
-/

@[expose] public section

namespace Lanes.Schedule

variable {K P A : Type} [DecidableEq K] [DecidableEq P] [DecidableEq A]

/-! ### Messages and the job they are about -/

/-- The key a message is about and what it does to it; a scheduling is about no job held. -/
def Msg.target : Schedule.Msg K P A → Option (K × Act A)
  | .schedule .. => none
  | .cancel key => some (key, .cancel)
  | .reply key attempt r => some (key, .reply attempt r)
  | .due key => some (key, .due)
  | .expire key => some (key, .expire)

/-- The message of an act on a key. -/
def Act.msg (key : K) : Act A → Schedule.Msg K P A
  | .cancel => .cancel key
  | .reply attempt r => .reply key attempt r
  | .due => .due key
  | .expire => .expire key

theorem step_target {config : Config K P A} {s : State K P} {msg : Schedule.Msg K P A} {key : K}
    {act : Act A} (h : msg.target = some (key, act)) :
    step config s msg = touch config s key act ∧ msg = act.msg key := by
  cases msg <;> simp only [Msg.target, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
    obtain ⟨rfl, rfl⟩ := h <;> exact ⟨rfl, rfl⟩

omit [DecidableEq K] [DecidableEq P] [DecidableEq A] in
theorem target_timer (j : Job K P) :
    ∃ act, (timer j : Schedule.Msg K P A).target = some (j.key, act) ∧
      (act = .due ∧ j.phase = .waiting ∨ act = .expire ∧ j.phase ≠ .waiting) := by
  unfold timer
  split
  · exact ⟨.due, rfl, .inl ⟨rfl, ‹_›⟩⟩
  · next h => exact ⟨.expire, rfl, .inr ⟨rfl, by simpa using h⟩⟩

omit [DecidableEq K] [DecidableEq P] [DecidableEq A] in
theorem timer_key {j : Job K P} {key : K} :
    (timer j : Schedule.Msg K P A) = .due key ∨ (timer j : Schedule.Msg K P A) = .expire key →
      j.key = key := by
  unfold timer
  split <;> simp_all

theorem touch_none {config : Config K P A} {s : State K P} {key : K} (act : Act A)
    (h : entry s.jobs key = none) : touch config s key act = (s, []) := by
  simp [touch, h]

theorem touch_some {config : Config K P A} {s : State K P} {key : K} (act : Act A)
    {j : Job K P} (h : entry s.jobs key = some j) :
    touch config s key act = (⟨(onJob config s.now_ms j act).now_ms,
      set s.jobs key (onJob config s.now_ms j act).job⟩, (onJob config s.now_ms j act).effs) := by
  simp [touch, h]

/-! ### One job -/

/-- Whether a job comes back for ever. -/
def Work.periodic : Work → Bool
  | .every _ => true
  | _ => false

/-- Whether an output is an attempt of `key`. -/
def isCall (key : K) : Output K P A → Bool
  | .call a => a.key == key
  | _ => false

/-- How far a job is from its end: two for each attempt left, one more while an attempt is
out, and nothing once it is cancelled while one is. -/
def left (config : Config K P A) (j : Job K P) : Nat :=
  match j.phase with
  | .waiting => 2 * (config.cap j.work - j.attempt)
  | .running => 2 * (config.cap j.work - j.attempt) + 1
  | .cancelling => 0

/-- The entry of a key after a step is gone or nearer its end than `j`. -/
def Moved (config : Config K P A) (j : Job K P) (e : Option (Job K P)) : Prop :=
  e = none ∨ ∃ j', e = some j' ∧ left config j' < left config j

/-- Takes an act on one job apart into its cases, in the goal and in `h`. -/
local macro "job_cases " act:ident " at " h:ident : tactic => `(tactic|
  (cases $act:ident <;> simp only [onJob, over, fail, run] at $h:ident ⊢ <;>
    repeat' (first | split | (split at $h:ident) | dsimp only | (dsimp only at $h:ident))))

section Job

variable {config : Config K P A} {now_ms : Nat} {j : Job K P} {act : Act A}

/-- What an act leaves of a job is the same job, with the same key, work and payload. -/
def Same (j j' : Job K P) : Prop := j'.key = j.key ∧ j'.work = j.work ∧ j'.payload = j.payload

theorem fail_same (last : Option A) :
    ∀ j', (fail config now_ms j last).1 = some j' → Same j j' := by
  intro j' h
  unfold fail at h
  split at h
  · dsimp only at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      simp_all [Same]
    · simp at h
  · simp at h

theorem over_same (result : Option A) :
    ∀ j', (over config now_ms j result).1 = some j' → Same j j' := by
  unfold over
  split
  · simp
  · split
    · simp
    · exact fail_same _
  · exact fail_same _

theorem run_same : ∀ j', (run config now_ms j).1 = some j' → Same j j' := by
  unfold run
  split <;> simp_all [Same]

theorem onJob_same : ∀ j', (onJob config now_ms j act).job = some j' → Same j j' := by
  cases act <;> simp only [onJob]
  · split <;> simp_all [Same]
  · split
    · exact over_same _
    · simp [Same]
  · split
    · exact run_same
    · simp [Same]
  · split
    · exact over_same _
    · simp [Same]

theorem onJob_key : ∀ j', (onJob config now_ms j act).job = some j' → j'.key = j.key :=
  fun j' h => (onJob_same j' h).1

theorem onJob_now : now_ms ≤ (onJob config now_ms j act).now_ms := by
  cases act <;> simp only [onJob] <;> (try split) <;> (try split) <;> simp <;> omega

theorem fail_runs (last : Option A) : (fail config now_ms j last).2.any Effect.isStop = false := by
  unfold fail
  split
  · dsimp only
    split <;> simp [Effect.isStop]
  · simp [Effect.isStop]

theorem over_runs (result : Option A) :
    (over config now_ms j result).2.any Effect.isStop = false := by
  unfold over
  split
  · simp [Effect.isStop]
  · split
    · simp [Effect.isStop]
    · exact fail_runs _
  · exact fail_runs _

theorem onJob_runs : (onJob config now_ms j act).effs.any Effect.isStop = false := by
  cases act <;> simp only [onJob]
  · split <;> simp [Effect.isStop]
  · split
    · simpa [Effect.isStop] using over_runs (config := config) (now_ms := now_ms) (j := j) _
    · simp
  · split
    · unfold run
      split <;> simp [Effect.isStop]
    · simp
  · split
    · simpa [Effect.isStop] using over_runs (config := config) (j := j) _
    · simp

/-- The timers an act's effects arm or cancel are its job's. -/
def OwnTimers (key : K) (effs : List (Eff K P A)) : Prop :=
  ∀ m, ((.cancel m : Eff K P A) ∈ effs ∨ ∃ d, (.after d m : Eff K P A) ∈ effs) →
    m = .due key ∨ m = .expire key

theorem ownTimers_nil (key : K) : OwnTimers (A := A) (P := P) key [] := by
  simp [OwnTimers]

theorem ownTimers_cons_emit {key : K} {out : Output K P A} {effs : List (Eff K P A)}
    (h : OwnTimers key effs) : OwnTimers key (.emit out :: effs) := by
  intro m hm
  simp only [List.mem_cons, reduceCtorEq, false_or] at hm
  exact h m hm

theorem ownTimers_cons_cancel {key : K} {m₀ : Schedule.Msg K P A} {effs : List (Eff K P A)}
    (hm₀ : m₀ = .due key ∨ m₀ = .expire key) (h : OwnTimers key effs) :
    OwnTimers key (.cancel m₀ :: effs) := by
  intro m hm
  simp only [List.mem_cons, Effect.cancel.injEq, reduceCtorEq, false_or] at hm
  rcases hm with (rfl | hm) | hm
  · exact hm₀
  · exact h m (.inl hm)
  · exact h m (.inr hm)

theorem fail_ownTimers (last : Option A) : OwnTimers j.key (fail config now_ms j last).2 := by
  intro m hm
  unfold fail at hm
  split at hm
  · dsimp only at hm
    split at hm <;> simp_all
  · simp_all

theorem over_ownTimers (result : Option A) : OwnTimers j.key (over config now_ms j result).2 := by
  unfold over
  split
  · exact ownTimers_cons_emit (ownTimers_nil _)
  · split
    · exact ownTimers_cons_emit (ownTimers_nil _)
    · exact fail_ownTimers _
  · exact fail_ownTimers _

theorem onJob_ownTimers : OwnTimers j.key (onJob config now_ms j act).effs := by
  cases act <;> simp only [onJob]
  · split
    · exact ownTimers_cons_cancel (.inl rfl) (ownTimers_cons_emit (ownTimers_nil _))
    · exact ownTimers_nil _
    · exact ownTimers_nil _
  · split
    · exact ownTimers_cons_cancel (.inr rfl) (over_ownTimers _)
    · exact ownTimers_nil _
  · split
    · unfold run
      split <;> intro m hm <;> simp_all
    · exact ownTimers_nil _
  · split
    · exact ownTimers_cons_emit (over_ownTimers _)
    · exact ownTimers_nil _

/-- A job is within its attempts: no more started than its work allows, another left while it
waits, and one at least while one is out. -/
def Job.Within (config : Config K P A) (j : Job K P) : Prop :=
  j.attempt ≤ config.cap j.work ∧ (j.phase = .waiting → j.attempt < config.cap j.work) ∧
    (j.phase ≠ .waiting → 1 ≤ j.attempt)

theorem onJob_within (h : Job.Within config j) :
    ∀ j', (onJob config now_ms j act).job = some j' → Job.Within config j' := by
  intro j' hj'
  obtain ⟨h1, h2, h3⟩ := h
  cases act <;> simp only [onJob, over, fail, run] at hj' <;>
    repeat' (first | (split at hj') | (dsimp only at hj'))
  all_goals (try simp only [Option.some.injEq, reduceCtorEq] at hj')
  all_goals (try subst hj')
  all_goals (simp_all [Job.Within] <;> omega)

/-- What an act leaves of a job waits on a timer the act arms and does not cancel, or on the
job's timer as it was, which the act did not fire. -/
theorem onJob_timer :
    ∀ j', (onJob config now_ms j act).job = some j' →
      ((∃ d, (.after d (timer j') : Eff K P A) ∈ (onJob config now_ms j act).effs) ∧
        (.cancel (timer j') : Eff K P A) ∉ (onJob config now_ms j act).effs) ∨
      ((onJob config now_ms j act).effs = [] ∧ timer j' = (timer j : Schedule.Msg K P A) ∧
        (timer j : Schedule.Msg K P A) ≠ act.msg j.key) := by
  intro j' hj'
  cases act <;> simp only [onJob, over, fail, run] at hj' ⊢ <;>
    repeat' (first | split | (split at hj') | dsimp only | (dsimp only at hj'))
  all_goals (try simp only [Option.some.injEq, reduceCtorEq] at hj')
  all_goals (try subst hj')
  all_goals (simp_all [timer, Act.msg])
  all_goals (split <;> simp)

/-- No act arms again the timer a job that does not come back for ever waits on: its `due` is
armed only by a failure, which ends an attempt out, its `expire` only when it is due. -/
theorem onJob_not_arms (hp : j.work.periodic = false) (d : Nat) :
    (.after d (timer j) : Eff K P A) ∉ (onJob config now_ms j act).effs := by
  intro hd
  job_cases act at hd
  all_goals (simp_all [timer, Work.periodic])

/-- A job is over only by an act that tells its requester. -/
theorem onJob_ends (hgone : (onJob config now_ms j act).job = none) :
    (∃ o, (.emit (.answer j.key o) : Eff K P A) ∈ (onJob config now_ms j act).effs) ∨
      (.emit (.notice j.key j.payload) : Eff K P A) ∈ (onJob config now_ms j act).effs := by
  job_cases act at hgone
  all_goals (simp_all)

/-- An act dispatches an attempt only when its job waits and is due, as the next attempt, with
the job's key and payload, stamped with the time then known, which is the job's run time or
later; the job then has that attempt out. -/
theorem onJob_dispatch {a : Attempt K P}
    (h : (.emit (.call a) : Eff K P A) ∈ (onJob config now_ms j act).effs) :
    act = .due ∧ j.phase = .waiting ∧ (onJob config now_ms j act).now_ms = max now_ms j.at_ms ∧
      ∃ retry, j.work = .call retry ∧
        a = ⟨j.key, j.attempt + 1, max now_ms j.at_ms, retry.deadline_ms, j.payload⟩ ∧
        (onJob config now_ms j act).job =
          some { j with attempt := j.attempt + 1, phase := .running,
                        at_ms := max now_ms j.at_ms + config.wait retry } := by
  job_cases act at h
  all_goals (simp_all)

/-- An attempt that failed leaves its job due the backoff after the time the failure was known. -/
theorem onJob_retry (hout : j.phase ≠ .waiting) {j' : Job K P}
    (hj' : (onJob config now_ms j act).job = some j') (hwait : j'.phase = .waiting) :
    ∃ retry, j.work = .call retry ∧ j'.attempt = j.attempt ∧
      j'.at_ms = (onJob config now_ms j act).now_ms + config.backoff retry j.key j.attempt := by
  job_cases act at hj'
  all_goals (try simp only [Option.some.injEq, reduceCtorEq] at hj')
  all_goals (try subst hj')
  all_goals (simp_all)

/-- An attempt out ends only with its answer, or with the end of its wait, abandoned. -/
theorem onJob_attempt_ends (hout : j.phase ≠ .waiting)
    (hend : ∀ j', (onJob config now_ms j act).job = some j' → j'.phase = .waiting) :
    (∃ r, act = .reply j.attempt r) ∨
      (act = .expire ∧ (.emit (.abandon j.key j.attempt) : Eff K P A) ∈ (onJob config now_ms j act).effs) := by
  cases act with
  | cancel =>
    simp only [onJob] at hend
    split at hend <;> simp_all
  | reply attempt r =>
    by_cases hm : j.attempt = attempt
    · exact .inl ⟨r, by rw [hm]⟩
    · simp only [onJob, hm, and_false, ↓reduceIte] at hend
      simp_all
  | due =>
    simp only [onJob, hout, ↓reduceIte] at hend
    simp_all
  | expire => exact .inr ⟨rfl, by simp [onJob, hout]⟩

/-- An act calls its job's key no more often than the attempts it takes from the job. -/
theorem onJob_calls (h : Job.Within config j) :
    (Effect.emits (onJob config now_ms j act).effs).countP (isCall j.key)
        + (onJob config now_ms j act).job.elim 0 (fun j' => config.cap j'.work - j'.attempt)
      ≤ config.cap j.work - j.attempt := by
  obtain ⟨h1, h2, h3⟩ := h
  have hj : (onJob config now_ms j act).job = (onJob config now_ms j act).job := rfl
  job_cases act at hj
  all_goals (simp_all [Effect.emits, isCall] <;> omega)

/-- An act leaves a job that does not come back for ever as it was, or nearer its end. -/
theorem onJob_moved (h : Job.Within config j) (hp : j.work.periodic = false) :
    (onJob config now_ms j act).job = some j ∨ Moved config j (onJob config now_ms j act).job := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨key, payload, work, at_ms, attempt, phase⟩ := j
  have hj : (onJob config now_ms ⟨key, payload, work, at_ms, attempt, phase⟩ act).job =
    (onJob config now_ms ⟨key, payload, work, at_ms, attempt, phase⟩ act).job := rfl
  cases phase <;> job_cases act at hj
  all_goals (simp_all [Moved, left, Work.periodic] <;> omega)

/-- The act of the timer a job waits on moves it nearer its end. -/
theorem onJob_moved_timer (h : Job.Within config j) (hp : j.work.periodic = false)
    (hact : act = .due ∧ j.phase = .waiting ∨ act = .expire ∧ j.phase ≠ .waiting) :
    Moved config j (onJob config now_ms j act).job := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨key, payload, work, at_ms, attempt, phase⟩ := j
  rcases hact with ⟨rfl, hw⟩ | ⟨rfl, hw⟩
  · simp only at hw
    subst hw
    simp only [onJob, ↓reduceIte, run]
    split <;> simp_all [Moved, left, Work.periodic] <;> omega
  · cases phase
    · simp at hw
    all_goals (simp only [onJob, over, fail]; repeat' (first | split | dsimp only))
    all_goals (simp_all [Moved, left, Work.periodic] <;> omega)

end Job

/-! ### A step -/

section Step

variable {config : Config K P A} {s : State K P}

/-- The job a scheduling makes, if it admits one. -/
def Spec.job (spec : Spec K P) : Job K P := ⟨spec.key, spec.payload, spec.work, spec.at_ms, 0, .waiting⟩

/-- A scheduling leaves the jobs held as they are, and adds a job under an id not held, with an
answer and its timer. -/
theorem admit_cases (now_ms : Nat) (spec : Spec K P) :
    (admit config s now_ms spec).1.now_ms = max s.now_ms now_ms ∧
    (((admit config s now_ms spec).1.jobs = s.jobs ∧
        ∃ o, (admit config s now_ms spec).2 = [.emit (.answer spec.key o)]) ∨
      (spec.key ∉ keys s.jobs ∧ s.jobs.length < config.maxJobs ∧
        (admit config s now_ms spec).1.jobs = spec.job :: s.jobs ∧
        (admit config s now_ms spec).2 = [.emit (.answer spec.key .scheduled),
          .after (spec.at_ms - max s.now_ms now_ms) (.due spec.key)])) := by
  simp only [admit]
  split
  · exact ⟨rfl, .inl ⟨rfl, _, rfl⟩⟩
  · split
    · exact ⟨rfl, .inl ⟨rfl, _, rfl⟩⟩
    · split
      · exact ⟨rfl, .inl ⟨rfl, _, rfl⟩⟩
      · exact ⟨rfl, .inr ⟨‹_›, by omega, rfl, rfl⟩⟩

theorem step_schedule (now_ms : Nat) (spec : Spec K P) :
    step config s (.schedule now_ms spec) = admit config s now_ms spec := rfl

/-- A step about the job held under `key` is its act on that job; any other leaves the job as it
is. -/
theorem step_key {key : K} {j : Job K P} (hj : entry s.jobs key = some j)
    (msg : Schedule.Msg K P A) :
    (entry (step config s msg).1.jobs key = some j ∧ ∀ act : Act A, msg ≠ act.msg key) ∨
      ∃ act, msg = act.msg key ∧ step config s msg =
        (⟨(onJob config s.now_ms j act).now_ms, set s.jobs key (onJob config s.now_ms j act).job⟩,
          (onJob config s.now_ms j act).effs) := by
  have hheld : key ∈ keys s.jobs := mem_keys.mpr ⟨j, (entry_some hj).1, (entry_some hj).2⟩
  cases htarget : msg.target with
  | none =>
    cases msg <;> simp only [Msg.target, reduceCtorEq] at htarget
    rename_i now_ms spec
    refine .inl ⟨?_, fun act => by cases act <;> simp [Act.msg]⟩
    rw [step_schedule]
    obtain ⟨-, h | h⟩ := admit_cases (config := config) (s := s) now_ms spec
    · rw [h.1]
      exact hj
    · rw [h.2.2.1, entry_cons_of_ne _ _ (fun he => h.1 (by rw [show spec.key = key from he]; exact hheld))]
      exact hj
  | some target =>
    obtain ⟨k, act⟩ := target
    obtain ⟨hstep, rfl⟩ := step_target (config := config) (s := s) htarget
    by_cases hk : k = key
    · subst hk
      exact .inr ⟨act, rfl, by rw [hstep, touch_some act hj]⟩
    · refine .inl ⟨?_, fun act' h => by cases act <;> cases act' <;> simp_all [Act.msg]⟩
      rw [hstep]
      cases hk' : entry s.jobs k with
      | none => simpa [touch_none act hk'] using hj
      | some j' =>
        rw [touch_some act hk']
        refine (entry_set_of_ne (Ne.symm hk) ?_).trans hj
        intro b hb
        exact (onJob_key b hb).trans (entry_some hk').2

/-- A step is a scheduling, or an act on the job held under its key, or nothing. -/
theorem step_cases (msg : Schedule.Msg K P A) :
    (∃ now_ms spec, msg = .schedule now_ms spec) ∨
      (∃ key, ∃ act : Act A, msg = act.msg key ∧ entry s.jobs key = none ∧ step config s msg = (s, [])) ∨
      ∃ key, ∃ act : Act A, ∃ j, msg = act.msg key ∧ entry s.jobs key = some j ∧ step config s msg =
        (⟨(onJob config s.now_ms j act).now_ms, set s.jobs key (onJob config s.now_ms j act).job⟩,
          (onJob config s.now_ms j act).effs) := by
  cases htarget : msg.target with
  | none =>
    cases msg <;> simp only [Msg.target, reduceCtorEq] at htarget
    exact .inl ⟨_, _, rfl⟩
  | some target =>
    obtain ⟨k, act⟩ := target
    obtain ⟨hstep, rfl⟩ := step_target (config := config) (s := s) htarget
    cases hk : entry s.jobs k with
    | none => exact .inr (.inl ⟨k, act, rfl, hk, by rw [hstep, touch_none act hk]⟩)
    | some j => exact .inr (.inr ⟨k, act, j, rfl, hk, by rw [hstep, touch_some act hk]⟩)

theorem step_runs (config : Config K P A) (s : State K P) (msg : Schedule.Msg K P A) :
    (step config s msg).2.any Effect.isStop = false := by
  rcases step_cases (config := config) (s := s) msg with
    ⟨now_ms, spec, rfl⟩ | ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩
  · rw [step_schedule]
    obtain ⟨-, ⟨-, o, h⟩ | ⟨-, -, -, h⟩⟩ := admit_cases (config := config) (s := s) now_ms spec <;>
      simp [h, Effect.isStop]
  · simp [h]
  · simpa [h] using onJob_runs

theorem recover_runs (config : Config K P A) (s : State K P) :
    ((actor config).recover s).2.any Effect.isStop = false := by
  simp [actor, rearm, Effect.isStop]

/-- The scheduler's time never goes back. -/
theorem now_le_step (config : Config K P A) (s : State K P) (msg : Schedule.Msg K P A) :
    s.now_ms ≤ (step config s msg).1.now_ms := by
  rcases step_cases (config := config) (s := s) msg with
    ⟨now_ms, spec, rfl⟩ | ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩
  · rw [step_schedule, (admit_cases (config := config) (s := s) now_ms spec).1]
    omega
  · simp [h]
  · simpa [h] using onJob_now

/-- No more jobs are held than `maxJobs`, and no id twice. -/
def State.Within (config : Config K P A) (s : State K P) : Prop :=
  s.jobs.length ≤ config.maxJobs ∧ (keys s.jobs).Nodup

/-- Every job held is within its attempts. -/
def State.Attempts (config : Config K P A) (s : State K P) : Prop :=
  ∀ j ∈ s.jobs, Job.Within config j

theorem onJob_key_of {key : K} {j : Job K P} (hj : entry s.jobs key = some j) (act : Act A) :
    ∀ b, (onJob config s.now_ms j act).job = some b → b.key = key :=
  fun b hb => (onJob_key b hb).trans (entry_some hj).2

theorem within_step (config : Config K P A) {s : State K P} (msg : Schedule.Msg K P A)
    (h : s.Within config) : (step config s msg).1.Within config := by
  rcases step_cases (config := config) (s := s) msg with
    ⟨now_ms, spec, rfl⟩ | ⟨_, _, _, _, hs⟩ | ⟨key, act, j, _, hj, hs⟩
  · rw [step_schedule]
    obtain ⟨-, ⟨hjobs, -⟩ | ⟨hnew, hroom, hjobs, -⟩⟩ :=
      admit_cases (config := config) (s := s) now_ms spec
    · unfold State.Within
      rw [hjobs]
      exact h
    · rw [State.Within, hjobs]
      exact ⟨by simp only [List.length_cons]; omega, List.nodup_cons.mpr ⟨hnew, h.2⟩⟩
  · rw [hs]
    exact h
  · rw [hs]
    exact ⟨Nat.le_trans (length_set_le ..) h.1, nodup_set key (onJob_key_of hj act) h.2⟩

theorem attempts_step (config : Config K P A) {s : State K P} (msg : Schedule.Msg K P A)
    (h : s.Attempts config) : (step config s msg).1.Attempts config := by
  rcases step_cases (config := config) (s := s) msg with
    ⟨now_ms, spec, rfl⟩ | ⟨_, _, _, _, hs⟩ | ⟨key, act, j, _, hj, hs⟩
  · rw [step_schedule]
    obtain ⟨-, ⟨hjobs, -⟩ | ⟨-, -, hjobs, -⟩⟩ := admit_cases (config := config) (s := s) now_ms spec
    · unfold State.Attempts
      rw [hjobs]
      exact h
    · intro b hb
      rw [hjobs] at hb
      rcases List.mem_cons.mp hb with rfl | hb
      · have := config.one_le_cap spec.work
        exact ⟨by simp [Spec.job], fun _ => by simp [Spec.job]; omega,
          fun h => by simp [Spec.job] at h⟩
      · exact h b hb
  · rw [hs]
    exact h
  · rw [hs]
    intro b hb
    rcases mem_set (onJob_key_of hj act) hb with hb | ⟨hb, -⟩
    · exact onJob_within (h j (entry_some hj).1) b hb
    · exact h b hb

theorem actor_within (config : Config K P A) :
    (actor (K := K) (P := P) config).Invariant (State.Within config) :=
  Actor.Inductive.invariant
    ⟨⟨by simp [actor], by simp [actor, keys]⟩, fun _ msg h => within_step config msg h,
      fun _ h => h⟩

theorem actor_attempts (config : Config K P A) :
    (actor (K := K) (P := P) config).Invariant (State.Attempts config) :=
  Actor.Inductive.invariant
    ⟨by simp [actor, State.Attempts], fun _ msg h => attempts_step config msg h, fun _ h => h⟩

/-! What an attempt is: never before its time, one at a time, and the next only after a wait. -/

/-- An attempt is dispatched only when its job's `due` timer fires, for a job held that waits,
with no attempt out: it is the job's next attempt, with its payload, stamped with the
scheduler's time after the step, which is no earlier than the time the job was due. The job
then has that attempt out. -/
theorem dispatch_due {msg : Schedule.Msg K P A} {a : Attempt K P}
    (h : (.emit (.call a) : Eff K P A) ∈ (step config s msg).2) :
    msg = .due a.key ∧ ∃ j, entry s.jobs a.key = some j ∧ j.phase = .waiting ∧
      j.at_ms ≤ a.start_ms ∧ a.start_ms = (step config s msg).1.now_ms ∧
      a.attempt = j.attempt + 1 ∧ a.payload = j.payload ∧
      ∃ j', entry (step config s msg).1.jobs a.key = some j' ∧ j'.phase = .running ∧
        j'.attempt = a.attempt := by
  rcases step_cases (config := config) (s := s) msg with
    ⟨now_ms, spec, rfl⟩ | ⟨_, _, _, _, hs⟩ | ⟨key, act, j, rfl, hj, hs⟩
  · rw [step_schedule] at h
    obtain ⟨-, ⟨-, o, he⟩ | ⟨-, -, -, he⟩⟩ := admit_cases (config := config) (s := s) now_ms spec <;>
      simp [he] at h
  · simp [hs] at h
  · rw [hs] at h ⊢
    obtain ⟨rfl, hwait, hnow, retry, hwork, rfl, hjob⟩ := onJob_dispatch h
    obtain ⟨hmem, rfl⟩ := entry_some hj
    refine ⟨rfl, j, hj, hwait, Nat.le_max_right .., hnow.symm, rfl, rfl, ?_⟩
    rw [hjob]
    exact ⟨_, entry_put_self (mem_keys.mpr ⟨j, hmem, rfl⟩), rfl, rfl⟩

/-- After an attempt failed, its job is due again the backoff after the time the failure was
known: a step that takes the job under `key` from an attempt out to waiting sets its run time
there. -/
theorem retry_waits {msg : Schedule.Msg K P A} {key : K} {j j' : Job K P}
    (hj : entry s.jobs key = some j) (hout : j.phase ≠ .waiting)
    (hj' : entry (step config s msg).1.jobs key = some j') (hwait : j'.phase = .waiting) :
    ∃ retry, j.work = .call retry ∧ j'.attempt = j.attempt ∧
      j'.at_ms = (step config s msg).1.now_ms + config.backoff retry key j.attempt := by
  have hheld : key ∈ keys s.jobs := mem_keys.mpr ⟨j, (entry_some hj).1, (entry_some hj).2⟩
  rcases step_key (config := config) hj msg with ⟨hsame, -⟩ | ⟨act, rfl, hstep⟩
  · rw [hsame] at hj'
    obtain rfl := Option.some.inj hj'
    exact absurd hwait hout
  · rw [hstep] at hj' ⊢
    rw [entry_set_self hheld (onJob_key_of hj act)] at hj'
    obtain ⟨retry, hw, ha, hat⟩ := onJob_retry hout hj' hwait
    exact ⟨retry, hw, ha, (entry_some hj).2 ▸ hat⟩

/-- An attempt out ends only with its answer, or abandoned at the end of its wait: a step that
takes the job under `key` from an attempt out to waiting, or ends it, handles the reply to that
attempt, or the job's `expire` and emits `abandon`. -/
theorem attempt_ends {msg : Schedule.Msg K P A} {key : K} {j : Job K P}
    (hj : entry s.jobs key = some j) (hout : j.phase ≠ .waiting)
    (hend : ∀ j', entry (step config s msg).1.jobs key = some j' → j'.phase = .waiting) :
    (∃ r, msg = .reply key j.attempt r) ∨
      (msg = .expire key ∧ (.emit (.abandon key j.attempt) : Eff K P A) ∈ (step config s msg).2) := by
  have hheld : key ∈ keys s.jobs := mem_keys.mpr ⟨j, (entry_some hj).1, (entry_some hj).2⟩
  rcases step_key (config := config) hj msg with ⟨hsame, -⟩ | ⟨act, rfl, hstep⟩
  · exact absurd (hend j hsame) hout
  · rw [hstep] at hend ⊢
    rw [entry_set_self hheld (onJob_key_of hj act)] at hend
    obtain ⟨-, rfl⟩ := entry_some hj
    rcases onJob_attempt_ends hout hend with ⟨r, rfl⟩ | ⟨rfl, habandon⟩
    · exact .inl ⟨r, rfl⟩
    · exact .inr ⟨rfl, habandon⟩

omit [DecidableEq K] [DecidableEq P] [DecidableEq A] in
theorem timer_act_key {b : Job K P} {key : K} {act : Act A}
    (h : (timer b : Schedule.Msg K P A) = act.msg key) : b.key = key := by
  cases act <;> unfold timer at h <;> split at h <;> simp_all [Act.msg]

/-- After a step, the timer of every job held is armed, if before it the timer of every job held
was, but perhaps the one the step handles. -/
theorem armed_step (config : Config K P A) {s : State K P} {timers : List (Schedule.Msg K P A)}
    (msg : Schedule.Msg K P A)
    (h : ∀ j ∈ s.jobs, timer j ≠ msg → timer j ∈ timers) :
    ∀ j ∈ (step config s msg).1.jobs, timer j ∈ Effect.retime (step config s msg).2 timers := by
  rcases step_cases (config := config) (s := s) msg with
    ⟨now_ms, spec, rfl⟩ | ⟨key, act, rfl, hnone, hs⟩ | ⟨key, act, j, rfl, hj, hs⟩
  · have hne (b : Job K P) : timer b ≠ (.schedule now_ms spec : Schedule.Msg K P A) := by
      unfold timer
      split <;> simp
    rw [step_schedule]
    obtain ⟨-, ⟨hjobs, o, he⟩ | ⟨-, -, hjobs, he⟩⟩ := admit_cases (config := config) (s := s) now_ms spec
    · intro b hb
      rw [hjobs] at hb
      rw [he]
      exact h b hb (hne b)
    · intro b hb
      rw [hjobs] at hb
      rw [he]
      rcases List.mem_cons.mp hb with rfl | hb
      · exact Effect.mem_retime_of_after (delay_ms := spec.at_ms - max s.now_ms now_ms)
          (by simp [timer, Spec.job]) (by simp)
      · exact Effect.mem_retime_of_mem (h b hb (hne b)) (by simp)
  · rw [hs]
    intro b hb
    refine h b hb fun he => ?_
    have hkey : b.key = key := timer_act_key he
    exact entry_eq_none.mp hnone (mem_keys.mpr ⟨b, hb, hkey⟩)
  · rw [hs]
    obtain ⟨hmem, rfl⟩ := entry_some hj
    intro b hb
    rcases mem_set (onJob_key_of hj act) hb with hb' | ⟨hb', hne⟩
    · rcases onJob_timer b hb' with ⟨⟨d, hd⟩, hc⟩ | ⟨heffs, htimer, hfired⟩
      · exact Effect.mem_retime_of_after hd hc
      · rw [heffs, htimer]
        exact h j hmem hfired
    · have hnot : timer b ≠ (act.msg j.key : Schedule.Msg K P A) := fun he =>
        hne (timer_act_key he)
      refine Effect.mem_retime_of_mem (h b hb' hnot) fun hc => hne ?_
      exact timer_key (onJob_ownTimers _ (.inl hc))

end Step

/-! ### The scheduler as a system -/

variable {config : Config K P A} {env : EnvModel (sig K P A)}

/-- While the scheduler is up, the timer each job held waits on is armed. -/
def Armed (c : SysState (system (K := K) (P := P) config)) : Prop :=
  c.up () = true → ∀ j ∈ (c.state () : State K P).jobs, timer j ∈ c.timers ()

/-- No more jobs are held than `maxJobs`, and no id twice, in every environment. -/
theorem within (config : Config K P A) (env : EnvModel (sig K P A)) :
    (system (K := K) (P := P) config).Invariant env fun c => (c.state ()).Within config :=
  System.invariant_of_actor _ () (actor_within config) env

/-- Every job held is within its attempts, in every environment. -/
theorem attempts (config : Config K P A) (env : EnvModel (sig K P A)) :
    (system (K := K) (P := P) config).Invariant env fun c => (c.state ()).Attempts config :=
  System.invariant_of_actor _ () (actor_attempts config) env

theorem handle_eq (c : SysState (system (K := K) (P := P) config)) (msg : Schedule.Msg K P A) :
    c.handle env () msg = { c with
      state := update c.state () (step config (c.state ()) msg).1
      net := c.net ++ Effect.sends () (step config (c.state ()) msg).2
      timers := update c.timers () (Effect.retime (step config (c.state ()) msg).2 (c.timers ()))
      outbox := c.outbox ++ Effect.emits (step config (c.state ()) msg).2 } := by
  have hr : ((actor config).step (c.state ()) msg).2.any Effect.isStop = false :=
    step_runs config (c.state ()) msg
  simp only [SysState.handle, SysState.settle_eq, hr, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem startActor_eq (c : SysState (system (K := K) (P := P) config)) :
    c.startActor env () = { c with
      up := update c.up () true
      net := c.net ++ Effect.sends () ((c.state ()).jobs.map (rearm (c.state ())))
      timers := update c.timers ()
        (Effect.retime ((c.state ()).jobs.map (rearm (c.state ()))) (c.timers ()))
      outbox := c.outbox ++ Effect.emits ((c.state ()).jobs.map (rearm (c.state ()))) } := by
  have hr := recover_runs (K := K) (P := P) config (c.state ())
  simp only [SysState.startActor, SysState.settle_eq, hr, Bool.false_eq_true, ↓reduceIte]
  simp only [actor, SysState.mk.injEq, and_true]
  funext i
  simp

private theorem armed_handle {c : SysState (system (K := K) (P := P) config)}
    (msg : Schedule.Msg K P A)
    (h : ∀ j ∈ (c.state () : State K P).jobs, timer j ≠ msg → timer j ∈ c.timers ()) :
    Armed (c.handle env () msg) := by
  intro _ j hj
  rw [handle_eq] at hj ⊢
  simp only [update_self] at hj ⊢
  exact armed_step config msg h j hj

private theorem armed_start (c : SysState (system (K := K) (P := P) config)) :
    Armed (c.startActor env ()) := by
  intro _ j hj
  rw [startActor_eq] at hj ⊢
  simp only [update_self] at hj ⊢
  refine Effect.mem_retime_of_after (List.mem_map.mpr ⟨j, hj, rfl⟩) ?_
  intro hc
  obtain ⟨b, -, hb⟩ := List.mem_map.mp hc
  simp [rearm] at hb

/-- The scheduler cannot forget a job, in any environment: while it is up, the timer the job
waits on is armed. -/
theorem armed (config : Config K P A) (env : EnvModel (sig K P A)) :
    (system (K := K) (P := P) config).Invariant env Armed := by
  intro c hc
  induction hc with
  | init => exact armed_start (env := env) (SysState.blank _)
  | @step c c' ev hc hstep ih =>
    cases ev with
    | input x =>
      obtain rfl := SysState.step_input.mp hstep
      exact ih
    | deliver e =>
      obtain ⟨hup, _, rfl⟩ := SysState.step_deliver.mp hstep
      exact armed_handle (c := { c with net := c.net.erase e }) e.msg
        fun j hj _ => ih hup j hj
    | duplicate e =>
      obtain ⟨hup, _, _, rfl⟩ := SysState.step_duplicate.mp hstep
      exact armed_handle e.msg fun j hj _ => ih hup j hj
    | drop e =>
      obtain ⟨_, _, rfl⟩ := SysState.step_drop.mp hstep
      exact ih
    | timeout i msg =>
      obtain ⟨hup, _, rfl⟩ := SysState.step_timeout.mp hstep
      refine armed_handle msg fun j hj hne => ?_
      simpa using (List.mem_erase_of_ne hne).mpr (ih hup j hj)
    | output out =>
      obtain ⟨_, rfl⟩ := SysState.step_output.mp hstep
      exact ih
    | crash i =>
      obtain ⟨_, _, rfl⟩ := SysState.step_crash.mp hstep
      simp [Armed, SysState.down]
    | start i =>
      obtain ⟨_, _, rfl⟩ := SysState.step_start.mp hstep
      exact armed_start c

/-! ### No more calls than attempts allowed -/

/-- The attempts of `key` handed over, as often as they were. -/
def calls (key : K) (shown : List (Deed (sig K P A))) : Nat :=
  shown.countP fun
    | .output (.call a) => a.key == key
    | _ => false

/-- The schedulings of `key` the scheduler handled, as often as it handled them. -/
def schedulings (key : K) (shown : List (Deed (sig K P A))) : Nat :=
  shown.countP fun
    | .handle _ (.schedule _ spec) => spec.key == key
    | _ => false

private def schedules (key : K) : Schedule.Msg K P A → Bool
  | .schedule _ spec => spec.key == key
  | _ => false

/-- The attempts the job under `key` may still start. -/
private def rest (config : Config K P A) (s : State K P) (key : K) : Nat :=
  (entry s.jobs key).elim 0 fun j => config.cap j.work - j.attempt

/-- What the scheduler may still call `key`: the attempts waiting to leave and those its job
may start. -/
private def owed (key : K) (c : SysState (system (K := K) (P := P) config)) : Nat :=
  c.outbox.countP (isCall key) + rest config (c.state ()) key

/-- One step calls `key` no more than its job had left, and adds to what is left only by a
scheduling of it, by at most `max 1 maxAttempts`. -/
private theorem owed_step (key : K) {s : State K P} (h : s.Attempts config)
    (msg : Schedule.Msg K P A) :
    (Effect.emits (step config s msg).2).countP (isCall key) + rest config (step config s msg).1 key
      ≤ rest config s key + max 1 config.maxAttempts * (schedules key msg).toNat := by
  rcases step_cases (config := config) (s := s) msg with
    ⟨now_ms, spec, rfl⟩ | ⟨_, _, rfl, _, hs⟩ | ⟨key', act, j, rfl, hj, hs⟩
  · rw [step_schedule]
    obtain ⟨-, ⟨hjobs, o, he⟩ | ⟨hnew, -, hjobs, he⟩⟩ :=
      admit_cases (config := config) (s := s) now_ms spec
    · simp [he, rest, hjobs, Effect.emits, isCall]
    · simp only [he, rest, hjobs, Effect.emits, List.filterMap_cons, List.filterMap_nil,
        List.countP_cons, List.countP_nil, isCall, Bool.false_eq_true, ↓reduceIte]
      by_cases hk : spec.key = key
      · subst hk
        have hnone : entry s.jobs spec.key = none := entry_eq_none.mpr hnew
        have := config.cap_le spec.work
        rw [show entry (spec.job :: s.jobs) spec.key = some spec.job from entry_cons_self _ _]
        simp [hnone, Spec.job, schedules]
        omega
      · rw [entry_cons_of_ne _ _ (by simpa [Spec.job] using hk)]
        omega
  · simp [hs, Effect.emits]
  · rw [hs]
    have hheld : key' ∈ keys s.jobs := mem_keys.mpr ⟨j, (entry_some hj).1, (entry_some hj).2⟩
    have hsched : schedules key (act.msg key' : Schedule.Msg K P A) = false := by
      cases act <;> rfl
    rw [hsched, Bool.toNat_false, Nat.mul_zero, Nat.add_zero]
    by_cases hk : key' = key
    · subst hk
      obtain ⟨hmem, hkey⟩ := entry_some hj
      have := onJob_calls (now_ms := s.now_ms) (act := act) (h j hmem)
      simp only [rest, entry_set_self hheld (onJob_key_of hj act), hj, Option.elim]
      rw [hkey] at this
      cases hjob : (onJob config s.now_ms j act).job <;> simp_all
    · have hnone : (Effect.emits (onJob config s.now_ms j act).effs).countP (isCall key) = 0 := by
        refine List.countP_eq_zero.mpr fun out hout => ?_
        cases out with
        | call a =>
          obtain ⟨-, -, -, _, -, rfl, -⟩ := onJob_dispatch (Effect.mem_emits.mp hout)
          simpa [isCall, (entry_some hj).2] using hk
        | _ => simp [isCall]
      simp only [rest, hnone, Nat.zero_add]
      rw [entry_set_of_ne (Ne.symm hk) (onJob_key_of hj act)]
      exact Nat.le_refl _

private theorem owed_handle (key : K) (c : SysState (system (K := K) (P := P) config))
    (h : (c.state ()).Attempts config) (i : Unit) (msg : Schedule.Msg K P A) :
    owed key (c.handle env i msg)
      ≤ owed key c + max 1 config.maxAttempts * (schedules key msg).toNat := by
  obtain rfl : i = () := rfl
  have hs := owed_step (config := config) key h msg
  rw [handle_eq]
  simp only [owed, update_self, List.countP_append]
  omega

private theorem owed_start (key : K) (c : SysState (system (K := K) (P := P) config)) :
    owed key (c.startActor env ()) = owed key c := by
  have hquiet : Effect.emits ((c.state ()).jobs.map (rearm (A := A) (c.state ()))) = [] := by
    rw [Effect.emits_map]
    exact List.filterMap_eq_nil_iff.mpr fun j _ => rfl
  rw [startActor_eq]
  simp [owed, hquiet, rest]

private theorem calls_snoc (events : List (Event (sig K P A))) (ev : Event (sig K P A)) (key : K) :
    calls key (deeds (events ++ [ev])) = calls key (deeds events) + calls key ev.deed.toList := by
  simp only [calls, deeds, List.filterMap_append, List.countP_append]
  cases h : ev.deed <;> simp [h]

private theorem schedulings_snoc (events : List (Event (sig K P A))) (ev : Event (sig K P A))
    (key : K) :
    schedulings key (deeds (events ++ [ev]))
      = schedulings key (deeds events) + schedulings key ev.deed.toList := by
  simp only [schedulings, deeds, List.filterMap_append, List.countP_append]
  cases h : ev.deed <;> simp [h]

private theorem schedulings_handle (i : Unit) (msg : Schedule.Msg K P A) (key : K) :
    schedulings key [Deed.handle (σ := sig K P A) i msg] = (schedules key msg).toNat := by
  cases msg <;> simp [schedulings, schedules, Bool.toNat]

private theorem calls_output (out : Output K P A) (key : K) :
    calls key [Deed.output (σ := sig K P A) out] = (isCall key out).toNat := by
  cases out <;> simp [calls, isCall, Bool.toNat]

/-- One event: the attempts it hands over and what is owed after it are covered by what was owed
before and the scheduling it handles. -/
private theorem owed_event (key : K) {c c' : SysState (system (K := K) (P := P) config)}
    (hc : (system (K := K) (P := P) config).Reachable env c) {ev : Event (sig K P A)}
    (hstep : c.step env ev = some c') :
    calls key ev.deed.toList + owed key c'
      ≤ owed key c + max 1 config.maxAttempts * schedulings key ev.deed.toList := by
  have hatt := attempts config env c hc
  cases ev with
  | input x =>
    obtain rfl := SysState.step_input.mp hstep
    simp only [Event.deed, Option.toList_none, calls, schedulings, List.countP_nil,
      Nat.zero_add, Nat.mul_zero, Nat.add_zero]
    exact Nat.le_refl _
  | deliver e =>
    obtain ⟨_, _, rfl⟩ := SysState.step_deliver.mp hstep
    have h := owed_handle (env := env) key { c with net := c.net.erase e } hatt e.dst e.msg
    have hsched := schedulings_handle e.dst e.msg key
    have hsame : owed key { c with net := c.net.erase e } = owed key c := rfl
    have hcalls : calls key [Deed.handle (σ := sig K P A) e.dst e.msg] = 0 := rfl
    simp only [Event.deed, Option.toList_some]
    rw [hsched, hcalls]
    omega
  | duplicate e =>
    obtain ⟨_, _, _, rfl⟩ := SysState.step_duplicate.mp hstep
    have h := owed_handle (env := env) key c hatt e.dst e.msg
    have hsched := schedulings_handle e.dst e.msg key
    have hcalls : calls key [Deed.handle (σ := sig K P A) e.dst e.msg] = 0 := rfl
    simp only [Event.deed, Option.toList_some]
    rw [hsched, hcalls]
    omega
  | drop e =>
    obtain ⟨_, _, rfl⟩ := SysState.step_drop.mp hstep
    simp only [Event.deed, Option.toList_none, calls, schedulings, List.countP_nil,
      Nat.zero_add, Nat.mul_zero, Nat.add_zero]
    exact Nat.le_refl _
  | timeout i msg =>
    obtain ⟨_, _, rfl⟩ := SysState.step_timeout.mp hstep
    have h := owed_handle (env := env) key
      { c with timers := update c.timers i ((c.timers i).erase msg) } hatt i msg
    have hsched := schedulings_handle i msg key
    have hsame : owed key { c with timers := update c.timers i ((c.timers i).erase msg) }
        = owed key c := rfl
    have hcalls : calls key [Deed.handle (σ := sig K P A) i msg] = 0 := rfl
    simp only [Event.deed, Option.toList_some]
    rw [hsched, hcalls]
    omega
  | output out =>
    have h := SysState.countP_outbox_of_output (isCall key) hstep
    obtain ⟨-, rfl⟩ := SysState.step_output.mp hstep
    have hcalls := calls_output out key
    have hsched : schedulings key [Deed.output (σ := sig K P A) out] = 0 := rfl
    simp only [Event.deed, Option.toList_some, owed] at h ⊢
    rw [hsched, hcalls]
    omega
  | crash i =>
    obtain ⟨_, _, rfl⟩ := SysState.step_crash.mp hstep
    simp [owed, rest, SysState.down, Event.deed, calls, schedulings]
  | start i =>
    obtain ⟨_, _, rfl⟩ := SysState.step_start.mp hstep
    have h := owed_start (env := env) key c
    simp [h, Event.deed, calls, schedulings]

/-- The scheduler calls no key more often than `max 1 maxAttempts` times for each scheduling of
it that it handled, in every environment: whatever arrives and however often, and whatever the
service answers. It may crash and restart, and its links may lose, reorder and duplicate. -/
theorem calls_le_scheduled (env : EnvModel (sig K P A)) {events : List (Event (sig K P A))}
    {c : SysState (system (K := K) (P := P) config)}
    (hrun : (SysState.init (system config) env).run env events = some c) (key : K) :
    calls key (deeds events) ≤ max 1 config.maxAttempts * schedulings key (deeds events) := by
  suffices h : calls key (deeds events) + owed key c
      ≤ max 1 config.maxAttempts * schedulings key (deeds events) from
    Nat.le_trans (Nat.le_add_right _ _) h
  refine System.Reachable.run_induction
    (P := fun events c => calls key (deeds events) + owed key c
      ≤ max 1 config.maxAttempts * schedulings key (deeds events)) .init hrun ?_ ?_
  · have hinit : owed key (SysState.init (system (K := K) (P := P) config) env) = 0 :=
      (owed_start (env := env) key (SysState.blank _)).trans
        (by simp [owed, rest, SysState.blank, actor, entry])
    simp [hinit, calls, schedulings, deeds]
  rintro evs c₁ ev c₂ hc hle hstep
  have h := owed_event (env := env) key hc hstep
  rw [calls_snoc, schedulings_snoc, Nat.mul_add]
  omega

end Lanes.Schedule
