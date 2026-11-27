/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Core.Join
public import Lanes.Outside.Rpc

/-!
# Schedule: work that is due later, retried until it succeeds or gives up

The scheduler holds jobs under ids its requester names. A job is due at a time; then it calls
the outside (`Work.call`, retried by its `Retry` policy until an answer `Config.ok` accepts, its
attempts or its time run out, or it is cancelled), or tells the requester once (`Work.once`), or
every period until it is cancelled (`Work.every`). A job id already held is not scheduled again
(`already`); beyond `maxJobs` jobs or `maxPayload` a job is refused at once (rule 2.6). A job that
gives up is answered `failed`, with its payload: the dead letter.

The semantics has no clock (D42), so the scheduler keeps the latest time it knows, `now_ms`: the
time each scheduling carries, and the deadline of each of its own timers that fires, since the
runtime fires a timer no earlier than its deadline (`Kernel.timerNext`). Each job waits on one
timer, armed for its `at_ms`: `due` while it waits, `expire` while an attempt is out. An attempt
is dispatched only when its job's `due` fires, and stamped with the time then known
(`Attempt.start_ms`), which is no earlier than the time the job was due. An attempt is over when
its answer comes or when its `expire` fires, which emits `abandon`, so that the adapter can cut
the call off; only then may the next start, after the backoff. A start arms every job's timer
again and dispatches nothing.

`system` is the scheduler alone; `attach sys config use` is it beside `sys`, which schedules and
cancels through its outputs and is told the notices and answers as inputs, while attempts and
abandons leave the join and answers to attempts come back as inputs. `callee` is what the
service called may do. `Lanes.Behaviours.Schedule.Sound` proves what holds in every run and
`Lanes.Semantics.Schedule` that every job ends in a fair run.
-/

@[expose] public section

namespace Lanes.Schedule

/-- How a call is retried (rule 2.6). The wait after the `n`th failed attempt is
`min cap_ms (base_ms * 2 ^ (n - 1))` and a jitter of at most `jitter_ms`. -/
lanes_data structure Retry where
  /-- At least one; at most `Config.maxAttempts`. -/
  maxAttempts : Nat := 5
  /-- How long the adapter waits for one answer before it says `unknown`. -/
  deadline_ms : Nat := 10000
  base_ms : Nat := 1000
  cap_ms : Nat := 60000
  jitter_ms : Nat := 0
  /-- No attempt is started after this time. -/
  until_ms : Option Nat := none
  deriving DecidableEq, Repr, Hashable, Codable

lanes_data inductive Work where
  | call (retry : Retry)
  | once
  /-- A notice every `max 1 period_ms`, until the job is cancelled. -/
  | every (period_ms : Nat)
  deriving DecidableEq, Repr, Hashable, Codable

lanes_data structure Spec (K P : Type) where
  key : K
  payload : P
  work : Work
  /-- When the job is first due. -/
  at_ms : Nat
  deriving DecidableEq, Repr, Hashable, Codable

lanes_data inductive Phase where
  | waiting
  | running
  /-- Cancelled while an attempt is out: it ends when the attempt does. -/
  | cancelling
  deriving DecidableEq, Repr, Hashable, Codable

/-- `at_ms` is when the timer the job waits on is due: its next run while it waits, the end of
its attempt's wait while one is out. `attempt` counts the attempts started. -/
lanes_data structure Job (K P : Type) where
  key : K
  payload : P
  work : Work
  at_ms : Nat
  attempt : Nat
  phase : Phase
  deriving DecidableEq, Repr, Hashable, Codable

/-- Durable: a restart that forgot a job would never run it. -/
lanes_data structure State (K P : Type) where
  now_ms : Nat
  jobs : List (Job K P)
  deriving DecidableEq, Repr, Hashable, Codable

/-- One attempt of a call, named by its key and number (rule 3.4): the far side can tell a
retry from a new request by the key. -/
lanes_data structure Attempt (K P : Type) where
  key : K
  attempt : Nat
  /-- The scheduler's time when it started the attempt. -/
  start_ms : Nat
  deadline_ms : Nat
  payload : P
  deriving DecidableEq, Repr, Hashable, Codable

lanes_data inductive Refusal where
  | full
  | tooLarge
  deriving DecidableEq, Repr, Hashable, Codable

lanes_data inductive Outcome (P A : Type) where
  | scheduled
  /-- The id is held by a job already, which is left as it is. -/
  | already
  | refused (why : Refusal)
  | cancelled
  | succeeded (answer : A)
  /-- The dead letter: the job gave up after `attempts`, the last of which was answered `last`
  (`none`: `unknown`, or no answer by the deadline). -/
  | failed (payload : P) (attempts : Nat) (last : Option A)
  deriving DecidableEq, Repr, Hashable, Codable

lanes_data inductive Input (K P A : Type) where
  /-- `now_ms` is the time the request was made, which the scheduler learns. -/
  | schedule (now_ms : Nat) (spec : Spec K P)
  | cancel (key : K)
  | reply (key : K) (attempt : Nat) (reply : Rpc.Reply A)
  deriving DecidableEq, Repr, Hashable, Codable

lanes_data inductive Output (K P A : Type) where
  | call (attempt : Attempt K P)
  /-- The attempt's wait is over with no answer: the scheduler no longer waits for it. -/
  | abandon (key : K) (attempt : Nat)
  | notice (key : K) (payload : P)
  | answer (key : K) (outcome : Outcome P A)
  deriving DecidableEq, Repr, Hashable, Codable

lanes_data inductive Msg (K P A : Type) where
  | schedule (now_ms : Nat) (spec : Spec K P)
  | cancel (key : K)
  | reply (key : K) (attempt : Nat) (reply : Rpc.Reply A)
  /-- A waiting job's run time. -/
  | due (key : K)
  /-- The end of the wait for an attempt's answer. -/
  | expire (key : K)
  deriving DecidableEq, Repr, Hashable, Codable

/-- Every limit is explicit (rule 2.6). -/
structure Config (K P A : Type) where
  maxJobs : Nat := 1024
  maxPayload : Nat := 4096
  size : P → Nat := fun _ => 0
  /-- The most attempts any job makes, whatever its `Retry` asks. -/
  maxAttempts : Nat := 16
  /-- How much longer than the adapter's deadline the scheduler waits for an answer. -/
  grace_ms : Nat := 1000
  /-- The answers that are a success; any other is a failure worth another attempt. -/
  ok : A → Bool := fun _ => true
  /-- The jitter of the wait after attempt `n` of a key, before it is cut to `jitter_ms`:
  deterministic, since a step is pure (`Schedule.hashJitter`). -/
  jitter : K → Nat → Nat := fun _ _ => 0

/-- A jitter from the hash of the key and the attempt. -/
def hashJitter {K : Type} [Hashable K] (key : K) (n : Nat) : Nat :=
  (mixHash (hash key) (hash n)).toNat

namespace Config

variable {K P A : Type}

/-- The attempts a job of `work` may make. -/
def cap (config : Config K P A) : Work → Nat
  | .call retry => min (max 1 config.maxAttempts) (max 1 retry.maxAttempts)
  | _ => 1

/-- The wait after attempt `n` of `key` failed. -/
def backoff (config : Config K P A) (retry : Retry) (key : K) (n : Nat) : Nat :=
  min retry.cap_ms (retry.base_ms * 2 ^ (n - 1)) + config.jitter key n % (retry.jitter_ms + 1)

/-- How long an attempt is waited for. -/
def wait (config : Config K P A) (retry : Retry) : Nat :=
  retry.deadline_ms + config.grace_ms

theorem cap_le (config : Config K P A) (work : Work) : config.cap work ≤ max 1 config.maxAttempts := by
  cases work <;> simp [cap] <;> omega

theorem one_le_cap (config : Config K P A) (work : Work) : 1 ≤ config.cap work := by
  cases work <;> simp [cap] <;> omega

end Config

section List

variable {K P : Type} [DecidableEq K]

def keys (jobs : List (Job K P)) : List K := jobs.map (·.key)

def entry (jobs : List (Job K P)) (key : K) : Option (Job K P) :=
  jobs.find? fun j => decide (j.key = key)

def put (jobs : List (Job K P)) (j : Job K P) : List (Job K P) :=
  jobs.map fun b => if b.key = j.key then j else b

def remove (jobs : List (Job K P)) (key : K) : List (Job K P) :=
  jobs.filter fun j => decide (j.key ≠ key)

/-- The jobs with the entry of `key` replaced, or taken out with `none`. -/
def set (jobs : List (Job K P)) (key : K) : Option (Job K P) → List (Job K P)
  | some j => put jobs j
  | none => remove jobs key

omit [DecidableEq K] in
@[simp] theorem keys_nil : keys ([] : List (Job K P)) = [] := rfl

omit [DecidableEq K] in
@[simp] theorem keys_cons (j : Job K P) (jobs : List (Job K P)) :
    keys (j :: jobs) = j.key :: keys jobs := rfl

omit [DecidableEq K] in
theorem mem_keys {jobs : List (Job K P)} {key : K} :
    key ∈ keys jobs ↔ ∃ j ∈ jobs, j.key = key := by
  simp [keys]

@[simp] theorem keys_put (jobs : List (Job K P)) (j : Job K P) :
    keys (put jobs j) = keys jobs := by
  simp only [keys, put, List.map_map]
  congr 1
  funext b
  by_cases h : b.key = j.key <;> simp [h]

@[simp] theorem length_put (jobs : List (Job K P)) (j : Job K P) :
    (put jobs j).length = jobs.length :=
  List.length_map ..

theorem mem_put {jobs : List (Job K P)} {j b : Job K P} (h : b ∈ put jobs j) :
    b = j ∨ (b ∈ jobs ∧ b.key ≠ j.key) := by
  obtain ⟨b', hb', rfl⟩ := List.mem_map.mp h
  by_cases hk : b'.key = j.key
  · simp [hk]
  · simp [hk, hb']

theorem mem_remove {jobs : List (Job K P)} {key : K} {j : Job K P} :
    j ∈ remove jobs key ↔ j ∈ jobs ∧ j.key ≠ key := by
  simp [remove]

theorem keys_remove (jobs : List (Job K P)) (key : K) :
    keys (remove jobs key) = (keys jobs).filter fun k => decide (k ≠ key) := by
  simp [keys, remove, List.filter_map, Function.comp_def]

theorem length_remove_le (jobs : List (Job K P)) (key : K) :
    (remove jobs key).length ≤ jobs.length :=
  List.length_filter_le ..

theorem entry_some {jobs : List (Job K P)} {key : K} {j : Job K P}
    (h : entry jobs key = some j) : j ∈ jobs ∧ j.key = key := by
  have hp := List.find?_some h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using hp⟩

theorem entry_eq_none {jobs : List (Job K P)} {key : K} :
    entry jobs key = none ↔ key ∉ keys jobs := by
  simp [entry, mem_keys]

theorem entry_of_mem {jobs : List (Job K P)} {j : Job K P} (hnodup : (keys jobs).Nodup)
    (h : j ∈ jobs) : entry jobs j.key = some j := by
  induction jobs with
  | nil => simp at h
  | cons b jobs ih =>
    simp only [keys_cons, List.nodup_cons] at hnodup
    rcases List.mem_cons.mp h with rfl | h
    · simp [entry]
    · have hne : b.key ≠ j.key := fun he => hnodup.1 (he ▸ mem_keys.mpr ⟨j, h, rfl⟩)
      simpa [entry, hne] using ih hnodup.2 h

theorem entry_put_self {jobs : List (Job K P)} {j : Job K P}
    (h : j.key ∈ keys jobs) : entry (put jobs j) j.key = some j := by
  induction jobs with
  | nil => simp at h
  | cons b jobs ih =>
    by_cases hb : b.key = j.key
    · simp [entry, put, hb]
    · have h' : j.key ∈ keys jobs := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm hb
        · exact h
      simpa [entry, put, hb] using ih h'

theorem entry_put_of_ne {jobs : List (Job K P)} {j : Job K P} {key : K}
    (h : key ≠ j.key) : entry (put jobs j) key = entry jobs key := by
  induction jobs with
  | nil => rfl
  | cons b jobs ih =>
    by_cases hb : b.key = j.key
    · have hne : ¬j.key = key := fun he => h he.symm
      have hne' : ¬b.key = key := hb ▸ hne
      simpa [entry, put, hb, hne, hne'] using ih
    · by_cases hk : b.key = key <;> simp_all [entry, put]

@[simp] theorem entry_remove_self (jobs : List (Job K P)) (key : K) :
    entry (remove jobs key) key = none :=
  entry_eq_none.mpr (by simp [keys_remove])

theorem entry_remove_of_ne (jobs : List (Job K P)) {key key' : K} (h : key' ≠ key) :
    entry (remove jobs key) key' = entry jobs key' := by
  simp only [entry, remove, List.find?_filter]
  congr 1
  funext j
  by_cases hj : j.key = key' <;> simp [hj, h]

theorem entry_cons_of_ne (j : Job K P) (jobs : List (Job K P)) {key : K}
    (h : j.key ≠ key) : entry (j :: jobs) key = entry jobs key := by
  simp [entry, h]

@[simp] theorem entry_cons_self (j : Job K P) (jobs : List (Job K P)) :
    entry (j :: jobs) j.key = some j := by
  simp [entry]

/-- Setting the entry of a key held, to a job of that key or to none, gives that entry. -/
theorem entry_set_self {jobs : List (Job K P)} {key : K} (hheld : key ∈ keys jobs)
    {e : Option (Job K P)} (he : ∀ j, e = some j → j.key = key) :
    entry (set jobs key e) key = e := by
  cases e with
  | none => exact entry_remove_self ..
  | some j =>
    obtain rfl := he j rfl
    exact entry_put_self hheld

theorem entry_set_of_ne {jobs : List (Job K P)} {key key' : K} (h : key' ≠ key)
    {e : Option (Job K P)} (he : ∀ j, e = some j → j.key = key) :
    entry (set jobs key e) key' = entry jobs key' := by
  cases e with
  | none => exact entry_remove_of_ne _ h
  | some j =>
    obtain rfl := he j rfl
    exact entry_put_of_ne h

theorem mem_set {jobs : List (Job K P)} {key : K} {e : Option (Job K P)}
    (he : ∀ j, e = some j → j.key = key) {b : Job K P} (hb : b ∈ set jobs key e) :
    e = some b ∨ (b ∈ jobs ∧ b.key ≠ key) := by
  cases e with
  | none => exact .inr (mem_remove.mp hb)
  | some j =>
    obtain rfl := he j rfl
    rcases mem_put hb with rfl | h
    · exact .inl rfl
    · exact .inr h

theorem length_set_le (jobs : List (Job K P)) (key : K) (e : Option (Job K P)) :
    (set jobs key e).length ≤ jobs.length := by
  cases e with
  | none => exact length_remove_le ..
  | some j => exact Nat.le_of_eq (length_put ..)

theorem nodup_set {jobs : List (Job K P)} (key : K) {e : Option (Job K P)}
    (he : ∀ j, e = some j → j.key = key) (h : (keys jobs).Nodup) :
    (keys (set jobs key e)).Nodup := by
  cases e with
  | none =>
    rw [set, keys_remove]
    exact h.filter _
  | some j =>
    obtain rfl := he j rfl
    simpa [set] using h

end List

abbrev sig (K P A : Type) [DecidableEq K] [DecidableEq P] [DecidableEq A] : Signature where
  Id := Unit
  Msg _ := Schedule.Msg K P A
  In := Input K P A
  Out := Output K P A

variable {K P A : Type} [DecidableEq K] [DecidableEq P] [DecidableEq A]

abbrev Eff (K P A : Type) [DecidableEq K] [DecidableEq P] [DecidableEq A] : Type :=
  Effect (sig K P A) ()

/-- The timer a job waits on. -/
def timer (j : Job K P) : Schedule.Msg K P A :=
  match j.phase with
  | .waiting => .due j.key
  | _ => .expire j.key

/-- What happened to the job a message is about: its attempt is answered, or not by the end of
its wait; its time came; it is cancelled. -/
inductive Act (A : Type) where
  | cancel
  | reply (attempt : Nat) (reply : Rpc.Reply A)
  | due
  | expire

/-- What an act does to one job: the job after it (`none`: it is over), the time then known,
and the effects. -/
structure Change (K P A : Type) [DecidableEq K] [DecidableEq P] [DecidableEq A] where
  job : Option (Job K P)
  now_ms : Nat
  effs : List (Eff K P A)

/-- An attempt of `j` failed at `now_ms`, with `last` its answer: after the backoff the job is
due again, or, its attempts or its time spent, it is over and answered `failed`. -/
def fail (config : Config K P A) (now_ms : Nat) (j : Job K P) (last : Option A) :
    Option (Job K P) × List (Eff K P A) :=
  let over : Option (Job K P) × List (Eff K P A) :=
    (none, [.emit (.answer j.key (.failed j.payload j.attempt last))])
  match j.work with
  | .call retry =>
    let delay := config.backoff retry j.key j.attempt
    if j.attempt < config.cap j.work && retry.until_ms.all (now_ms + delay ≤ ·) then
      (some { j with phase := .waiting, at_ms := now_ms + delay }, [.after delay (.due j.key)])
    else over
  | _ => over

/-- The attempt out for `j` is over: with an answer (`some`), or with none. -/
def over (config : Config K P A) (now_ms : Nat) (j : Job K P) (result : Option A) :
    Option (Job K P) × List (Eff K P A) :=
  match j.phase, result with
  | .cancelling, _ => (none, [.emit (.answer j.key .cancelled)])
  | _, some a =>
    if config.ok a then (none, [.emit (.answer j.key (.succeeded a))])
    else fail config now_ms j (some a)
  | _, none => fail config now_ms j none

/-- `j` is due at `now_ms`. -/
def run (config : Config K P A) (now_ms : Nat) (j : Job K P) :
    Option (Job K P) × List (Eff K P A) :=
  match j.work with
  | .call retry =>
    (some { j with attempt := j.attempt + 1, phase := .running, at_ms := now_ms + config.wait retry },
      [.emit (.call ⟨j.key, j.attempt + 1, now_ms, retry.deadline_ms, j.payload⟩),
        .after (config.wait retry) (.expire j.key)])
  | .once => (none, [.emit (.notice j.key j.payload)])
  | .every period_ms =>
    (some { j with at_ms := now_ms + max 1 period_ms },
      [.emit (.notice j.key j.payload), .after (max 1 period_ms) (.due j.key)])

/-- The answer a reply carries; `unknown` carries none. -/
def answerOf : Rpc.Reply A → Option A
  | .answer a => some a
  | .unknown => none

/-- What `act` does to `j`, when the time known is `now_ms`. -/
def onJob (config : Config K P A) (now_ms : Nat) (j : Job K P) : Act A → Change K P A
  | .cancel =>
    match j.phase with
    | .waiting => ⟨none, now_ms, [.cancel (.due j.key), .emit (.answer j.key .cancelled)]⟩
    | .running => ⟨some { j with phase := .cancelling }, now_ms, []⟩
    | .cancelling => ⟨some j, now_ms, []⟩
  | .reply attempt reply =>
    if j.phase ≠ .waiting ∧ j.attempt = attempt then
      let r := over config now_ms j (answerOf reply)
      ⟨r.1, now_ms, .cancel (.expire j.key) :: r.2⟩
    else ⟨some j, now_ms, []⟩
  | .expire =>
    if j.phase ≠ .waiting then
      let now_ms := max now_ms j.at_ms
      let r := over config now_ms j none
      ⟨r.1, now_ms, .emit (.abandon j.key j.attempt) :: r.2⟩
    else ⟨some j, now_ms, []⟩
  | .due =>
    if j.phase = .waiting then
      let now_ms := max now_ms j.at_ms
      let r := run config now_ms j
      ⟨r.1, now_ms, r.2⟩
    else ⟨some j, now_ms, []⟩

/-- `act` on the job held under `key`, if any. -/
def touch (config : Config K P A) (s : State K P) (key : K) (act : Act A) :
    State K P × List (Eff K P A) :=
  match entry s.jobs key with
  | some j =>
    let c := onJob config s.now_ms j act
    (⟨c.now_ms, set s.jobs key c.job⟩, c.effs)
  | none => (s, [])

def admit (config : Config K P A) (s : State K P) (now_ms : Nat) (spec : Spec K P) :
    State K P × List (Eff K P A) :=
  let now_ms := max s.now_ms now_ms
  if spec.key ∈ keys s.jobs then (⟨now_ms, s.jobs⟩, [.emit (.answer spec.key .already)])
  else if config.maxPayload < config.size spec.payload then
    (⟨now_ms, s.jobs⟩, [.emit (.answer spec.key (.refused .tooLarge))])
  else if config.maxJobs ≤ s.jobs.length then
    (⟨now_ms, s.jobs⟩, [.emit (.answer spec.key (.refused .full))])
  else
    (⟨now_ms, ⟨spec.key, spec.payload, spec.work, spec.at_ms, 0, .waiting⟩ :: s.jobs⟩,
      [.emit (.answer spec.key .scheduled), .after (spec.at_ms - now_ms) (.due spec.key)])

def step (config : Config K P A) (s : State K P) : Schedule.Msg K P A → State K P × List (Eff K P A)
  | .schedule now_ms spec => admit config s now_ms spec
  | .cancel key => touch config s key .cancel
  | .reply key attempt reply => touch config s key (.reply attempt reply)
  | .due key => touch config s key .due
  | .expire key => touch config s key .expire

/-- A start arms again the timer each job waits on, for the time it is due as far as the
scheduler knows. An attempt out is not dispatched again: its `expire` ends it. -/
def rearm (s : State K P) (j : Job K P) : Eff K P A :=
  .after (j.at_ms - s.now_ms) (timer j)

def actor (config : Config K P A) : (sig K P A).Actor () (State K P) where
  init := ⟨0, []⟩
  step := step config
  recover s := (s, s.jobs.map (rearm s))

abbrev system (config : Config K P A) : System (sig K P A) where
  State _ := State K P
  actor _ := actor config
  accept
    | .schedule now_ms spec => ⟨(), .schedule now_ms spec⟩
    | .cancel key => ⟨(), .cancel key⟩
    | .reply key attempt reply => ⟨(), .reply key attempt reply⟩
  boot := [()]

/-- How a system uses the scheduler: which of its outputs schedule or cancel a job, and the
inputs a notice and an answer are. -/
structure Use (τ : Signature) (K P A : Type) where
  scheduled : τ.Out → Option (Nat × Spec K P)
  cancelled : τ.Out → Option K := fun _ => none
  notice : K → P → τ.In
  answer : K → Outcome P A → τ.In

/-- A scheduling goes to the scheduler, a notice and an answer to the system that scheduled;
attempts and abandons leave the join. -/
def Use.wiring {τ : Signature} (use : Use τ K P A) : Wiring (sig K P A) τ where
  toRight
    | .notice key payload => some (use.notice key payload)
    | .answer key outcome => some (use.answer key outcome)
    | .call _ | .abandon .. => none
  toLeft out :=
    match use.scheduled out with
    | some (now_ms, spec) => some (.schedule now_ms spec)
    | none => (use.cancelled out).map .cancel

/-- `sys` with the scheduler beside it. -/
abbrev attach {τ : Signature} (sys : System τ) (config : Config K P A) (use : Use τ K P A) :
    System (joinSig (sig K P A) τ) :=
  (system config).join sys use.wiring

/-- The attempts out at the service, and those abandoned before the service was handed them:
outputs are handed over in any order. -/
structure Callee (K : Type) where
  out : List (K × Nat) := []
  early : List (K × Nat) := []

/-- Two lists that hold the same elements as often: the order the attempts went out in is not
the service's state, and the checker keeps one state for every order. -/
def sameBag {α : Type} [BEq α] (a b : List α) : Bool :=
  a.length == b.length && a.all fun x => a.count x == b.count x

/-- A hash that does not depend on the order of the list. -/
def bagHash {α : Type} [Hashable α] (l : List α) : UInt64 :=
  l.foldl (fun h x => h + mixHash 17 (hash x)) 0

instance {K : Type} [BEq K] : BEq (Callee K) where
  beq a b := sameBag a.out b.out && sameBag a.early b.early

instance {K : Type} [Hashable K] : Hashable (Callee K) where
  hash d := mixHash (bagHash d.out) (bagHash d.early)

/-- What the service called may do: answer an attempt that is out, once, with any answer or
`unknown`, or never. An attempt abandoned is over: the adapter cut it off. -/
def callee : Outside (sig K P A) (Callee K) where
  init := {}
  allow d x :=
    match x with
    | .reply key attempt _ =>
      if (key, attempt) ∈ d.out then some { d with out := d.out.erase (key, attempt) } else none
    | _ => none
  observe d o :=
    match o with
    | .call a =>
      if (a.key, a.attempt) ∈ d.early then { d with early := d.early.erase (a.key, a.attempt) }
      else { d with out := (a.key, a.attempt) :: d.out }
    | .abandon key attempt =>
      if (key, attempt) ∈ d.out then { d with out := d.out.erase (key, attempt) }
      else { d with early := (key, attempt) :: d.early }
    | _ => d

end Lanes.Schedule
