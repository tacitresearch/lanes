/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Actors.Join
public import Lanes.Actors.Outside
public import Lanes.Data.Declare

/-!
# Jobs: work done outside a step, with retries, deadlines and a bound

Work that must not run in a step (a call to another service, slow pure work) is submitted to
the jobs actor under a key its requester chooses. The actor dispatches each attempt as an
output, a pool of workers performs it (`Lanes.Env.Jobs`), and the worker's result comes back as
an input. The actor answers each key it admits once: with a result the policy accepts, with
the last result after `maxAttempts`, with `timedOut` when the last attempt's deadline passed,
or at once with `refused` when `maxInFlight` jobs are active (rule 2.6). Every attempt carries
the key, so the far side can tell a retry from a new request (rule 3.4).

`system` is the actor alone, and `attach sys config use` is it joined beside `sys`, whose outputs
`use` reads as submissions and to which it hands each answer as an input; attempts leave the
join as outputs and results come back as inputs. `Lanes.Behaviours.JobsSound` proves it answers no key more often
than it is submitted and that a retry carries the job it retries, `Lanes.Semantics.JobsLive`
that every job it admits is answered in a fair run.
-/

@[expose] public section

namespace Lanes.Jobs

lanes_data inductive Phase where
  | running
  | backoff
  deriving DecidableEq, Repr, Hashable, Codable

/-- A job holding one of the slots, from its first attempt to its answer. `attempt` is the
attempt being made or, while the job backs off, the one that failed; the first is `1`. -/
lanes_data structure Active (K J : Type) where
  key : K
  job : J
  attempt : Nat
  phase : Phase
  deriving DecidableEq, Repr, Hashable, Codable

lanes_data inductive Outcome (R : Type) where
  | done (r : R)
  /-- The result of the last attempt, which the policy would have retried. -/
  | failed (r : R)
  | timedOut
  | refused
  deriving DecidableEq, Repr, Hashable, Codable

lanes_data inductive Input (K J R : Type) where
  | submit (key : K) (job : J)
  | result (key : K) (attempt : Nat) (r : R)
  deriving DecidableEq, Repr, Hashable, Codable

lanes_data inductive Output (K J R : Type) where
  | answer (key : K) (outcome : Outcome R)
  | dispatch (key : K) (attempt : Nat) (job : J)
  deriving DecidableEq, Repr, Hashable, Codable

lanes_data inductive Msg (K J R : Type) where
  | submit (key : K) (job : J)
  | result (key : K) (attempt : Nat) (r : R)
  /-- The deadline of the attempt being made. -/
  | expire (key : K)
  /-- The end of a backoff. -/
  | retry (key : K)
  deriving DecidableEq, Repr, Hashable, Codable

/-- Every limit is explicit (rule 2.6). -/
structure Config (R : Type) where
  /-- Jobs active at once. A job submitted when all are taken is refused. At least one. -/
  maxInFlight : Nat := 16
  /-- At least one. -/
  maxAttempts : Nat := 3
  attempt_ms : Nat := 30000
  /-- The wait after the first failed attempt; it doubles after each one, up to
  `maxBackoff_ms`. -/
  backoff_ms : Nat := 200
  maxBackoff_ms : Nat := 30000
  /-- The results that are failures worth another attempt. -/
  retryable : R → Bool := fun _ => false

namespace Config

variable {R : Type}

def slots (config : Config R) : Nat := max 1 config.maxInFlight

def cap (config : Config R) : Nat := max 1 config.maxAttempts

def backoff (config : Config R) (attempt : Nat) : Nat :=
  min config.maxBackoff_ms (config.backoff_ms * 2 ^ (attempt - 1))

end Config

section List

variable {K J : Type} [DecidableEq K]

def keys (active : List (Active K J)) : List K := active.map (·.key)

def entry (active : List (Active K J)) (key : K) : Option (Active K J) :=
  active.find? fun a => decide (a.key = key)

def put (active : List (Active K J)) (a : Active K J) : List (Active K J) :=
  active.map fun b => if b.key = a.key then a else b

def remove (active : List (Active K J)) (key : K) : List (Active K J) :=
  active.filter fun a => decide (a.key ≠ key)

omit [DecidableEq K] in
@[simp] theorem keys_nil : keys ([] : List (Active K J)) = [] := rfl

omit [DecidableEq K] in
@[simp] theorem keys_cons (a : Active K J) (active : List (Active K J)) :
    keys (a :: active) = a.key :: keys active := rfl

omit [DecidableEq K] in
@[simp] theorem length_keys (active : List (Active K J)) : (keys active).length = active.length :=
  List.length_map ..

omit [DecidableEq K] in
theorem mem_keys {active : List (Active K J)} {key : K} :
    key ∈ keys active ↔ ∃ a ∈ active, a.key = key := by
  simp [keys]

@[simp] theorem keys_put (active : List (Active K J)) (a : Active K J) :
    keys (put active a) = keys active := by
  simp only [keys, put, List.map_map]
  congr 1
  funext b
  by_cases h : b.key = a.key <;> simp [h]

@[simp] theorem length_put (active : List (Active K J)) (a : Active K J) :
    (put active a).length = active.length :=
  List.length_map ..

theorem mem_put {active : List (Active K J)} {a b : Active K J} (h : b ∈ put active a) :
    b = a ∨ (b ∈ active ∧ b.key ≠ a.key) := by
  obtain ⟨b', hb', rfl⟩ := List.mem_map.mp h
  by_cases hk : b'.key = a.key
  · simp [hk]
  · simp [hk, hb']

theorem mem_remove {active : List (Active K J)} {key : K} {a : Active K J} :
    a ∈ remove active key ↔ a ∈ active ∧ a.key ≠ key := by
  simp [remove]

theorem keys_remove (active : List (Active K J)) (key : K) :
    keys (remove active key) = (keys active).filter fun k => decide (k ≠ key) := by
  simp [keys, remove, List.filter_map, Function.comp_def]

theorem length_remove_le (active : List (Active K J)) (key : K) :
    (remove active key).length ≤ active.length :=
  List.length_filter_le ..

theorem nodup_remove {active : List (Active K J)} (key : K) (h : (keys active).Nodup) :
    (keys (remove active key)).Nodup := by
  rw [keys_remove]
  exact h.filter _

theorem entry_some {active : List (Active K J)} {key : K} {a : Active K J}
    (h : entry active key = some a) : a ∈ active ∧ a.key = key := by
  have hp := List.find?_some h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using hp⟩

theorem entry_eq_none {active : List (Active K J)} {key : K} :
    entry active key = none ↔ key ∉ keys active := by
  simp [entry, mem_keys]

theorem entry_of_mem {active : List (Active K J)} {a : Active K J} (hnodup : (keys active).Nodup)
    (h : a ∈ active) : entry active a.key = some a := by
  induction active with
  | nil => simp at h
  | cons b active ih =>
    simp only [keys_cons, List.nodup_cons] at hnodup
    rcases List.mem_cons.mp h with rfl | h
    · simp [entry]
    · have hne : b.key ≠ a.key := fun he => hnodup.1 (he ▸ mem_keys.mpr ⟨a, h, rfl⟩)
      simpa [entry, hne] using ih hnodup.2 h

theorem entry_put_self {active : List (Active K J)} {a : Active K J}
    (h : a.key ∈ keys active) : entry (put active a) a.key = some a := by
  induction active with
  | nil => simp at h
  | cons b active ih =>
    by_cases hb : b.key = a.key
    · simp [entry, put, hb]
    · have h' : a.key ∈ keys active := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm hb
        · exact h
      simpa [entry, put, hb] using ih h'

theorem entry_put_of_ne {active : List (Active K J)} {a : Active K J} {key : K}
    (h : key ≠ a.key) : entry (put active a) key = entry active key := by
  induction active with
  | nil => rfl
  | cons b active ih =>
    by_cases hb : b.key = a.key
    · have hne : ¬a.key = key := fun he => h he.symm
      have hne' : ¬b.key = key := hb ▸ hne
      simpa [entry, put, hb, hne, hne'] using ih
    · by_cases hk : b.key = key <;> simp_all [entry, put]

@[simp] theorem entry_remove_self (active : List (Active K J)) (key : K) :
    entry (remove active key) key = none :=
  entry_eq_none.mpr (by simp [keys_remove])

theorem entry_remove_of_ne (active : List (Active K J)) {key key' : K} (h : key' ≠ key) :
    entry (remove active key) key' = entry active key' := by
  simp only [entry, remove, List.find?_filter]
  congr 1
  funext a
  by_cases ha : a.key = key' <;> simp [ha, h]

theorem entry_cons_of_ne (a : Active K J) (active : List (Active K J)) {key : K}
    (h : a.key ≠ key) : entry (a :: active) key = entry active key := by
  simp [entry, h]

@[simp] theorem entry_cons_self (a : Active K J) (active : List (Active K J)) :
    entry (a :: active) a.key = some a := by
  simp [entry]

variable {R : Type}

/-- No more jobs are active than there are slots, and no key is active twice. -/
def Within (config : Config R) (active : List (Active K J)) : Prop :=
  active.length ≤ config.slots ∧ (keys active).Nodup

/-- Every active job is on an attempt from the first to the last, and one that backs off has
another to make. -/
def Attempts (config : Config R) (active : List (Active K J)) : Prop :=
  ∀ a ∈ active, 1 ≤ a.attempt ∧ a.attempt ≤ config.cap ∧
    (a.phase = .backoff → a.attempt < config.cap)

theorem attempts_put {config : Config R} {active : List (Active K J)} {a : Active K J}
    (h : Attempts config active) (ha : 1 ≤ a.attempt ∧ a.attempt ≤ config.cap ∧
      (a.phase = .backoff → a.attempt < config.cap)) : Attempts config (put active a) := by
  intro b hb
  rcases mem_put hb with rfl | ⟨hb, -⟩
  · exact ha
  · exact h b hb

theorem attempts_remove {config : Config R} {active : List (Active K J)} (key : K)
    (h : Attempts config active) : Attempts config (remove active key) :=
  fun b hb => h b (mem_remove.mp hb).1

end List

abbrev sig (K J R : Type) [DecidableEq K] [DecidableEq J] [DecidableEq R] : Signature where
  Id := Unit
  Msg _ := Jobs.Msg K J R
  In := Input K J R
  Out := Output K J R

variable {K J R : Type} [DecidableEq K] [DecidableEq J] [DecidableEq R]

abbrev Eff (K J R : Type) [DecidableEq K] [DecidableEq J] [DecidableEq R] : Type :=
  Effect (sig K J R) ()

/-- The timer an active job waits on. -/
def timer (a : Active K J) : Jobs.Msg K J R :=
  match a.phase with
  | .running => .expire a.key
  | .backoff => .retry a.key

/-- An attempt of `a` failed: after `first`, another attempt once a backoff has passed, or the
answer `outcome` if it was the last. -/
def fail (config : Config R) (active : List (Active K J)) (a : Active K J) (outcome : Outcome R)
    (first : List (Eff K J R)) : List (Active K J) × List (Eff K J R) :=
  if a.attempt < config.cap then
    (put active { a with phase := .backoff },
      first ++ [.after (config.backoff a.attempt) (.retry a.key)])
  else (remove active a.key, first ++ [.emit (.answer a.key outcome)])

def step (config : Config R) (active : List (Active K J)) :
    Jobs.Msg K J R → List (Active K J) × List (Eff K J R)
  | .submit key job =>
    if key ∈ keys active then (active, [])
    else if config.slots ≤ active.length then (active, [.emit (.answer key .refused)])
    else (⟨key, job, 1, .running⟩ :: active,
      [.emit (.dispatch key 1 job), .after config.attempt_ms (.expire key)])
  | .result key attempt r =>
    match entry active key with
    | some a =>
      if a.phase = .running ∧ a.attempt = attempt then
        if config.retryable r then fail config active a (.failed r) [.cancel (.expire key)]
        else (remove active key, [.cancel (.expire key), .emit (.answer key (.done r))])
      else (active, [])
    | none => (active, [])
  | .expire key =>
    match entry active key with
    | some a => if a.phase = .running then fail config active a .timedOut [] else (active, [])
    | none => (active, [])
  | .retry key =>
    match entry active key with
    | some a =>
      if a.phase = .backoff then
        (put active { a with attempt := a.attempt + 1, phase := .running },
          [.emit (.dispatch key (a.attempt + 1) a.job), .after config.attempt_ms (.expire key)])
      else (active, [])
    | none => (active, [])

/-- A start arms again the timer each active job waits on. An attempt in flight is not
dispatched again: its deadline does that, if no result comes. -/
def rearm (config : Config R) (a : Active K J) : Eff K J R :=
  match a.phase with
  | .running => .after config.attempt_ms (.expire a.key)
  | .backoff => .after (config.backoff a.attempt) (.retry a.key)

/-- Its state is durable: a restart that forgot an active job would never answer it. -/
def actor (config : Config R) : (sig K J R).Actor () (List (Active K J)) where
  init := []
  step := step config
  recover active := (active, active.map (rearm config))

abbrev system (config : Config R) : System (sig K J R) where
  State _ := List (Active K J)
  actor _ := actor config
  accept
    | .submit key job => ⟨(), .submit key job⟩
    | .result key attempt r => ⟨(), .result key attempt r⟩
  boot := [()]

/-- How a system uses jobs: which of its outputs submit one, and the input an answer is. -/
structure Use (τ : Signature) (K J R : Type) where
  submitted : τ.Out → Option (K × J)
  answer : K → Outcome R → τ.In

/-- A submission goes to the jobs actor, an answer to the system that submitted it; attempts
leave the join. -/
def Use.wiring {τ : Signature} (use : Use τ K J R) : Wiring (sig K J R) τ where
  toRight
    | .answer key outcome => some (use.answer key outcome)
    | .dispatch .. => none
  toLeft out := (use.submitted out).map fun (key, job) => .submit key job

/-- `sys` with the jobs actor beside it. -/
abbrev attach {τ : Signature} (sys : System τ) (config : Config R) (use : Use τ K J R) :
    System (joinSig (sig K J R) τ) :=
  (system config).join sys use.wiring

/-- What a pool of workers may do: give the result of an attempt that was dispatched, once,
whatever it is, or never. It remembers the attempts open. -/
def pool : Outside (sig K J R) (List (K × Nat)) where
  init := []
  allow opened x :=
    match x with
    | .result key attempt _ =>
      if (key, attempt) ∈ opened then some (opened.erase (key, attempt)) else none
    | .submit .. => none
  observe opened out :=
    match out with
    | .dispatch key attempt _ => (key, attempt) :: opened
    | .answer .. => opened

/-! A step stays within the slots, keeps keys apart and attempts within the cap. -/

theorem within_fail (config : Config R) {active : List (Active K J)} {a : Active K J}
    (outcome : Outcome R) (first : List (Eff K J R)) (h : Within config active) :
    Within config (fail config active a outcome first).1 := by
  unfold fail
  split
  · exact ⟨by simpa using h.1, by simpa using h.2⟩
  · exact ⟨Nat.le_trans (length_remove_le ..) h.1, nodup_remove _ h.2⟩

theorem within_step (config : Config R) {active : List (Active K J)} (msg : Jobs.Msg K J R)
    (h : Within config active) : Within config (step config active msg).1 := by
  cases msg with
  | submit key job =>
    simp only [step]
    split
    · exact h
    · split
      · exact h
      · next hnew hroom =>
        exact ⟨by simp only [List.length_cons]; omega, List.nodup_cons.mpr ⟨hnew, h.2⟩⟩
  | result key attempt r =>
    simp only [step]
    split
    · split
      · split
        · exact within_fail config _ _ h
        · exact ⟨Nat.le_trans (length_remove_le ..) h.1, nodup_remove _ h.2⟩
      · exact h
    · exact h
  | expire key =>
    simp only [step]
    split
    · split
      · exact within_fail config _ _ h
      · exact h
    · exact h
  | retry key =>
    simp only [step]
    split
    · split
      · exact ⟨by simpa using h.1, by simpa using h.2⟩
      · exact h
    · exact h

theorem attempts_fail (config : Config R) {active : List (Active K J)} {a : Active K J}
    (outcome : Outcome R) (first : List (Eff K J R)) (h : Attempts config active)
    (ha : a ∈ active) : Attempts config (fail config active a outcome first).1 := by
  unfold fail
  split
  · next hlt =>
    obtain ⟨h1, hcap, -⟩ := h a ha
    exact attempts_put h ⟨h1, hcap, fun _ => hlt⟩
  · exact attempts_remove _ h

theorem attempts_step (config : Config R) {active : List (Active K J)} (msg : Jobs.Msg K J R)
    (h : Attempts config active) : Attempts config (step config active msg).1 := by
  cases msg with
  | submit key job =>
    simp only [step]
    split
    · exact h
    · split
      · exact h
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact ⟨Nat.le_refl 1, Nat.le_max_left .., nofun⟩
        · exact h b hb
  | result key attempt r =>
    simp only [step]
    split
    · next a ha =>
      split
      · split
        · exact attempts_fail config _ _ h (entry_some ha).1
        · exact attempts_remove _ h
      · exact h
    · exact h
  | expire key =>
    simp only [step]
    split
    · next a ha =>
      split
      · exact attempts_fail config _ _ h (entry_some ha).1
      · exact h
    · exact h
  | retry key =>
    simp only [step]
    split
    · next a ha =>
      split
      · next hback =>
        obtain ⟨h1, -, hlt⟩ := h a (entry_some ha).1
        exact attempts_put h ⟨by simp, hlt hback, nofun⟩
      · exact h
    · exact h

theorem actor_within (config : Config R) :
    (actor (K := K) (J := J) config).Invariant (Within config) :=
  Actor.Inductive.invariant
    ⟨⟨by simp [actor], by simp [actor, keys]⟩, fun _ msg h => within_step config msg h,
      fun _ h => h⟩

theorem actor_attempts (config : Config R) :
    (actor (K := K) (J := J) config).Invariant (Attempts config) :=
  Actor.Inductive.invariant
    ⟨by simp [actor, Attempts], fun _ msg h => attempts_step config msg h, fun _ h => h⟩

/-! A retry carries the job it retries. -/

/-- The attempts a step dispatches: of a job that is active after it, on the attempt the job
is then making, with the job's own key and work. -/
theorem dispatch_active (config : Config R) {active : List (Active K J)} {msg : Jobs.Msg K J R}
    {key : K} {attempt : Nat} {job : J}
    (h : (.emit (.dispatch key attempt job) : Eff K J R) ∈ (step config active msg).2) :
    ∃ a ∈ (step config active msg).1, a.key = key ∧ a.job = job ∧ a.attempt = attempt ∧
      a.phase = .running := by
  have hfail {a : Active K J} {outcome : Outcome R} {first : List (Eff K J R)}
      (hfirst : (.emit (.dispatch key attempt job) : Eff K J R) ∉ first)
      (h : (.emit (.dispatch key attempt job) : Eff K J R) ∈ (fail config active a outcome first).2) :
      False := by
    unfold fail at h
    split at h <;> simp_all
  cases msg with
  | submit key' job' =>
    simp only [step] at h ⊢
    split at h
    · simp at h
    · next hnew =>
      split at h
      · simp at h
      · next hroom =>
        simp only [List.mem_cons, Effect.emit.injEq, Output.dispatch.injEq, reduceCtorEq,
          List.not_mem_nil, or_false] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        simp only [hnew, hroom, ↓reduceIte]
        exact ⟨_, List.mem_cons_self .., rfl, rfl, rfl, rfl⟩
  | result key' attempt' r =>
    simp only [step] at h
    split at h
    · split at h
      · split at h
        · exact (hfail (by simp) h).elim
        · simp at h
      · simp at h
    · simp at h
  | expire key' =>
    simp only [step] at h
    split at h
    · split at h
      · exact (hfail (by simp) h).elim
      · simp at h
    · simp at h
  | retry key' =>
    simp only [step] at h ⊢
    split at h
    · next a ha =>
      split at h
      · next hback =>
        simp only [List.mem_cons, Effect.emit.injEq, Output.dispatch.injEq, reduceCtorEq,
          List.not_mem_nil, or_false] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        obtain ⟨hmem, rfl⟩ := entry_some ha
        simp only [hback, ↓reduceIte]
        let a' : Active K J := { a with attempt := a.attempt + 1, phase := .running }
        exact ⟨a', (entry_some (entry_put_self (a := a') (mem_keys.mpr ⟨a, hmem, rfl⟩))).1,
          rfl, rfl, rfl, rfl⟩
      · simp at h
    · simp at h

/-- A retry carries the key and the work of the attempt before it: a step that dispatches
attempt `attempt + 1` of `key`, after a first, does so for the job that was active under `key`,
on attempt `attempt`. -/
theorem retry_same (config : Config R) {active : List (Active K J)} {msg : Jobs.Msg K J R}
    {key : K} {attempt : Nat} {job : J} (hretry : 0 < attempt)
    (h : (.emit (.dispatch key (attempt + 1) job) : Eff K J R) ∈ (step config active msg).2) :
    ∃ a, entry active key = some a ∧ a.job = job ∧ a.attempt = attempt := by
  have hfail {a : Active K J} {outcome : Outcome R} {first : List (Eff K J R)}
      (hfirst : (.emit (.dispatch key (attempt + 1) job) : Eff K J R) ∉ first)
      (h : (.emit (.dispatch key (attempt + 1) job) : Eff K J R) ∈
        (fail config active a outcome first).2) :
      False := by
    unfold fail at h
    split at h <;> simp_all
  cases msg with
  | submit key' job' =>
    simp only [step] at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · simp only [List.mem_cons, Effect.emit.injEq, Output.dispatch.injEq, reduceCtorEq,
          List.not_mem_nil, or_false] at h
        omega
  | result key' attempt' r =>
    simp only [step] at h
    split at h
    · split at h
      · split at h
        · exact (hfail (by simp) h).elim
        · simp at h
      · simp at h
    · simp at h
  | expire key' =>
    simp only [step] at h
    split at h
    · split at h
      · exact (hfail (by simp) h).elim
      · simp at h
    · simp at h
  | retry key' =>
    simp only [step] at h
    split at h
    · next a ha =>
      split at h
      · simp only [List.mem_cons, Effect.emit.injEq, Output.dispatch.injEq, reduceCtorEq,
          List.not_mem_nil, or_false] at h
        obtain ⟨rfl, hn, rfl⟩ := h
        exact ⟨a, ha, rfl, by omega⟩
      · simp at h
    · simp at h

end Lanes.Jobs
