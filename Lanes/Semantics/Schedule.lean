/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Behaviours.Schedule.Sound
public import Lanes.Semantics.FairJoin
public import Lanes.Semantics.Liveness

/-!
# Every job the scheduler holds comes to an end

In a fair run in which the scheduler does not crash, every job it holds that is not periodic
leaves it (`Schedule.held_leaves`), and the step in which it leaves emits its end: a success, a
dead letter, a cancellation or its notice (`Schedule.ends_of_leaves`), which is then handed over
(`Schedule.held_ends`). That step tells the requester once: one answer that ends the job, or the
notice of a job that runs once, and nothing else about it (`Schedule.told_of_leaves`). That holds
whatever the service does: it may answer an attempt late, wrongly, `unknown` or never. A periodic job is noticed again and again while it is held
(`Schedule.every_noticed`).

Fairness is the repository's (`System.Run.Fair`): a timer that stays armed and that no step arms
again fires. The measure is `Schedule.left`: two for each attempt a job has left, and one more
while an attempt is out. While a job is held its timer is armed (`Schedule.armed`), no step arms
it again (`Schedule.not_arms`), and firing it brings the job nearer its end
(`Schedule.entry_step_timer`); no other step takes it further away (`Schedule.entry_step`). So by
`System.LeadsTo.ensures_of_invariant` each value of the measure leads to a smaller one or to the
job's end, and by `System.LeadsTo.induction` the job ends.

The premise that the scheduler does not crash is the gate's and the jobs actor's
(`Lanes.Semantics.Front`, `Lanes.Semantics.Jobs`): a crash loses its timers, and a stopped actor
with no mail is not obliged to start again. A shard restarts its actors from the journal, and
the start arms every job's timer again (`Schedule.armed`); what is not proved is that a start
comes.

Beside a system (`Schedule.attach`) the end is a message to it, and fairness delivers it
(`System.Run.Fair.routed_right`) when the links to it lose nothing and its actors are not
crashed and never stop. A call job's end is then an answer, `succeeded`, `failed` or
`cancelled`: never `scheduled` or `already`, which answer a scheduling, and never a notice.

## Main statements

- `Schedule.held_leaves`: a job held that is not periodic stops being held.
- `Schedule.held_ends`: in a fair run, its end is handed over.
- `Schedule.every_noticed`: a periodic job held is noticed, or stops being held.
- `Schedule.attach_held_leaves`: the same beside any system.
- `Schedule.attach_end_handled`: beside any system, the end is handled by that system.
- `Schedule.attach_answer_handled`: beside any system, a call job's answer that ends it is
  handled by that system.
-/

@[expose] public section

namespace Lanes.Schedule

variable {K P A : Type} [DecidableEq K] [DecidableEq P] [DecidableEq A] {config : Config K P A}
  {env : EnvModel (sig K P A)}

/-! ### Steps, for one job -/

/-- A step leaves a job that is not periodic as it was, or moves it nearer its end. -/
theorem entry_step {s : State K P} (hatt : s.Attempts config) {key : K} {j : Job K P}
    (hj : entry s.jobs key = some j) (hp : j.work.periodic = false) (msg : Schedule.Msg K P A) :
    entry (step config s msg).1.jobs key = some j ∨
      Moved config j (entry (step config s msg).1.jobs key) := by
  have hheld : key ∈ keys s.jobs := mem_keys.mpr ⟨j, (entry_some hj).1, (entry_some hj).2⟩
  rcases step_key (config := config) hj msg with ⟨hsame, -⟩ | ⟨act, -, hstep⟩
  · exact .inl hsame
  · rw [hstep]
    simp only
    rw [entry_set_self hheld (onJob_key_of hj act)]
    exact onJob_moved (hatt j (entry_some hj).1) hp

/-- What a step leaves of the job under a key is the same job: same work and payload. -/
theorem entry_step_same {s : State K P} {key : K} {j j' : Job K P}
    (hj : entry s.jobs key = some j) {msg : Schedule.Msg K P A}
    (hj' : entry (step config s msg).1.jobs key = some j') : Same j j' := by
  have hheld : key ∈ keys s.jobs := mem_keys.mpr ⟨j, (entry_some hj).1, (entry_some hj).2⟩
  rcases step_key (config := config) hj msg with ⟨hsame, -⟩ | ⟨act, -, hstep⟩
  · rw [hsame] at hj'
    obtain rfl := Option.some.inj hj'
    exact ⟨rfl, rfl, rfl⟩
  · rw [hstep] at hj'
    simp only at hj'
    rw [entry_set_self hheld (onJob_key_of hj act)] at hj'
    exact onJob_same j' hj'

/-- Handling the timer a job that is not periodic waits on moves it nearer its end. -/
theorem entry_step_timer {s : State K P} (hatt : s.Attempts config) {key : K} {j : Job K P}
    (hj : entry s.jobs key = some j) (hp : j.work.periodic = false) :
    Moved config j (entry (step config s (timer j)).1.jobs key) := by
  have hheld : key ∈ keys s.jobs := mem_keys.mpr ⟨j, (entry_some hj).1, (entry_some hj).2⟩
  obtain ⟨act, htarget, hact⟩ := target_timer (A := A) j
  rw [(step_target (config := config) (s := s) htarget).1, (entry_some hj).2, touch_some act hj]
  simp only
  rw [entry_set_self hheld (onJob_key_of hj act)]
  exact onJob_moved_timer (hatt j (entry_some hj).1) hp hact

/-- No step arms again the timer a job held that is not periodic waits on. -/
theorem not_arms {s : State K P} {j : Job K P} (hj : entry s.jobs j.key = some j)
    (hp : j.work.periodic = false) (msg : Schedule.Msg K P A) (d : Nat) :
    (.after d (timer j) : Eff K P A) ∉ (step config s msg).2 := by
  have hheld : j.key ∈ keys s.jobs := mem_keys.mpr ⟨j, (entry_some hj).1, rfl⟩
  intro hd
  rcases step_cases (config := config) (s := s) msg with
    ⟨now_ms, spec, rfl⟩ | ⟨_, _, _, _, hs⟩ | ⟨key', act, j', rfl, hj', hs⟩
  · rw [step_schedule] at hd
    obtain ⟨-, ⟨-, o, he⟩ | ⟨hnew, -, -, he⟩⟩ := enroll_cases (config := config) (s := s) now_ms spec
    · simp [he] at hd
    · simp only [he, List.mem_cons, Effect.after.injEq, List.not_mem_nil, or_false,
        reduceCtorEq, false_or] at hd
      exact hnew (timer_key (.inl hd.2) ▸ hheld)
  · simp [hs] at hd
  · rw [hs] at hd
    by_cases hk : key' = j.key
    · subst hk
      obtain rfl : j' = j := Option.some.inj (hj'.symm.trans hj)
      exact onJob_not_arms hp d hd
    · obtain ⟨-, hkey'⟩ := entry_some hj'
      exact hk (hkey' ▸ (timer_key (onJob_ownTimers _ (.inr ⟨d, hd⟩))).symm)

/-- A job leaves only in a step that tells its requester: an answer to its id, or its notice. -/
theorem ends_of_leaves {s : State K P} {key : K} {j : Job K P} (hj : entry s.jobs key = some j)
    {msg : Schedule.Msg K P A} (hgone : entry (step config s msg).1.jobs key = none) :
    (∃ o, (.emit (.answer key o) : Eff K P A) ∈ (step config s msg).2) ∨
      ∃ n, (.emit (.notice key j.payload n) : Eff K P A) ∈ (step config s msg).2 := by
  have hheld : key ∈ keys s.jobs := mem_keys.mpr ⟨j, (entry_some hj).1, (entry_some hj).2⟩
  rcases step_key (config := config) hj msg with ⟨hsame, -⟩ | ⟨act, -, hstep⟩
  · rw [hsame] at hgone
    exact absurd hgone (Option.some_ne_none j)
  · rw [hstep] at hgone ⊢
    simp only at hgone ⊢
    rw [entry_set_self hheld (onJob_key_of hj act)] at hgone
    obtain ⟨-, rfl⟩ := entry_some hj
    exact onJob_ends hgone

/-! ### Runs -/

/-- A scheduler that the environment does not crash stays up. -/
theorem stays_up (hcrash : env.mayCrash () = false)
    {c c' : SysState (system (K := K) (P := P) config)} {ev : Event (sig K P A)}
    (hup : c.up () = true) (hstep : c.step env ev = some c') : c'.up () = true :=
  SysState.up_of_step hcrash (fun s msg => step_runs config s msg) hup hstep

/-- A step leaves the scheduler's state as it is, or takes it by one step of the actor. -/
theorem state_step {c c' : SysState (system (K := K) (P := P) config)} {ev : Event (sig K P A)}
    (hstep : c.step env ev = some c') :
    c'.state () = c.state () ∨ ∃ msg, c'.state () = (step config (c.state ()) msg).1 := by
  rcases SysState.step_state hstep with h | ⟨i, msg, h⟩ | ⟨i, h⟩
  · exact .inl (by rw [h])
  · exact .inr ⟨msg, by rw [h]; rfl⟩
  · exact .inl (by rw [h]; rfl)

/-- The job under `key` is gone, or is the same job as `j`, nearer its end. -/
def Nearer (config : Config K P A) (key : K) (j : Job K P)
    (c : SysState (system (K := K) (P := P) config)) : Prop :=
  key ∉ keys (c.state ()).jobs ∨ (c.up () = true ∧
    ∃ j', entry (c.state ()).jobs key = some j' ∧ left config j' < left config j ∧ Same j j')

private theorem moved_nearer {c : SysState (system (K := K) (P := P) config)} {key : K}
    {j : Job K P} (hup : c.up () = true) (h : Moved config j (entry (c.state ()).jobs key))
    (hsame : ∀ j', entry (c.state ()).jobs key = some j' → Same j j') : Nearer config key j c := by
  rcases h with h | ⟨j', h, hlt⟩
  · exact .inl (entry_eq_none.mp h)
  · exact .inr ⟨hup, j', h, hlt, hsame j' h⟩

/-- A job held that is not periodic is, in a fair run, no longer held or nearer its end. -/
theorem entry_leads (config : Config K P A) (hcrash : env.mayCrash () = false) (key : K)
    (j : Job K P) (hp : j.work.periodic = false) :
    (system (K := K) (P := P) config).LeadsTo env
      (fun c => c.up () = true ∧ entry (c.state ()).jobs key = some j)
      (Nearer config key j) := by
  refine System.LeadsTo.ensures_of_invariant
    (I := fun c => Armed c ∧ (c.state ()).Attempts config) ?_ (.timeout () (timer j)) ?_ ?_ ?_ ?_
  · exact fun c hc => ⟨armed config env c hc, attempts config env c hc⟩
  · intro c ev c' ⟨_, hatt⟩ ⟨hup, hj⟩ _ hstep
    have hup' := stays_up hcrash hup hstep
    rcases state_step hstep with hs | ⟨msg, hs⟩
    · exact .inl ⟨hup', hs ▸ hj⟩
    · rcases entry_step hatt hj hp msg with he | hmoved
      · exact .inl ⟨hup', hs ▸ he⟩
      · exact .inr (moved_nearer hup' (hs ▸ hmoved) fun j' h => entry_step_same hj (hs ▸ h))
  · exact fun c ⟨harmed, _⟩ ⟨hup, hj⟩ _ => ⟨hup, harmed hup j (entry_some hj).1⟩
  · intro c c' ⟨_, hatt⟩ ⟨hup, hj⟩ _ hstep
    have hup' := stays_up hcrash hup hstep
    obtain ⟨_, _, rfl⟩ := SysState.step_timeout.mp hstep
    refine moved_nearer hup' ?_ fun j' h => ?_
    · rw [handle_eq]
      simp only [update_self]
      exact entry_step_timer hatt hj hp
    · rw [handle_eq] at h
      simp only [update_self] at h
      exact entry_step_same hj h
  · intro c ev c' _ ⟨hup, hj⟩ _ hstep hrestarted
    exfalso
    obtain ⟨-, rfl⟩ := entry_some hj
    have hnot (msg : Schedule.Msg K P A) :
        Event.timeout (σ := sig K P A) () (timer j) ∉
          Effect.timeouts () (step config (c.state ()) msg).2 :=
      fun h => by
        obtain ⟨d, hd⟩ := Effect.mem_timeouts.mp h
        exact not_arms hj hp msg d hd
    cases ev with
    | deliver e | duplicate e => exact hnot e.msg hrestarted
    | timeout i msg => exact hnot msg hrestarted
    | start i =>
      obtain ⟨hdown, -⟩ := SysState.step_start.mp hstep
      simp [hup] at hdown
    | input _ | drop _ | output _ | crash _ => exact List.not_mem_nil hrestarted

/-- A job held that is not periodic stops being held, whatever the service does, in any
environment that does not crash the scheduler. -/
theorem held_leaves (config : Config K P A) (hcrash : env.mayCrash () = false) (key : K) :
    (system (K := K) (P := P) config).LeadsTo env
      (fun c => c.up () = true ∧ ∃ j, entry (c.state ()).jobs key = some j ∧
        j.work.periodic = false)
      (fun c => key ∉ keys (c.state ()).jobs) := by
  let f (c : SysState (system (K := K) (P := P) config)) : Nat :=
    match entry (c.state ()).jobs key with
    | some j => left config j
    | none => 0
  refine System.LeadsTo.induction f fun n => ?_
  refine System.LeadsTo.mono
    (P := fun (c : SysState (system (K := K) (P := P) config)) => ∃ j : Job K P, ((c.up () = true ∧ entry (c.state ()).jobs key = some j)
      ∧ j.work.periodic = false) ∧ left config j = n) ?_ (fun _ h => h) ?_
  · intro c ⟨⟨hup, j, hj, hp⟩, hf⟩
    exact ⟨j, ⟨⟨hup, hj⟩, hp⟩, by simpa [f, hj] using hf⟩
  refine System.LeadsTo.exists_left fun j => ?_
  by_cases hp : j.work.periodic = false
  · by_cases hn : left config j = n
    · refine System.LeadsTo.mono (fun c h => h.1.1) (fun c hQ => ?_)
        (entry_leads config hcrash key j hp)
      rcases hQ with hgone | ⟨hup, j', hj', hlt, hsame⟩
      · exact .inl hgone
      · refine .inr ⟨⟨hup, j', hj', hsame.2.1 ▸ hp⟩, ?_⟩
        simp only [f, hj']
        omega
    · exact System.LeadsTo.of_imp fun c h => absurd h.2 hn
  · exact System.LeadsTo.of_imp fun c h => absurd h.1.2 hp

/-- A job stops being held only in a step that emits its end. -/
theorem ends_of_step {c c' : SysState (system (K := K) (P := P) config)}
    {ev : Event (sig K P A)} (hstep : c.step env ev = some c') {key : K} {j : Job K P}
    (hj : entry (c.state ()).jobs key = some j) (hout : key ∉ keys (c'.state ()).jobs) :
    (∃ o, Output.answer key o ∈ c'.outbox) ∨ ∃ n, Output.notice key j.payload n ∈ c'.outbox := by
  have hin : key ∈ keys (c.state ()).jobs :=
    mem_keys.mpr ⟨j, (entry_some hj).1, (entry_some hj).2⟩
  have hhandle (c₀ : SysState (system (K := K) (P := P) config)) (hs : c₀.state = c.state)
      (i : Unit) (msg : Schedule.Msg K P A)
      (hgone : key ∉ keys ((c₀.handle env i msg).state ()).jobs) :
      (∃ o, Output.answer key o ∈ (c₀.handle env i msg).outbox) ∨
        ∃ n, Output.notice key j.payload n ∈ (c₀.handle env i msg).outbox := by
    obtain rfl : i = () := rfl
    rw [handle_eq] at hgone ⊢
    simp only [update_self] at hgone
    rw [hs] at hgone ⊢
    rcases ends_of_leaves (config := config) hj (entry_eq_none.mpr hgone) with ⟨o, ho⟩ | ho
    · exact .inl ⟨o, List.mem_append_right _ (Effect.mem_emits.mpr ho)⟩
    · obtain ⟨n, ho⟩ := ho
      exact .inr ⟨n, List.mem_append_right _ (Effect.mem_emits.mpr ho)⟩
  cases ev with
  | input x =>
    obtain rfl := SysState.step_input.mp hstep
    exact absurd hin hout
  | deliver e =>
    obtain ⟨_, _, rfl⟩ := SysState.step_deliver.mp hstep
    exact hhandle { c with net := c.net.erase e } rfl e.dst e.msg hout
  | duplicate e =>
    obtain ⟨_, _, _, rfl⟩ := SysState.step_duplicate.mp hstep
    exact hhandle _ rfl e.dst e.msg hout
  | drop e =>
    obtain ⟨_, _, rfl⟩ := SysState.step_drop.mp hstep
    exact absurd hin hout
  | timeout i msg =>
    obtain ⟨_, _, rfl⟩ := SysState.step_timeout.mp hstep
    exact hhandle { c with timers := update c.timers i ((c.timers i).erase msg) } rfl i msg hout
  | output out =>
    obtain ⟨_, rfl⟩ := SysState.step_output.mp hstep
    exact absurd hin hout
  | crash i =>
    obtain ⟨_, _, rfl⟩ := SysState.step_crash.mp hstep
    exact absurd hin hout
  | start i =>
    obtain ⟨_, _, rfl⟩ := SysState.step_start.mp hstep
    rw [startActor_eq] at hout
    exact absurd hin hout

/-- Every job the scheduler holds that is not periodic comes to an end: in a fair run in which
the scheduler is not crashed, a job held while it is up has its end handed over at a later
position, as an answer to its id (a success, a dead letter, a cancellation) or as its notice. -/
theorem held_ends (config : Config K P A) (hcrash : env.mayCrash () = false) (key : K)
    {r : (system (K := K) (P := P) config).Run env} (hfair : r.Fair) {n : Nat}
    (hup : (r.state n).up () = true) {j : Job K P}
    (hj : entry ((r.state n).state ()).jobs key = some j) (hp : j.work.periodic = false) :
    ∃ m, n ≤ m ∧ ((∃ o, r.event m = some (.output (.answer key o))) ∨
      ∃ p n, r.event m = some (.output (.notice key p n))) := by
  obtain ⟨m, hm, hgone⟩ := System.LeadsTo.iff.mp (held_leaves config hcrash key)
    r hfair n ⟨hup, j, hj, hp⟩
  have hin : key ∈ keys ((r.state n).state ()).jobs :=
    mem_keys.mpr ⟨j, (entry_some hj).1, (entry_some hj).2⟩
  have hleaves : ∃ k, n ≤ k ∧ key ∈ keys ((r.state k).state ()).jobs ∧
      key ∉ keys ((r.state (k + 1)).state ()).jobs := by
    induction m, hm using le_induction with
    | base => exact absurd hin hgone
    | succ m hm ih =>
      by_cases hin' : key ∈ keys ((r.state m).state ()).jobs
      · exact ⟨m, hm, hin', hgone⟩
      · exact ih hin'
  obtain ⟨k, hk, hin', hout⟩ := hleaves
  obtain ⟨j', hj'⟩ := Option.ne_none_iff_exists'.mp ((not_congr entry_eq_none).mpr (Classical.not_not.mpr hin'))
  cases hev : r.event k with
  | none => exact absurd (System.Run.step_none hev ▸ hin') hout
  | some ev =>
    rcases ends_of_step (System.Run.step_some hev) hj' hout with ⟨o, ho⟩ | ho
    · obtain ⟨m', hm', htaken⟩ := hfair.output_taken (n := k + 1) ho
      exact ⟨m', by omega, .inl ⟨o, htaken⟩⟩
    · obtain ⟨t, ho⟩ := ho
      obtain ⟨m', hm', htaken⟩ := hfair.output_taken (n := k + 1) ho
      exact ⟨m', by omega, .inr ⟨_, _, htaken⟩⟩

/-- A step leaves a periodic job waiting as it was, without arming its timer again, or ends it,
or emits its notice. -/
theorem every_step {s : State K P} {key : K} {j : Job K P} (hj : entry s.jobs key = some j)
    {period_ms : Nat} (hwork : j.work = .every period_ms) (hwait : j.phase = .waiting)
    (msg : Schedule.Msg K P A) :
    (entry (step config s msg).1.jobs key = some j ∧
        ∀ d, (.after d (timer j) : Eff K P A) ∉ (step config s msg).2) ∨
      entry (step config s msg).1.jobs key = none ∨
      ∃ n, (.emit (.notice key j.payload n) : Eff K P A) ∈ (step config s msg).2 := by
  have hheld : key ∈ keys s.jobs := mem_keys.mpr ⟨j, (entry_some hj).1, (entry_some hj).2⟩
  obtain ⟨-, hkey⟩ := entry_some hj
  have hother {key' : K} (hk : key' ≠ key) {effs : List (Eff K P A)} (hown : OwnTimers key' effs) :
      ∀ d, (.after d (timer j) : Eff K P A) ∉ effs := fun d hd =>
    hk (hkey ▸ (timer_key (hown _ (.inr ⟨d, hd⟩))).symm)
  rcases step_cases (config := config) (s := s) msg with
    ⟨now_ms, spec, rfl⟩ | ⟨key', act, rfl, hnone, hs⟩ | ⟨key', act, j', rfl, hj', hs⟩
  · refine .inl ⟨?_, fun d hd => ?_⟩
    · rcases step_key (config := config) hj (.schedule now_ms spec) with ⟨h, -⟩ | ⟨act, h, -⟩
      · exact h
      · cases act <;> simp [Act.msg] at h
    · rw [step_schedule] at hd
      obtain ⟨-, ⟨-, o, he⟩ | ⟨hnew, -, -, he⟩⟩ :=
        enroll_cases (config := config) (s := s) now_ms spec
      · simp [he] at hd
      · simp only [he, List.mem_cons, Effect.after.injEq, List.not_mem_nil, or_false,
          reduceCtorEq, false_or] at hd
        exact hnew (by rw [← timer_key (.inl hd.2), hkey]; exact hheld)
  · rw [hs]
    exact .inl ⟨hj, by simp⟩
  · rw [hs]
    simp only
    by_cases hk : key' = key
    · subst hk
      obtain rfl : j' = j := Option.some.inj (hj'.symm.trans hj)
      rw [entry_set_self hheld (onJob_key_of hj act), ← hkey]
      cases act with
      | cancel => exact .inr (.inl (by simp [onJob, hwait]))
      | reply attempt r => exact .inl ⟨by simp [onJob, hwait], by simp [onJob, hwait]⟩
      | expire => exact .inl ⟨by simp [onJob, hwait], by simp [onJob, hwait]⟩
      | due => exact .inr (.inr (by simp [onJob, hwait, run, hwork]))
    · rw [entry_set_of_ne (Ne.symm hk) (onJob_key_of hj' act)]
      obtain ⟨-, hkey'⟩ := entry_some hj'
      exact .inl ⟨hj, hother hk (hkey' ▸ onJob_ownTimers)⟩

/-- A step from a state in which a periodic job waits keeps it so, ends it or emits its notice;
and one that arms its timer again does one of the last two. -/
private theorem every_event {c c' : SysState (system (K := K) (P := P) config)}
    {ev : Event (sig K P A)} (hstep : c.step env ev = some c') (hup : c.up () = true)
    {key : K} {j : Job K P} (hj : entry (c.state ()).jobs key = some j) {period_ms : Nat}
    (hwork : j.work = .every period_ms) (hwait : j.phase = .waiting) :
    (key ∉ keys (c'.state ()).jobs ∨ ∃ p n, Output.notice key p n ∈ c'.outbox) ∨
      (entry (c'.state ()).jobs key = some j ∧ .timeout () (timer j) ∉ c.arms ev) := by
  have hhandle (c₀ : SysState (system (K := K) (P := P) config)) (hs : c₀.state = c.state)
      (msg : Schedule.Msg K P A) :
      (key ∉ keys ((c₀.handle env () msg).state ()).jobs ∨
          ∃ p n, Output.notice key p n ∈ (c₀.handle env () msg).outbox) ∨
        (entry ((c₀.handle env () msg).state ()).jobs key = some j ∧
          Event.timeout (σ := sig K P A) () (timer j) ∉
            Effect.timeouts () (step config (c.state ()) msg).2) := by
    rw [handle_eq]
    simp only [update_self]
    rw [hs]
    rcases every_step (config := config) hj hwork hwait msg with ⟨he, hnot⟩ | hgone | hnotice
    · refine .inr ⟨he, fun h => ?_⟩
      obtain ⟨d, hd⟩ := Effect.mem_timeouts.mp h
      exact hnot d hd
    · exact .inl (.inl (entry_eq_none.mp hgone))
    · obtain ⟨n, hnotice⟩ := hnotice
      exact .inl (.inr ⟨_, n, List.mem_append_right _ (Effect.mem_emits.mpr hnotice)⟩)
  cases ev with
  | input x =>
    obtain rfl := SysState.step_input.mp hstep
    exact .inr ⟨hj, List.not_mem_nil⟩
  | deliver e =>
    obtain ⟨_, _, rfl⟩ := SysState.step_deliver.mp hstep
    exact hhandle { c with net := c.net.erase e } rfl e.msg
  | duplicate e =>
    obtain ⟨_, _, _, rfl⟩ := SysState.step_duplicate.mp hstep
    exact hhandle c rfl e.msg
  | drop e =>
    obtain ⟨_, _, rfl⟩ := SysState.step_drop.mp hstep
    exact .inr ⟨hj, List.not_mem_nil⟩
  | timeout i msg =>
    obtain ⟨_, _, rfl⟩ := SysState.step_timeout.mp hstep
    exact hhandle { c with timers := update c.timers i ((c.timers i).erase msg) } rfl msg
  | output out =>
    obtain ⟨_, rfl⟩ := SysState.step_output.mp hstep
    exact .inr ⟨hj, List.not_mem_nil⟩
  | crash i =>
    obtain ⟨_, _, rfl⟩ := SysState.step_crash.mp hstep
    exact .inr ⟨hj, List.not_mem_nil⟩
  | start i =>
    obtain ⟨hdown, -⟩ := SysState.step_start.mp hstep
    simp [hup] at hdown

/-- A periodic job held is, in a fair run in which the scheduler is not crashed, noticed, or no
longer held. Each notice it gives is handed over in turn (`System.Run.Fair.output_taken`), so
while it is held it is noticed again and again. -/
theorem every_noticed (config : Config K P A) (hcrash : env.mayCrash () = false) (key : K)
    (j : Job K P) {period_ms : Nat} (hwork : j.work = .every period_ms)
    (hwait : j.phase = .waiting) :
    (system (K := K) (P := P) config).LeadsTo env
      (fun c => c.up () = true ∧ entry (c.state ()).jobs key = some j)
      (fun c => key ∉ keys (c.state ()).jobs ∨ ∃ p n, Output.notice key p n ∈ c.outbox) := by
  refine System.LeadsTo.ensures_of_invariant (I := fun c => Armed c) ?_
    (.timeout () (timer j)) ?_ ?_ ?_ ?_
  · exact fun c hc => armed config env c hc
  · intro c ev c' _ ⟨hup, hj⟩ _ hstep
    rcases every_event hstep hup hj hwork hwait with hQ | ⟨he, -⟩
    · exact .inr hQ
    · exact .inl ⟨stays_up hcrash hup hstep, he⟩
  · exact fun c harmed ⟨hup, hj⟩ _ => ⟨hup, harmed hup j (entry_some hj).1⟩
  · intro c c' _ ⟨hup, hj⟩ _ hstep
    obtain ⟨_, _, rfl⟩ := SysState.step_timeout.mp hstep
    refine .inr ⟨j.payload, max (c.state ()).now_ms j.at_ms, ?_⟩
    rw [handle_eq]
    refine List.mem_append_right _ (Effect.mem_emits.mpr ?_)
    obtain ⟨-, rfl⟩ := entry_some hj
    simp [timer, hwait, step, touch_some _ hj, onJob, run, hwork]
  · intro c ev c' _ ⟨hup, hj⟩ _ hstep hrestarted
    rcases every_event hstep hup hj hwork hwait with hQ | ⟨-, hnot⟩
    · exact hQ
    · exact absurd hrestarted hnot

/-- Beside any system, every job held that is not periodic stops being held, in any environment
that does not crash the scheduler: what it does alone, it does in `attach sys`. -/
theorem attach_held_leaves {τ : Signature} (sys : System τ) (config : Config K P A)
    (use : Use τ K P A) {env : EnvModel (joinSig (sig K P A) τ)}
    (hcrash : env.mayCrash (.inl ()) = false) (key : K) :
    (attach sys config use).LeadsTo env
      (fun c => c.up (.inl ()) = true ∧ ∃ j, entry (c.state (.inl ()) : State K P).jobs key = some j ∧
        j.work.periodic = false)
      (fun c => key ∉ keys (c.state (.inl ()) : State K P).jobs) :=
  System.LeadsTo.join_left
    (P := fun c : SysState (system (K := K) (P := P) config) =>
      c.up () = true ∧ ∃ j, entry (c.state ()).jobs key = some j ∧ j.work.periodic = false)
    (Q := fun s _ => key ∉ keys (s ()).jobs) (held_leaves config (env := env.left) hcrash key)

/-- Beside any system, the job held under `key` at position `n` is the same job at `k`: the
same work and payload. Or it left at a position between, where it was still that job. -/
theorem attach_held_same {τ : Signature} {sys : System τ} {use : Use τ K P A}
    {env : EnvModel (joinSig (sig K P A) τ)} {r : (attach sys config use).Run env} {n : Nat}
    {key : K} {j : Job K P} (hj : entry ((r.state n).state (.inl ()) : State K P).jobs key = some j)
    (k : Nat) (hk : n ≤ k) :
    (∃ j', entry ((r.state k).state (.inl ()) : State K P).jobs key = some j' ∧ Same j j') ∨
      ∃ i j', n ≤ i ∧ i < k ∧ entry ((r.state i).state (.inl ()) : State K P).jobs key = some j' ∧
        Same j j' ∧ key ∉ keys ((r.state (i + 1)).state (.inl ()) : State K P).jobs := by
  induction k, hk using le_induction with
  | base => exact .inl ⟨j, hj, rfl, rfl, rfl⟩
  | succ k hk ih =>
    rcases ih with ⟨j', hj', hsame⟩ | ⟨i, j', hi, hik, hj', hsame, hout⟩
    · have hnext : ((r.state (k + 1)).state (.inl ()) : State K P) = (r.state k).state (.inl ()) ∨
          ∃ msg, ((r.state (k + 1)).state (.inl ()) : State K P) =
            (step config ((r.state k).state (.inl ())) msg).1 := by
        cases hev : r.event k with
        | none => exact .inl (by rw [System.Run.step_none hev])
        | some ev =>
          rcases SysState.step_left_state (System.Run.step_some hev) () with
            hs | ⟨msg, -, hs⟩ | ⟨-, hs⟩
          · exact .inl hs
          · exact .inr ⟨msg, hs⟩
          · exact .inl hs
      cases he : entry ((r.state (k + 1)).state (.inl ()) : State K P).jobs key with
      | none => exact .inr ⟨k, j', hk, by omega, hj', hsame, entry_eq_none.mp he⟩
      | some j'' =>
        refine .inl ⟨j'', rfl, ?_⟩
        rcases hnext with hs | ⟨msg, hs⟩
        · rw [hs, hj'] at he
          cases he
          exact hsame
        · rw [hs] at he
          obtain ⟨h1, h2, h3⟩ := entry_step_same hj' he
          exact ⟨h1.trans hsame.1, h2.trans hsame.2.1, h3.trans hsame.2.2⟩
    · exact .inr ⟨i, j', hi, by omega, hj', hsame, hout⟩

/-- Beside any system, the end of every job held that is not periodic is handled by that system:
in a fair run in which the scheduler is not crashed, a job held while it is up has its end
delivered, at a later position, to the actor of `sys` that takes it. The end is an answer that
ends the job (`succeeded`, `failed` or `cancelled`), or, for a job that runs once, its notice.
The links from the scheduler to `sys` must lose nothing, and the actors of `sys` must not be
crashed and never stop: a loss, a crash or a stop can take the end out of flight. -/
theorem attach_end_handled {τ : Signature} (sys : System τ) (config : Config K P A)
    (use : Use τ K P A) {env : EnvModel (joinSig (sig K P A) τ)}
    (hcrash : env.mayCrash (.inl ()) = false)
    (hlossless : ∀ j, (env.link (some (.inl ())) (.inr j)).lossy = false)
    (hcrashes : ∀ j, env.mayCrash (.inr j) = false)
    (hruns : ∀ j s msg, ((sys.actor j).step s msg).2.any Effect.isStop = false)
    (hrecovers : ∀ j s, ((sys.actor j).recover s).2.any Effect.isStop = false) (key : K)
    {r : (attach sys config use).Run env} (hfair : r.Fair) {n : Nat}
    (hup : (r.state n).up (.inl ()) = true) {j : Job K P}
    (hj : entry ((r.state n).state (.inl ()) : State K P).jobs key = some j)
    (hp : j.work.periodic = false) :
    ∃ m x, n ≤ m ∧
      ((∃ o, o.isEnd = true ∧ x = use.answer key o) ∨
        (j.work = .once ∧ ∃ t, x = use.notice key j.payload t)) ∧
      (r.event m = some (.deliver ⟨some (.inl ()), .inr (sys.accept x).1, (sys.accept x).2⟩) ∨
        r.event m =
          some (.duplicate ⟨some (.inl ()), .inr (sys.accept x).1, (sys.accept x).2⟩)) := by
  obtain ⟨m, hm, hgone⟩ := System.LeadsTo.iff.mp (attach_held_leaves sys config use hcrash key)
    r hfair n ⟨hup, j, hj, hp⟩
  rcases attach_held_same hj m hm with ⟨j', hj', -⟩ | ⟨k, j', hk, -, hj', hsame, hout⟩
  · exact absurd (mem_keys.mpr ⟨j', (entry_some hj').1, (entry_some hj').2⟩) hgone
  have hin' : key ∈ keys ((r.state k).state (.inl ()) : State K P).jobs :=
    mem_keys.mpr ⟨j', (entry_some hj').1, (entry_some hj').2⟩
  cases hev : r.event k with
  | none => exact absurd (System.Run.step_none hev ▸ hin') hout
  | some ev =>
    rcases SysState.step_left_state (System.Run.step_some hev) () with
      hs | ⟨msg, hdeed, hs⟩ | ⟨-, hs⟩
    · exact absurd (hs ▸ hin') hout
    · have hmem {out : Output K P A}
          (h : (Effect.emits (step config ((r.state k).state (.inl ())) msg).2).filter
            (tells key) = [out]) :
          (.emit out : Eff K P A) ∈ (step config ((r.state k).state (.inl ())) msg).2 :=
        Effect.mem_emits.mp ((List.mem_filter.mp (by rw [h]; exact List.mem_singleton_self out)).1)
      obtain ⟨out, x, hemit, hx, hend⟩ : ∃ out x, (.emit out : Eff K P A) ∈
          (step config ((r.state k).state (.inl ())) msg).2 ∧ use.wiring.toRight out = some x ∧
          ((∃ o, o.isEnd = true ∧ x = use.answer key o) ∨
            (j.work = .once ∧ ∃ t, x = use.notice key j.payload t)) := by
        rcases told_of_leaves (config := config) hj' (entry_eq_none.mpr (hs ▸ hout)) with
          ⟨o, hend, ho⟩ | ⟨honce, t, ho⟩
        · exact ⟨_, _, hmem ho, rfl, .inl ⟨o, hend, rfl⟩⟩
        · exact ⟨_, _, hmem ho, rfl, .inr ⟨hsame.2.1.symm.trans honce, t, by rw [hsame.2.2]⟩⟩
      obtain ⟨m, hm, h⟩ := hfair.routed_right hev hdeed hemit hx (hlossless _) (hcrashes _)
        (hruns _) (hrecovers _)
      exact ⟨m, x, by omega, hend, h⟩
    · exact absurd (hs ▸ hin') hout

/-- Beside any system, every call job held is answered: in a fair run in which the scheduler is
not crashed, a call job held while it is up has an answer that ends it (`succeeded`, `failed` or
`cancelled`) delivered, at a later position, to the actor of `sys` that takes it. The premises
are those of `attach_end_handled`. -/
theorem attach_answer_handled {τ : Signature} (sys : System τ) (config : Config K P A)
    (use : Use τ K P A) {env : EnvModel (joinSig (sig K P A) τ)}
    (hcrash : env.mayCrash (.inl ()) = false)
    (hlossless : ∀ j, (env.link (some (.inl ())) (.inr j)).lossy = false)
    (hcrashes : ∀ j, env.mayCrash (.inr j) = false)
    (hruns : ∀ j s msg, ((sys.actor j).step s msg).2.any Effect.isStop = false)
    (hrecovers : ∀ j s, ((sys.actor j).recover s).2.any Effect.isStop = false) (key : K)
    {r : (attach sys config use).Run env} (hfair : r.Fair) {n : Nat}
    (hup : (r.state n).up (.inl ()) = true) {j : Job K P}
    (hj : entry ((r.state n).state (.inl ()) : State K P).jobs key = some j) {retry : Retry}
    (hwork : j.work = .call retry) :
    ∃ m o, n ≤ m ∧ o.isEnd = true ∧
      (r.event m = some (.deliver ⟨some (.inl ()), .inr (sys.accept (use.answer key o)).1,
          (sys.accept (use.answer key o)).2⟩) ∨
        r.event m = some (.duplicate ⟨some (.inl ()), .inr (sys.accept (use.answer key o)).1,
          (sys.accept (use.answer key o)).2⟩)) := by
  obtain ⟨m, x, hm, ⟨o, hend, rfl⟩ | ⟨honce, -⟩, h⟩ :=
    attach_end_handled sys config use hcrash hlossless hcrashes hruns hrecovers key hfair hup hj
      (by simp [hwork, Work.periodic])
  · exact ⟨m, o, hm, hend, h⟩
  · rw [hwork] at honce
    cases honce

end Lanes.Schedule
