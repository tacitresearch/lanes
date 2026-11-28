/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Behaviours.Jobs.Sound
public import Lanes.Semantics.FairJoin
public import Lanes.Semantics.Liveness

/-!
# The jobs actor answers every job it admits

In a fair run in which the jobs actor does not crash, every job it admits is answered, and so is
every submission it handles (`Jobs.submitted_answered`), whatever the workers do: they may answer
an attempt late, wrongly, or never. The measure is `Jobs.left`: two for each attempt a job has
left, and one more while an attempt is made. While a job is active, the timer it waits on is
armed (`Jobs.armed`), no step arms it again (`Jobs.not_arms`), and handling it brings the job
nearer its answer (`Jobs.entry_step_timer`); no other step takes it further away
(`Jobs.entry_step`). So by `System.LeadsTo.ensures_of_invariant` each value of the measure leads
to a smaller one or to the job's answer, and by `System.LeadsTo.induction` the job is answered.

The actor must not crash, for the reason the gate must not (`Lanes.Semantics.Front`): a
crashed actor with no mail need never start again.

## Main statements

- `Jobs.active_leaves`: an active job stops being active.
- `Jobs.active_answered`: in a fair run, an active job has its answer handed over.
- `Jobs.submitted_answered`: in a fair run, a submission the actor handles has an answer to its
  key handed over.
- `Jobs.attach_active_leaves`: beside any system, an active job stops being active.
-/

@[expose] public section

namespace Lanes.Jobs

variable {K J R : Type} [DecidableEq K] [DecidableEq J] [DecidableEq R] {config : Config R}
  {env : EnvModel (sig K J R)}

/-- A jobs actor that the environment does not crash stays up. -/
theorem stays_up (hcrash : env.mayCrash () = false)
    {c c' : SysState (system (K := K) (J := J) config)} {ev : Event (sig K J R)}
    (hup : c.up () = true) (hstep : c.step env ev = some c') : c'.up () = true :=
  SysState.up_of_step hcrash (fun s msg => step_runs config s msg) hup hstep

/-- A step leaves the active jobs as they are, or takes them by one step of the actor. -/
theorem state_step {c c' : SysState (system (K := K) (J := J) config)} {ev : Event (sig K J R)}
    (hstep : c.step env ev = some c') :
    c'.state () = c.state () ∨ ∃ msg, c'.state () = (step config (c.state ()) msg).1 := by
  rcases SysState.step_state hstep with h | ⟨i, msg, h⟩ | ⟨i, h⟩
  · exact .inl (by rw [h])
  · exact .inr ⟨msg, by rw [h]; rfl⟩
  · exact .inl (by rw [h]; rfl)

private theorem moved_leads {c : SysState (system (K := K) (J := J) config)} {key : K}
    {a : Active K J} (hup : c.up () = true) (h : Moved config a (entry (c.state ()) key)) :
    key ∉ keys (c.state ()) ∨
      (c.up () = true ∧ ∃ a', entry (c.state ()) key = some a' ∧ left config a' < left config a) := by
  rcases h with h | ⟨a', h, hlt⟩
  · exact .inl (entry_eq_none.mp h)
  · exact .inr ⟨hup, a', h, hlt⟩

/-- An active job is, in a fair run, no longer active or nearer its answer. -/
theorem entry_leads (config : Config R) (hcrash : env.mayCrash () = false) (key : K)
    (a : Active K J) :
    (system (K := K) (J := J) config).LeadsTo env
      (fun c => c.up () = true ∧ entry (c.state ()) key = some a)
      (fun c => key ∉ keys (c.state ()) ∨ (c.up () = true ∧
        ∃ a', entry (c.state ()) key = some a' ∧ left config a' < left config a)) := by
  refine System.LeadsTo.ensures_of_invariant
    (I := fun c => Armed c ∧ Attempts config (c.state ())) ?_ (.timeout () (timer a)) ?_ ?_ ?_ ?_
  · exact fun c hc => ⟨armed config env c hc, attempts config env c hc⟩
  · intro c ev c' ⟨_, hatt⟩ ⟨hup, ha⟩ _ hstep
    have hup' := stays_up hcrash hup hstep
    rcases state_step hstep with hs | ⟨msg, hs⟩
    · exact .inl ⟨hup', hs ▸ ha⟩
    · rcases entry_step config hatt ha msg with he | hmoved
      · exact .inl ⟨hup', hs ▸ he⟩
      · exact .inr (moved_leads hup' (hs ▸ hmoved))
  · exact fun c ⟨harmed, _⟩ ⟨hup, ha⟩ _ => ⟨hup, harmed hup a (entry_some ha).1⟩
  · intro c c' ⟨_, hatt⟩ ⟨hup, ha⟩ _ hstep
    have hup' := stays_up hcrash hup hstep
    obtain ⟨_, _, rfl⟩ := SysState.step_timeout.mp hstep
    refine moved_leads hup' ?_
    rw [handle_eq]
    exact entry_step_timer config hatt ha
  · intro c ev c' _ ⟨hup, ha⟩ _ hstep hrestarted
    exfalso
    obtain ⟨-, rfl⟩ := entry_some ha
    have hnot (msg : Jobs.Msg K J R) :
        Event.timeout (σ := sig K J R) () (timer a) ∉
          Effect.timeouts () (step config (c.state ()) msg).2 :=
      fun h => by
        obtain ⟨d, hd⟩ := Effect.mem_timeouts.mp h
        exact not_arms config ha msg d hd
    cases ev with
    | deliver e | duplicate e => exact hnot e.msg hrestarted
    | timeout i msg => exact hnot msg hrestarted
    | start i =>
      obtain ⟨hdown, -⟩ := SysState.step_start.mp hstep
      simp [hup] at hdown
    | input _ | drop _ | output _ | crash _ => exact List.not_mem_nil hrestarted

/-- An active job stops being active, whatever the workers do, in any environment that does not
crash the jobs actor. -/
theorem active_leaves (config : Config R) (hcrash : env.mayCrash () = false) (key : K) :
    (system (K := K) (J := J) config).LeadsTo env
      (fun c => c.up () = true ∧ key ∈ keys (c.state ()))
      (fun c => key ∉ keys (c.state ())) := by
  let f (c : SysState (system (K := K) (J := J) config)) : Nat :=
    match entry (c.state ()) key with
    | some a => left config a
    | none => 0
  refine System.LeadsTo.induction f fun n => ?_
  refine System.LeadsTo.mono
    (P := fun c => ∃ a : Active K J, (c.up () = true ∧ entry (c.state ()) key = some a)
      ∧ left config a = n) ?_ (fun _ h => h) ?_
  · intro c ⟨⟨hup, hkey⟩, hf⟩
    obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp ((not_congr entry_eq_none).mpr (Classical.not_not.mpr hkey))
    refine ⟨a, ⟨hup, ha⟩, ?_⟩
    simpa [f, ha] using hf
  refine System.LeadsTo.exists_left fun a => ?_
  by_cases hn : left config a = n
  · refine System.LeadsTo.mono (fun c h => h.1) (fun c hQ => ?_) (entry_leads config hcrash key a)
    rcases hQ with hgone | ⟨hup, a', ha', hlt⟩
    · exact .inl hgone
    · refine .inr ⟨⟨hup, mem_keys.mpr ⟨a', (entry_some ha').1, (entry_some ha').2⟩⟩, ?_⟩
      simp only [f, ha']
      omega
  · exact System.LeadsTo.of_imp fun c h => absurd h.2 hn

/-- A job stops being active only in a step that emits its answer. -/
theorem answered_of_leaves {c c' : SysState (system (K := K) (J := J) config)}
    {ev : Event (sig K J R)} (hstep : c.step env ev = some c') {key : K}
    (hin : key ∈ keys (c.state ())) (hout : key ∉ keys (c'.state ())) :
    ∃ outcome, Output.answer key outcome ∈ c'.outbox := by
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp ((not_congr entry_eq_none).mpr (Classical.not_not.mpr hin))
  have hhandle (c₀ : SysState (system (K := K) (J := J) config)) (hs : c₀.state = c.state)
      (i : Unit) (msg : Jobs.Msg K J R) (hgone : key ∉ keys ((c₀.handle env i msg).state ())) :
      ∃ outcome, Output.answer key outcome ∈ (c₀.handle env i msg).outbox := by
    obtain rfl : i = () := rfl
    rw [handle_eq] at hgone ⊢
    simp only [update_self] at hgone
    rw [hs] at hgone ⊢
    obtain ⟨o, ho⟩ := answer_of_leaves config ha (entry_eq_none.mpr hgone)
    exact ⟨o, List.mem_append_right _ (Effect.mem_emits.mpr ho)⟩
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

/-- The jobs actor answers every job it admits: in a fair run in which it is not crashed, a job
active while it is up has an answer handed over at a later position. -/
theorem active_answered (config : Config R) (hcrash : env.mayCrash () = false) (key : K)
    {r : (system (K := K) (J := J) config).Run env} (hfair : r.Fair) {n : Nat}
    (hup : (r.state n).up () = true) (hkey : key ∈ keys ((r.state n).state ())) :
    ∃ m, n ≤ m ∧ ∃ outcome, r.event m = some (.output (.answer key outcome)) := by
  obtain ⟨m, hm, hgone⟩ := System.LeadsTo.iff.mp (active_leaves config hcrash key)
    r hfair n ⟨hup, hkey⟩
  have hleaves : ∃ k, n ≤ k ∧ key ∈ keys ((r.state k).state ()) ∧
      key ∉ keys ((r.state (k + 1)).state ()) := by
    induction m, hm using le_induction with
    | base => exact absurd hkey hgone
    | succ m hm ih =>
      by_cases hin : key ∈ keys ((r.state m).state ())
      · exact ⟨m, hm, hin, hgone⟩
      · exact ih hin
  obtain ⟨k, hk, hin, hout⟩ := hleaves
  cases hev : r.event k with
  | none => exact absurd (System.Run.step_none hev ▸ hin) hout
  | some ev =>
    obtain ⟨outcome, hemitted⟩ := answered_of_leaves (System.Run.step_some hev) hin hout
    obtain ⟨m', hm', htaken⟩ := hfair.output_taken (n := k + 1) hemitted
    exact ⟨m', by omega, outcome, htaken⟩

/-- Every submission the jobs actor handles is answered: in a fair run in which it is not
crashed, a step that delivers a submission, or a duplicate of one, is followed by a hand-over of
an answer to its key. The answer may be to an earlier submission of the same key that is still
active, which this one then joins. -/
theorem submitted_answered (config : Config R) (hcrash : env.mayCrash () = false)
    {r : (system (K := K) (J := J) config).Run env} (hfair : r.Fair) {n : Nat}
    {e : Envelope (sig K J R)} {key : K} {job : J}
    (hev : r.event n = some (.deliver e) ∨ r.event n = some (.duplicate e))
    (hmsg : e.msg = .submit key job) :
    ∃ m, n < m ∧ ∃ outcome, r.event m = some (.output (.answer key outcome)) := by
  have hafter : (r.state n).up () = true ∧ ∃ c₀ : SysState (system (K := K) (J := J) config),
      c₀.state = (r.state n).state ∧ c₀.outbox = (r.state n).outbox ∧
        r.state (n + 1) = c₀.handle env e.dst e.msg := by
    rcases hev with hev | hev
    · obtain ⟨hup, _, h⟩ := SysState.step_deliver.mp (System.Run.step_some hev)
      exact ⟨hup, { r.state n with net := (r.state n).net.erase e }, rfl, rfl, h⟩
    · obtain ⟨hup, _, _, h⟩ := SysState.step_duplicate.mp (System.Run.step_some hev)
      exact ⟨hup, _, rfl, rfl, h⟩
  obtain ⟨hup, c₀, hs, ho, hnext⟩ := hafter
  have hup' : (r.state (n + 1)).up () = true := by
    rcases hev with hev | hev <;> exact stays_up hcrash hup (System.Run.step_some hev)
  have hsubmit := submit_step config ((r.state n).state ()) key job
  rw [← hmsg] at hsubmit
  have hstate : (r.state (n + 1)).state () = (step config ((r.state n).state ()) e.msg).1 := by
    rw [hnext, handle_eq]
    simp [hs]
  rcases hsubmit with hkey | ⟨outcome, houtcome⟩
  · obtain ⟨m, hm, h⟩ := active_answered config hcrash key hfair hup' (hstate ▸ hkey)
    exact ⟨m, by omega, h⟩
  · have hout : Output.answer key outcome ∈ (r.state (n + 1)).outbox := by
      rw [hnext, handle_eq, ho, hs]
      exact List.mem_append_right _ (Effect.mem_emits.mpr houtcome)
    obtain ⟨m, hm, h⟩ := hfair.output_taken hout
    exact ⟨m, by omega, outcome, h⟩

/-- Beside any system, every active job stops being active, in any environment that does not
crash the jobs actor: what the actor alone does, it does in `attach sys`. The step in which a
job stops being active emits its answer (`Jobs.answered_of_leaves`), which the wiring hands to
`sys`. -/
theorem attach_active_leaves {τ : Signature} (sys : System τ) (config : Config R)
    (use : Use τ K J R) {env : EnvModel (joinSig (sig K J R) τ)}
    (hcrash : env.mayCrash (.inl ()) = false) (key : K) :
    (attach sys config use).LeadsTo env
      (fun c => c.up (.inl ()) = true ∧ key ∈ keys (c.state (.inl ()) : List (Active K J)))
      (fun c => key ∉ keys (c.state (.inl ()) : List (Active K J))) :=
  System.LeadsTo.join_left
    (P := fun c : SysState (system (K := K) (J := J) config) =>
      c.up () = true ∧ key ∈ keys (c.state ()))
    (Q := fun s _ => key ∉ keys (s ())) (active_leaves config (env := env.left) hcrash key)

end Lanes.Jobs
