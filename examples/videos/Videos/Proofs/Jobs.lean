/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Semantics
import Videos.Proofs.Gone
import Videos.System

/-!
# The site's jobs

The site's work that is due later is the scheduler's (`Lanes.Schedule`): a check, the last
check of an upload never confirmed, the delete of a deleted video's object. What the scheduler
proves holds of them here, since its steps are its own steps beside the site:

- the scheduler holds at most `maxJobs` jobs and no key twice (`jobs_bounded`), so one delete
  of each object at a time, and one check for each request;
- in a fair run in which the scheduler does not crash, every job it holds ends, whatever the
  store does: answers late, wrongly, `unknown` or never (`job_ends`).

Of the site: a delete answered schedules the delete of the object (`Site.delete_schedules`), and
the end of that job is reported as an object given up exactly when the scheduler gave it up
(`Site.delete_reported`). That the end the scheduler emits reaches the site, which the
semantics' fairness gives for a message to an actor that stays up, is not proved here; the
checker checks the whole of it (`Videos.Check`).

`job_ends` keeps the scheduler's premise that the job is not periodic. The site schedules only
calls, but the system takes schedulings from outside too, as every input of the scheduler is
an input of the join, so that no job is periodic is not an invariant of it.
-/

set_option linter.unusedSectionVars false

namespace Videos

open Lanes

/-- The scheduler beside the site holds no more than `maxJobs` jobs, and no key twice, in every
run under every environment model. -/
theorem jobs_bounded (config : Config) (env : EnvModel fullSig) :
    (system config).Invariant env fun c =>
      (c.state (.inl ()) : Schedule.State Key Unit).jobs.length ≤ config.maxJobs ∧
        (Schedule.keys (c.state (.inl ()) : Schedule.State Key Unit).jobs).Nodup :=
  Schedule.attach_within (alone config) config.scheduler use env

/-- Every job of the site ends: in a fair run in which the scheduler does not crash, a job it
holds while it is up stops being held, whatever the store answers, and whenever. -/
theorem job_ends (config : Config) {env : EnvModel fullSig}
    (hcrash : env.mayCrash (.inl ()) = false) (key : Key) :
    (system config).LeadsTo env
      (fun c => c.up (.inl ()) = true ∧ ∃ j, Schedule.entry
        (c.state (.inl ()) : Schedule.State Key Unit).jobs key = some j ∧ j.work.periodic = false)
      (fun c => key ∉ Schedule.keys (c.state (.inl ()) : Schedule.State Key Unit).jobs) :=
  Schedule.attach_held_leaves (alone config) config.scheduler use hcrash key

namespace Site

variable (config : Config)

/-- A delete answered schedules the delete of the video's object in the store, retried as
`deleteRetry` says. -/
theorem delete_schedules {s : Site} {req : ReqId} {m : Member} {session : Sid} {at_s : Nat}
    {v v' : VideoId} {r : ReqId} {viewer : Viewer}
    (h : Out.reply r viewer (.deleted v) ∈ (s.handle config (.request (.delete req m session v') at_s)).2) :
    schedule (.delete v) config.deleteRetry at_s (at_s * 1000) ∈
      (s.handle config (.request (.delete req m session v') at_s)).2 := by
  simp only [handle, request, withSession, owned] at h ⊢
  by_cases hl : s.accepts config.lifetime at_s m session = true
  · cases hfind : s.find? v' with
    | none => simp [hl, hfind, answer] at h
    | some video =>
      by_cases ho : video.owner = m
      · simp only [hl, hfind, ho, ite_true, delete] at h ⊢
        have hv : v = video.id := by
          simp only [List.mem_append, answer, List.mem_singleton, Out.reply.injEq,
            Reply.deleted.injEq] at h
          rcases h with (((h | h) | h) | h) | h
          · unfold waiterOf at h
            split at h <;> simp [answer] at h
          · exact h.2.2
          · simp [schedule] at h
          · unfold unexpire at h
            split at h <;> simp at h
          · unfold unstart at h
            split at h <;> simp at h
        subst hv
        simp
      · simp [hl, hfind, ho, answer] at h
  · simp [hl, answer] at h

/-- Told the end of the delete of a video's object, the site reports the object given up exactly
when the scheduler gave it up: refused, or out of attempts or time. -/
theorem delete_reported (s : Site) (v : VideoId) (o : Outcome) :
    Out.orphan v ∈ (s.handle config (.job (.delete v) o)).2 ↔ o.givenUp = true := by
  simp only [handle, job]
  split <;> simp_all

end Site

end Videos
