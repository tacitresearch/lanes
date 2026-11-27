# D?. The video site's calls to the store are jobs of the scheduler, named by what they are for

`examples/videos`, `Lanes/Behaviours/Schedule/Sound.lean` (`Schedule.succeeded_replied`),
`Lanes/Testing/S3.lean` (`Fake.refuse`). D79 left the video site to move onto the scheduler: a
delete the store did not answer was sent again at once a few times, then logged; an upload never
confirmed stayed pending, and held one of its member's `maxPending` places, until its owner
deleted it. This is that move.

## What became a job

Every call the site makes to the store is a job of the scheduler beside it (`Schedule.attach`),
held under a key that names what it is for (`Videos.Key`):

- `check v req`: the `HEAD` that request `req` asked for when the browser said the upload is
  done. The request waits for the job's end. Two attempts, five seconds each, half a second
  apart: a member waits for it, so it is short.
- `expire v`: the last check of an upload, a day after its record was made (`Config.pending_s`),
  far past the upload form's fifteen minutes. Found, the video is ready, whether or not its
  member ever said it was uploaded; not there, its record is taken out, and its place in
  `maxPending` is free again. It is cancelled when the video is ready or deleted.
- `delete v`: the delete of a deleted video's object, ten attempts with a backoff capped at five
  minutes. Given up, or refused because the scheduler is full, it is reported (`Out.orphan`).

Sessions did not become a job. They end by the time each request carries (`Auth.Sessions`,
judged at the time the request arrived), and a member's are bounded by `maxSessions`; a sweep
would only free the memory of sessions over, which the bound already caps.

The site holds no call ids, no list of deletes and no `maxDeleting`: the scheduler holds the
jobs, under `maxJobs`, and its state is the journal's, so a job survives a restart. The site's
start no longer sends every delete again; the scheduler's start arms every job's timer again
(`Schedule.armed`).

## The key says what the job asks

A job's payload is `Unit`, and the adapter asks the store what the key says (`Key.op`): the head
of `videos/<v>` for a check, its delete for a delete. A key and a payload that disagree, a check
of `v` that asks about `w`, cannot be written (rule 2.1). The check's key carries the request
that waits, so the end of an old check, superseded by a newer one, is told to nobody, as call
ids did before; a `found` of any check still makes the video ready, since it is the store's word.

## What is proved

The site's own claims are kept and restated where the store's word now comes through the
scheduler. A video is shown only after an input in which the scheduler said that a job of a key
that asks for its object's head succeeded with `found` (`Videos.Site.listed_confirmed`), and the
scheduler says a job succeeded with an answer only in the step that takes that answer to the
job's attempt out (`Schedule.succeeded_replied`, new, for every configuration and every
environment). Of the site beside its scheduler: a like counts once and a private video is its
owner's alone in every run (`Videos.likes_distinct`, `Videos.private_to_owner`, now of the
join); the scheduler holds at most `maxJobs` jobs and no key twice (`Videos.jobs_bounded`); in
a fair run in which the scheduler does not crash, every job held ends, whatever the store does
(`Videos.job_ends`); a delete answered schedules the delete of the object
(`Videos.Site.delete_schedules`), whose end the site reports as given up exactly when the
scheduler gave it up (`Videos.Site.delete_reported`).

*Not proved: that a deleted video's object is eventually deleted from the store.* It is false:
the store may refuse every attempt, and the job then gives up; and the object store's model lets
an upload granted before the delete land after it, the gap the README already names. What holds
is that the delete ends, deleted or reported, and the theorems above give its parts; the step
between them, that the end the scheduler emits reaches the site, is a message to an actor that
stays up, which fairness delivers (`System.Run.Fair.delivered`), but no lemma lifts
`Schedule.held_ends` through a join yet. The checker checks the whole (`Videos/Check.lean`): in
every state of a run with no crash, a video whose delete was answered has its delete still under
way, the store's `deleted` to one of its attempts, or its report.

*Not with a crash, and why that is the semantics'.* The checker found, in 10 steps, the
scheduler crashing with the site's scheduling of a delete in its mail: a crash loses an actor's
mail (`SysState.down`), the job is never held, and the object is never deleted nor reported. The
old site kept its deletes and sent each again at its start, which covers its own crash but not
the scheduler's. On one shard neither happens: an actor crashes only by stopping itself
(`Kernel.env`, `TRUSTED.md`), which neither does, and the death of the process returns to the
journal, the kernel's queue of messages included. So the claim is checked of runs with no crash
of an actor, and every other claim of runs with one anywhere. If the scheduler ever runs on
another shard than the site, the site must keep what it scheduled until the scheduler answers
(`scheduled`, `already`) and schedule it again, as D79 says a requester may.

`Videos.job_ends` keeps the scheduler's premise that the job held is not periodic. The site
schedules only calls, but every input of the scheduler is an input of the join, so a scheduling
from outside could be periodic: that no job is periodic is not an invariant of the system.

## What changed for a member

- A check the store refuses or does not answer is tried once more before the member is told
  `unconfirmed`. The page waits up to about thirteen seconds, not ten.
- An upload never confirmed is checked a day later, made ready if the store has it and taken out
  if not. Before, it stayed pending until its owner deleted it: this was the bug of friction
  item 5, a member with `maxPending` abandoned uploads could upload nothing more.
- A delete the store refuses is retried for about ten minutes, not three times at once.
- At the bound, a delete past `maxJobs` is given up and reported at once; before, the oldest
  delete past `maxDeleting` was.

## Consequences

- The journal's format changed (no `deleting`, no call ids, the scheduler's actor), and the
  journal is named `videos 2`: a journal of `videos 1` is refused, not misread. No `Upgrade` was
  written.
- `Testing.S3.Fake.refuse n` answers the next `n` signed requests `503 SlowDown`, so that a test
  sees a retry; the video site's end-to-end test has a check and a delete each refused once and
  retried.
