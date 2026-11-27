# D?. A video is ready only after a transcode worker outside the site says so, signed

`Lanes/Outside/Transcode.lean`, `Lanes/Web/Transcode.lean`, `Lanes/Testing/Transcode.lean`,
`examples/videos`. The owner approved a video pipeline: an external transcode and thumbnail
worker, modelled as an outside service, so that a video is ready only after its transcode. Until
now a video was ready once a `HEAD` confirmed its upload, and its page played the upload itself,
in whatever format the member sent. This is that pipeline.

## The worker is a class of outside service

`Lanes.Transcode` models a worker as an `Rpc.Server` beside the object store it writes to, in
the style of D65 and D81: a job is a call (a source key and the keys to write), the call's
answer says only that the worker took the job, and what became of it comes later as a report,
done or failed, by a webhook. The store is `ObjectStore.server`, embedded, so that the worker's
writes are the store's: from the moment a job is sent each of its writes may land at any moment
or never, as a write granted to a browser does, and a done report lands them. Reports are
delivered late, again (`Events.bounded`) or never. A job is sent under its id (rule 3.4): a
repeat of an id is the same job.

**The honesty assumption.** An honest worker (`server made true`) reports a job done only if it
was sent the job, names the job's targets as what it wrote, could read the source (the store may
hold an object there), and has written the targets. Honest or not, it reports each job one way.
A dishonest worker (`server made false`) may report done for a job it was never sent, naming any
keys, having written nothing. Which reports are the worker's is not the model's to say: a caller
takes a report as the worker's only if it is signed with a key it shares with the worker alone,
and assumes the worker holding it is honest. A report not signed so is anyone's, and the checker
lets anyone post one (`Videos.Check`, `forging`).

Proved, with gates in `Tests/Axioms/Outside.lean`: under honesty a done report delivered names a
job some call of the run sent, and that job's targets (`Transcode.done_given`); honest or not,
two reports delivered for one job are the same report, however often each is delivered
(`Transcode.reports_agree`). Tested with runs written by hand (`Tests/Outside.lean`): a job
retried after a timeout, done, reported twice, its rendition then held; a done report refused
for a job not sent, other targets, an unreadable source, or after a failed one; a third
delivery refused; the rendition held after the done report and maybe before.

## A generic HTTP worker in Lanes, not MediaConvert in integrations

D61 puts a class of outside system in `Lanes/` and a vendor in `integrations/`. The worker here
is a class, and its wire format is no vendor's: a job is a JSON object posted to the worker's
`/jobs`, `{"callback","id","source","targets"}`, and the worker posts its report back as JSON to
the callback, `{"job","status","written"}`. Both carry an HMAC-SHA-256 tag in a
`lanes-signature` header under a key the site and the worker share: a job's over its body, for
the purpose `transcode-job`; a report's over its job and its status, one line each, for the
purpose `transcode`, which is all the site acts on and which a worker computes from its fields
however it writes its JSON, as SNS signs a canonical string of its fields
(`Lanes/Web/Transcode.lean`, `Transcode.verify_iff`, gated in `Tests/Axioms/Web.lean`). Any
worker that speaks this, a process of one's own around ffmpeg, a function behind a queue, fits;
MediaConvert does not speak it, and is a vendor: an adapter for it, which would turn a job into
`CreateJob` and its EventBridge events into reports, belongs in `integrations/aws` and is not
written. The site depends on the class, so swapping the worker changes no theorem of the site's.

The test kit has a worker that speaks the format (`Lanes.Testing.Transcode`): it takes a job
only with its signature, reads the source from the store through the S3 client, writes small
objects at the targets, and posts its signed report when the test says (`Fake.work`); it can be
told to fail the next jobs and to forge a report with another key. Through the S3 client it
works against the fake S3 or a real bucket, so `videosLive` runs it too.

## The site

A video moves pending → checking → transcoding → ready, or → failed (`Videos.Status`).

- **A confirmed upload starts a transcode.** A check or the last check that the store answers
  `found` makes the video `transcoding size 0` and schedules the start of round 0
  (`Key.transcode`), a job of the scheduler whose call posts the round's job to the worker,
  retried by `Config.transcodeRetry` (six attempts, about five minutes) and bounded by
  `maxJobs`. Round `n` of video `v` is the worker's job `v.n`; its targets are `videos/<v>.mp4`
  and `videos/<v>.jpg`, beside the upload `videos/<v>`.
- **Ready only on the worker's word.** A report comes as a request, `Command.report`, with the
  signature it came with; the bridge decides nothing about it. The site takes it only if the
  signature is the worker's for its round and status (`Report.signed`, through
  `Transcode.verify`, under `Config.workerKey`), and answers `403` otherwise. A done report of
  the round under way, or of a failed one, makes the video ready; a failed report of the round
  under way makes it failed; a report of another round changes nothing, and is acknowledged,
  so a worker that retries until it is acknowledged stops.
- **Failed, and tried again.** A start the scheduler gives up on, or refuses at `maxJobs`, is a
  failed round. A failed video is shown to its owner, on its page and its channel, with "Try
  again" (`Command.retry`), which begins the next round. A video not ready is shown to its owner
  as what it waits for (`Reply.preparing`: the upload, its transcode, or a retry), to no one
  else.
- **The page plays the rendition**, with the thumbnail as its poster, both by links presigned
  as the upload's were. A delete deletes the upload, the rendition and the thumbnail, one job
  whose attempt is the three deletes, `deleted` only if each is, and cancels the start of a
  round under way.

Why the signature is checked in the spec and not in the bridge, as a session cookie is: a check
in the bridge is tested, one in the spec is proved and model-checked, and a forged report is
exactly the input the checker should be able to send. The key is a field of `Config`, with no
default, so no deployment runs with a key it did not choose; the spec holds no other secret.

## What is proved and checked

Of every run of the spec's functions, with the seeded bugs off (`Config.Honest`, which now also
asks `trustUnsigned` off):

- a video is listed as ready only after a request in which the worker reported a round of its
  transcode done, with a signature that checks under the worker's key
  (`Videos.Site.listed_transcoded`), and still only after the store confirmed its upload
  (`Videos.Site.listed_confirmed`);
- a report changes only the video its round names: every other video, every channel and every
  count is as it was, whatever the report and its signature (`Videos.Site.report_names`).

Every theorem of the site that held before holds, restated where its functions changed.

*Liveness is checked, not proved.* With a fair run and an honest worker that eventually
reports, a confirmed upload leads to ready or failed. D89's join lemmas, which would carry the
scheduler's ends and the worker's reports through the join (`Fair.routed_*`,
`Schedule.attach_end_handled`), are in an open pull request (tacitresearch/lanes#80), not on the
main branch. So the checker checks it instead: of runs with no crash, every state with no
successor, the script done, every message delivered, every timer fired and the worker's reports
spent, has no video transcoding (`Videos.Check`, `pipeline`, as deadlocks). A run with a crash
can lose the report on its way in the mail of the site, which the semantics allows and one shard
does not (D87); a real worker posts again until it is acknowledged.

The checker explores the site, its scheduler, the worker's model with its store, two browsers and
a forger, with a crash anywhere: reports delivered twice, failed, or forged; every claim of the
site's held, and three more: nothing shown that the worker did not report done, signed; nothing
shown whose rendition and thumbnail the store may not hold. Seeded: a report taken unsigned
(`trustUnsigned`) shows a video the worker never reported done.

## Consequences

- A deployment needs a worker: `VIDEOS_WORKER_URL`, `VIDEOS_WORKER_SECRET`, and
  `VIDEOS_WORKER_CALLBACK` when the worker reaches the site by another address. None is in the
  repository; the test kit's is the only worker that speaks the format so far.
- The journal's format changed (statuses, commands, keys) and the journal is named `videos 3`: a
  journal of `videos 2` is refused, not misread. No `Upgrade` was written.
- A round under way has no deadline. The scheduler's outcomes carry no time, so the site cannot
  set one from the moment a check succeeds, and a worker that took a job and never reports leaves
  the video transcoding until its owner deletes it. A deadline wants the time in
  `Schedule.Outcome`, or a notice job scheduled from a request.
- The checks are larger, and `lake test` in `examples/videos` takes longer.
