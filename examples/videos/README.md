# videos

A small video-sharing site: members sign in with Google or GitHub, each has a channel, uploads
videos straight from the browser to S3, has them transcoded by a worker outside the site, and
watches, likes, comments on and deletes them. A video is public (in the feed and on its
channel), unlisted (by its link) or private (its owner's alone). It is the V1 acceptance application of Lanes: the pieces a site like YouTube needs, put
together, checked and proved, and deployable with `docs/DEPLOY.md`. What made it harder than it
should be is at the end.

```bash
cd examples/videos
mkdir -p .lake && ln -s ../../../.lake/packages .lake/packages   # share the fetched dependencies
lake build            # the site, the proofs and the tests
lake test             # model checks, the bridge, and the site over HTTP against a fake S3 and worker, ~10 min
lake exe videosTest pipeline   # only the model checks whose names contain a word; `http`, only the site
```

## How it works

- **The spec is the code.** `Videos/Spec.lean` is one value, `Site`, and two functions:
  `Site.handle` for an input (a request, or the scheduler's word on a job) and `Site.recover` for
  a start of the actor. `Videos/System.lean` runs them in one actor, so every claim is about one
  atomic owner: a delete vanishes from the feed, the channel and the watch page at once.
- **Work that is due later** is the scheduler's (`Lanes.Schedule`, D79), beside the site in the
  same shard and on the same journal. Every call to the store or the worker is a job, held under
  a key that names what it is for and so what it asks (`Videos.Key`, `Key.op`): a check, the last
  check of an upload, the start of a round of a transcode, the delete of a video's objects. A job survives a restart, is retried with a
  backoff and a jitter (`Config.checkRetry`, `Config.deleteRetry`), and the scheduler holds at
  most `maxJobs`; past it a job is refused. Each attempt carries its deadline, and the S3 client
  cuts the call off there.
- **Sign-in** is Lanes' (`Lanes.OAuth`, D72), in `serve`'s `arrive`: the system gets only the
  identity the provider vouched for, by its issuer and subject, and a member is made the first
  time one signs in, its channel named by the provider's name for it (the login, without one),
  which the pages show as text. A session is a signed cookie and an entry of the member's
  `Auth.Sessions`, and lets requests in for 30 days after its sign-in (`Config.lifetime`), judged
  at the time each request arrived; a sign-in sweeps the member's sessions that are over.
- **Upload.** "Upload" makes a record, `pending`, and answers a page whose form posts to the
  bucket under a policy signed for fifteen minutes (`Lanes.S3.Post`): the key `videos/<id>` and
  the content type exactly, and a size from one byte to `maxUpload_bytes` (2 GiB, or
  `VIDEOS_MAX_UPLOAD_BYTES`), which the store refuses past (`EntityTooLarge`). The browser posts
  the file there itself (`upload.js`, a dozen lines that `fetch` the form's `FormData` and then
  post the next form, and that do not send a file over the limit), and posts "uploaded". The site
  then schedules a check, a `HEAD` tried twice, and answers that request when the job ends:
  `found` confirms the upload; `missing`, two errors or no answer in time leave it `pending`,
  to check again from the channel. A day after the record was made (`Config.pending_s`), an
  upload still not confirmed is checked a last time: found, it is confirmed; not there, its
  record is taken out. The site never carries video bytes.
- **Transcode** (`docs/decisions/new-video-pipeline.md`). A confirmed upload is `transcoding`:
  the scheduler posts round 0's job to the worker (`Lanes.Transcode`, a JSON job over HTTP with
  its signature, `Config.transcodeRetry`), whose targets are `videos/<id>.mp4`, a playable
  rendition, and `videos/<id>.jpg`, its thumbnail. The worker posts its report to `/transcoded`,
  signed with the key the site shares with it alone (`VIDEOS_WORKER_SECRET`). Only a done report
  of the round, with the worker's signature, makes the video `ready`; a report without it is
  answered `403` and changes nothing. A failed report, or a job the worker could not be given,
  makes it `failed`, which its owner sees on its page and channel with "Try again": the next
  round. A video not ready is shown to its owner as what it waits for, and to no one else.
- **Watch.** The page's `<video>` plays the rendition, with the thumbnail as its poster, each a
  link presigned for a `GET`, signed when the request arrived: `arrive` writes the time into the request, so the time is in the journal and the
  link is the same on replay. Links are signed in the bridge's `encode`, with the deployment's
  credentials; the system holds none.
- **Delete** takes the record out at once and schedules the delete of the upload, the rendition
  and the thumbnail, tried up to ten times over about ten minutes, and cancels the start of a
  round under way; one given up on, or refused because the scheduler is full, is
  logged (`Out.orphan`).
- **Pages** are server-rendered with Lanes' templates. Every form that changes something carries
  a token bound to the session (`Auth.formToken`) and must come from the site's origin; the style
  sheet and the script are served by the bridge, since templates refuse inline code.
- **Ops**: `/healthz`, `/readyz`, `/metrics` and the access log (`ServerConfig.ops`); SIGTERM
  drains the requests in flight before it stops (`Server.stopOnSignal`).
- **Storage**: the journal, with a snapshot every 256 inputs, of the site and its scheduler. No
  database.

## The claims

Each is a theorem in `Videos/Proofs/`, gated in `Videos/Proofs/Axioms.lean`, and each is also
model-checked (`Videos/Check.lean`).

| Claim | Theorem |
| --- | --- |
| A private video is its owner's alone: in every run of the system, under every environment model, an output that shows one is addressed to its owner; and of every input, only in an answer to a session of the owner that let the request in when it arrived, open and not past its lifetime | `Videos.private_to_owner`, `Videos.Site.handle_private` |
| A like counts each member once: in every reachable state of the system, under every environment model, no video's likes name a member twice, so the count shown is the number of distinct likers | `Videos.likes_distinct`, `Videos.count_distinct` |
| A deleted video is never served again: once a delete is answered, no output of any later input or start shows it, however the store answers the delete (late, refused, `unknown`, never) | `Videos.Site.deleted_never_served`, `Videos.Site.Gone.run` |
| A video is shown only once the store confirmed its upload: an output that shows a video comes after an input in which the scheduler said a job that asks the store for its upload's `HEAD` succeeded with `found`; and the scheduler says so only in the step that takes the store's `found` to that job's attempt | `Videos.Site.listed_confirmed` (the seeded bugs off: `Config.Honest`), `Schedule.succeeded_replied` |
| A video is listed as ready only after a done report for it whose signature checks: an output that shows a video comes after a request in which the worker reported a round of the video's transcode done, signed under the worker's key | `Videos.Site.listed_transcoded` (the seeded bugs off) |
| A report changes only the video its round names: every other video, every channel and every count is as it was, whatever the report and its signature | `Videos.Site.report_names` |
| What an output shows is a ready video of the site, and a private one only to a session of its owner that let the request in | `Videos.Site.shows_handle` |
| The scheduler holds at most `maxJobs` jobs and no key twice: one delete of an object at a time | `Videos.jobs_bounded` |
| Every job ends, whatever the store and the worker do: in a fair run in which the scheduler does not crash, a check, a last check, the start of a transcode or a delete held stops being held | `Videos.job_ends` |
| A delete answered schedules the delete of the object, and its end is reported as given up exactly when the scheduler gave it up | `Videos.Site.delete_schedules`, `Videos.Site.delete_reported` |

`listed_confirmed`, `listed_transcoded`, `report_names`, `deleted_never_served`, `Gone.run` and
`shows_handle` are about runs of the spec's functions, `Site.handle` and `Site.recover`, which is what the actor runs; the others
about the runs of the site beside its scheduler. The theorem that turns a run of the system into
the run of the spec its actor performed is not written (as for rookery). That a deleted video's
object is eventually deleted from the store is not proved, and is false: the store may refuse
every attempt, and an upload begun before the delete may land after it. What is proved is that
the delete ends and is reported if it gave up, but for the step between: that the scheduler's
word reaches the site, which the checker checks. That a confirmed upload ends ready or failed,
with an honest worker that reports, is checked and not proved: the lemmas that carry fairness
through the join (D89's) are in an open pull request.

### What the claims rest on

- **The bridge** (`Videos/Web.lean`) is tested, not proved: that a request names a member only
  through a cookie it verified, that a form needs its token, that the time is the server's
  (`bridge:` tests, and over HTTP).
- **Links handed out before a delete are the store's.** A watch link lasts six hours and an upload
  form fifteen minutes. A link signed before the delete still works until it expires or the
  store's delete lands, and an upload form used after the delete leaves an object no record
  names. A lifecycle rule on the bucket, or a second delete after the upload form expires, would
  close it.
- **The store** is as `Lanes.ObjectStore` models it, with the browser's upload as a write the
  site grants and never hears answered (`granted`), and its `HEAD` as the model's head
  (`Videos/Check.lean`).
- **The worker** is as `Lanes.Transcode` models it, honest: it reports a round done only once it
  was given the job, could read the upload and wrote the rendition and the thumbnail, and each
  round one way. Only it holds the key (`VIDEOS_WORKER_SECRET`), and HMAC-SHA-256 is unforgeable
  (`TRUSTED.md`). A round under way has no deadline: a worker that took a job and never reports
  leaves the video transcoding until its owner deletes it.
- **The scheduler's time** is not ahead of the clock (D79's premise, `TRUSTED.md`): a job is
  never run before its time as the scheduler knows it.

## What is checked

`Videos/Check.lean`, run by `lake test`: two members, at most two videos and one per member, one
pending upload per member, two comments and one per member on a video, three jobs, one attempt
for each job or two where the scenario says. The site and its scheduler beside the browsers,
which follow a script, and the worker's model with the object store's, which answers each
attempt out at most once, late, never, refused or `unknown`, lets an upload not answered and the
worker's writes land at any moment or never, and has the worker report each job it was given
done or failed, late or never; in the pipeline, twice, and anyone else post reports not signed
with the worker's key. Every timer of the scheduler fires at any moment, and the site's actor or
the scheduler crashes and starts again anywhere. What each browser is shown is judged as it is
shown: besides the claims above, nothing is shown that the worker did not report done, signed,
or whose rendition and thumbnail the store may not hold.

The worker's faults multiply every interleaving, so they are explored where they are the point.
In the scenarios about the site and the store the worker takes each job and reports it done once,
at any moment while its video is there; in the two about a check under way it never answers, and
only the site crashes, as the scenarios too large for both to crash did before. The pipeline
explores a job not answered, refused or `unknown` (with no crash), a report late, failed or
never, and a retry; the forgery a report delivered twice and one posted by someone else. And of
runs with no crash, every state with no successor (the script done, every message delivered,
every timer fired, the worker's reports spent) has no video transcoding: a confirmed upload ends
ready or failed. That is the liveness claim, checked and not proved.

| Scenario | States | Result |
| --- | --- | --- |
| A public video: made, checked, transcoded, watched, liked three times, deleted, asked for after the delete | 1,838,171 | pass |
| A private video: asked for by another member, a stranger and its owner; channels, the feed, a like and a comment by another | 33,850 | pass |
| A video deleted while its check may be out (the site crashes) | 1,648,323 | pass |
| A second check asked for while the first may be out (the site crashes) | 1,414,585 | pass |
| A delete tried twice: deleted after its first attempt failed, or given up and reported | 61,578 | pass |
| An upload never confirmed, checked a last time, twice: confirmed, transcoded and shown, or taken out | 359,757 | pass |
| A session past its lifetime: a private video watched inside it, asked for and liked after it, then watched in a new session | 24,529 | pass |
| The pipeline: a job not answered, refused or `unknown` (with no crash), a report late, failed or never, shown to the owner, tried again and shown (the site crashes) | 2,852,633 | pass |
| Reports delivered twice, and one forged by someone else | 286,132 | pass |
| With no crash, every run that cannot go on leaves each confirmed upload ready or failed | 2,812,148 | pass |
| Seeded: the browser's word taken for the upload (`trustBrowser`) | | found in 20 steps |
| Seeded: a check the store did not answer in time taken as found (`readyOnTimeout`) | | found in 25 steps |
| Seeded: sessions that never end (`lifetime := {}`) | | found in 20 steps |
| Seeded: a report taken whatever its signature (`trustUnsigned`) | | found in 21 steps |

Once a video's delete is answered, in every state its delete is under way, or the store said
it deleted the object, or the site reported it given up; this is checked of runs with no crash.
A crash in the semantics loses an actor's mail (`SysState.down`), and the checker found, in 10
steps, the scheduler crashing with the delete's scheduling in its mail: never held, never
reported. On one shard an actor crashes only by stopping itself, which neither does, and the
death of the process returns to the journal, the kernel's queue included (`TRUSTED.md`,
"Environment model"); if the scheduler ever runs apart from the site, the site must keep what it
scheduled until the scheduler answers.

Every bound holds in every state of every scenario, those of one member among them: one member's
videos (`maxOwned`) and comments on one video (`maxCommentsEach`) are bounded far below the site's
(`maxVideos`, `maxComments`), so one member cannot fill them for everyone. `capTests` checks
each at its limit, and that a video's owner takes out anyone's comment on it.

Over HTTP (`Videos/EndToEnd.lean`): the site as `Main` serves it, on a journal, against the test
kit of Lanes (`Lanes.Testing`): its identity provider in GitHub's shape, read by `GitHub.read`,
its fake S3, which checks every signature, the presigned links' and the upload forms' included,
and refuses a file over a policy's size, its transcode worker, which takes a job only with its
signature, reads the upload from the fake S3, writes a rendition and a thumbnail there and posts
its signed report when the test says, and its browser, which keeps the cookies. Three members
sign in; a video is made, posted to the store with its form, checked, shown to its owner alone as
being prepared, given to the worker, and once the worker reports watched through the
`<video>`'s links, the rendition and the thumbnail; a file over the limit refused by the store; likes counted
once, a comment, a forged form, another's delete; a private video seen by its owner alone; an
upload not yet in the store not listed; then the server is stopped and started again on its
journal, and the sessions, likes and comments are there, an upload begun before is checked, a
report of its transcode forged with another key is refused, its transcode fails, is shown to its
owner with "Try again", is tried again and is listed, the feed comes a page at a time, a comment is deleted by its author or the video's owner
and by no one else, a delete removes the video, its upload, rendition and thumbnail, and a
sign-out ends the session.
Twice the fake S3 is told to refuse the next call (`Testing.S3.Fake.refuse`): a check, which
the scheduler tries again and the video is confirmed, and a delete, whose next attempt deletes
the object.

## Running it

```bash
VIDEOS_BUCKET=my-videos AWS_REGION=eu-west-1 AWS_ACCESS_KEY_ID=... AWS_SECRET_ACCESS_KEY=... \
GITHUB_CLIENT_ID=... GITHUB_CLIENT_SECRET=... \
VIDEOS_WORKER_URL=http://127.0.0.1:9100 VIDEOS_WORKER_SECRET=... \
lake exe videos 8080 videos.journal videos.secrets
```

`Main.lean` lists what it reads: `VIDEOS_URL` (the public origin, from which each provider's
redirect URI `<VIDEOS_URL>/sign-in/<google|github>/callback` is made, and `Secure` cookies when
it is `https:`), `LANES_HOST`, `LANES_IDLE_MS` and `LANES_DRAIN_MS` (as `lanes new` reads
them; SIGTERM drains for that long, `Server.stopOnSignal`), `VIDEOS_BUCKET` (or
`LANES_MEDIA_BUCKET`, as a deployment's unit sets it), `AWS_REGION`,
`VIDEOS_S3_ENDPOINT` (MinIO or LocalStack, as `http://host:port`), the `AWS_*` credentials,
`VIDEOS_MAX_UPLOAD_BYTES`, each provider's client, and the worker: `VIDEOS_WORKER_URL` (its
origin; jobs go to `/jobs`), `VIDEOS_WORKER_SECRET` (the key the two sign with) and
`VIDEOS_WORKER_CALLBACK` (where it posts reports, `<VIDEOS_URL>/transcoded` unless set). The
worker speaks `Lanes/Web/Transcode.lean`'s format and writes to the same bucket; none ships with
Lanes but the test kit's (`Lanes.Testing.Transcode`). The bucket's CORS rules must allow `POST`
and `GET` from the site's origin. For a local store, MinIO with a bucket and a CORS rule for `http://localhost:8080` will
do; over plain HTTP set nothing else, since `VIDEOS_URL` defaults to `http://localhost:<port>`.

`lake exe videosLive` runs the end-to-end flow against the bucket the same variables name, with
the provider and the worker still the test's, under keys `videos-live-<n>/` that it deletes at the end. It is
not part of `lake test`, and has not been run against AWS from where it was written.

## Deploying it on AWS

`docs/DEPLOY.md`, with this directory as the application: the deploy workflow's `app-dir`
is `examples/videos` (or `.` in a repository of its own). The stack's parameters:

| Parameter | Value |
| --- | --- |
| `AppName` | `videos` |
| `BinaryName` | `videos` |
| `AppArguments` | `{port} {journal} {data}/videos.secrets` |
| `AppPort` | `8080` |
| `HealthCheckPath` | `/readyz` |
| `MetricsPath` | `/metrics` |
| `DomainName` | the site, such as `video.example.com` |
| `MediaUser` | `true` (the S3 client reads keys from the environment) |
| `DatabaseEngine` | `none` |

The unit names the stack's media bucket and its region (`LANES_MEDIA_BUCKET`, `AWS_REGION`),
which `Main` reads. On the instance, `/etc/lanes/secrets.env` (DEPLOY.md, "Media") holds, besides
the media user's `AWS_ACCESS_KEY_ID` and `AWS_SECRET_ACCESS_KEY`:

```bash
VIDEOS_URL=https://<DomainName>
GOOGLE_CLIENT_ID=...       # and/or GITHUB_CLIENT_ID
GOOGLE_CLIENT_SECRET=...
VIDEOS_WORKER_URL=...      # a worker that reads and writes the media bucket
VIDEOS_WORKER_SECRET=...
```

and each provider is registered with `https://<DomainName>/sign-in/<google|github>/callback`. The
stack's media bucket already allows the upload form's `POST`, and the presigned `GET` and
`HEAD`, from `https://<DomainName>`. The key in `videos.secrets` is made at the first start; losing it ends
every session, nothing else.


## Friction log

Where Lanes made this harder than it should be, most costly first. Workarounds are in this
package; none touches the library.

### Missing, or in the way

1. **Every page view is journalled.** A watch, a feed page or a channel page is a request, so it
   enters the journal, with its headers, and is synced before it is answered; ten page views
   added 3.4 KB to the journal of a smoke run, and each is replayed at every start until a
   snapshot cuts it. A site that is read a thousand times for each write wants reads answered
   from the state without a journal entry.
2. **`S3.handler` cannot be used behind the HTTP server.** It needs the system's `Runtime`, which
   `Http.serveFronted` keeps private; and `serveFronted` takes `onOutput` before the server it
   would hand inputs to exists, and wants its journal opened by hand with the sum of codecs.
   `Videos/Serve.lean` makes the call with `S3.exchange`, answers with `Server.tryInput`, and
   holds a promise of the server for the calls a start makes before `serveFronted` returns
   (about 40 lines that every application with an adapter will write).
3. **The bridge's `encode` sees only the output** (rookery's and the ledger's friction too). The
   links are signed there, with a time, so `arrive` writes the time into the request and it
   rides through the spec as `at_s`; the form tokens need the session, so every answer carries
   the viewer (`Out.reply`).
4. **A large upload does not resume.** A video is one `POST` under a policy that bounds its
   size (`Lanes.S3.Post`), so a failed upload starts again from its first byte. Lanes has
   multipart uploads (`Lanes.S3.Multipart`, and `S3.presignPart` for a browser's parts, each
   length signed), but the site would have to keep each upload's id and parts, which the spec
   does not: not wired.
5. **Nothing ran in the background** (since fixed: the scheduler, `Lanes.Schedule`, holds the
   site's checks, last checks and deletes as jobs, retried with a backoff). A delete was sent
   again at once a few times, then given up; an upload never confirmed stayed `pending` until its
   owner deleted it, and held one of their `maxPending` places. Transcoding and thumbnails are a
   worker's now (`Lanes.Transcode`), started by a job; the store's own events (S3 notifications)
   still have no way in. The
   scheduler's word comes back as an input, so the site's proofs about what it shows now rest on
   one more step: that the scheduler reports the store's answer as it was
   (`Schedule.succeeded_replied`).
6. **The object store's model** had no `HEAD` and no write by someone else, such as the
   browser with a presigned link (since fixed: `head` and `granted`, and `ObjectStore.held_sent`;
   its histories are sets now, and a key's settled outcomes replace its earlier ones). That cut
   the scenario of a video's life only from 741,759 states to 736,480 for thirteen requests: what
   remains is the interleavings of the store's answers with the site's crashes, not history.
7. **No kit for tests** (since fixed: `Lanes.Testing`, which this package's tests use). The fake
   S3 and the fake provider were test files of Lanes, which an application outside this
   repository cannot import; the browser (cookies, form tokens, following links) was written
   again here, as rookery and the ledger did.
8. **The S3 client takes keys only from the environment**: no instance role (IMDSv2), so the
   deployment needs a long-lived IAM user's keys. (The stack did not tell the application its
   media bucket; it does now, as `LANES_MEDIA_BUCKET` and `AWS_REGION`.)
9. **An identity had no name** (since fixed: `OAuth.Identity.name`, the provider's name or
   GitHub's login, which a channel now shows). A channel was named by what came before the `@`.
10. **Sessions did not end on their own** (since fixed: `Auth.Sessions` takes a `Lifetime`,
    judged at the time a request arrived, and this site's sessions last 30 days). Ending them
    needed a timer per session, as rookery's are. Each request now carries its time
    (`Input.request`), and the site does not record each use, which an idle limit would need.

### Clumsy

- **Tables are lists.** Every request scans the videos (the feed filters all of them), and every
  snapshot writes the whole site. Bounded, but a map that runs and proves easily would serve.
- **`arrive` starts a thread of its own for every request**, the style sheet's included, once an
  application has one (the sign-in needs it).
- **The checker and the outside world.** With requests from outside reordered, the first
  scenario did not finish in two minutes; the scripts are chains, and requests arrive in order.
- **Inline code is refused in templates**, so the bridge serves `/upload.js` and `/style.css`.
- **D71** presents `S3.handler` as how a system calls the store, which a web application cannot
  do (2). (`docs/DEPLOY.md` called the S3 client "in progress"; no longer.)

### Not there for a site like YouTube

Search (no index; a scan of the list), a worker that transcodes for real (the format is
written, the worker is not), renditions at several sizes, a CDN in front of the bucket (CloudFront's signed URLs need RSA signing, which Lanes does not
do), mail (SES speaks Signature Version 4, but there is no client), view counts (each view would
be a write), live updates (no server push), subscriptions, notifications, moderation and reports,
and a rate limit per member (`Lanes.RateLimit` exists; not used here).
