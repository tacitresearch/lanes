# videos

A small video-sharing site: members sign in with Google or GitHub, each has a channel, uploads
videos straight from the browser to S3, and watches, likes, comments on and deletes them. A video
is public (in the feed and on its channel), unlisted (by its link) or private (its owner's
alone). It is the V1 acceptance application of Lanes: the pieces a site like YouTube needs, put
together, checked and proved, and deployable with `docs/DEPLOY.md`. What made it harder than it
should be is at the end.

```bash
cd examples/videos
mkdir -p .lake && ln -s ../../../.lake/packages .lake/packages   # share the fetched dependencies
lake build            # the site, the proofs and the tests
lake test             # model checks, the bridge, and the site over HTTP against a fake S3, ~15 s
```

## How it works

- **The spec is the code.** `Videos/Spec.lean` is one value, `Site`, and two functions:
  `Site.handle` for an input (a request, or the store's answer to a call) and `Site.recover` for
  a start of the actor. `Videos/System.lean` runs them in one actor, so every claim is about one
  atomic owner: a delete vanishes from the feed, the channel and the watch page at once.
- **Sign-in** is Lanes' (`Lanes.OAuth`, D72), in `serve`'s `arrive`: the system gets only the
  identity the provider vouched for, by its issuer and subject, and a member is made the first
  time one signs in, its channel named by the provider's name for it (the login, without one),
  which the pages show as text. A session is a signed cookie and an entry of the member's
  `Auth.Sessions`, and lets requests in for 30 days after its sign-in (`Config.lifetime`), judged
  at the time each request arrived; a sign-in sweeps the member's sessions that are over.
- **Upload.** "Upload" makes a record, `pending`, and answers a page whose form carries a link
  presigned for a `PUT` of `videos/<id>`, with the content type signed. The browser puts the file
  there itself (`upload.js`, a dozen lines that `fetch` the link and then post the next form),
  and posts "uploaded". The site then asks the store with a `HEAD` and answers that request only
  when the store has: `found` makes the video `ready`; `missing`, an error or no answer in time
  leaves it `pending`, to check again from the channel. The site never carries video bytes.
- **Watch.** The page's `<video>` has a link presigned for a `GET`, signed when the request
  arrived: `arrive` writes the time into the request, so the time is in the journal and the
  link is the same on replay. Links are signed in the bridge's `encode`, with the deployment's
  credentials; the system holds none.
- **Delete** takes the record out at once and then deletes the object, sent again on an error or
  a timeout up to `maxAttempts`, and again at every start; one given up on is logged
  (`Out.orphan`).
- **Pages** are server-rendered with Lanes' templates. Every form that changes something carries
  a token bound to the session (`Auth.formToken`) and must come from the site's origin; the style
  sheet and the script are served by the bridge, since templates refuse inline code.
- **Ops**: `/healthz`, `/readyz`, `/metrics` and the access log (`ServerConfig.ops`); SIGTERM
  drains the requests in flight before it stops (`Server.stopOnSignal`).
- **Storage**: the journal, with a snapshot every 256 inputs. No database.

## The claims

Each is a theorem in `Videos/Proofs/`, gated in `Videos/Proofs/Axioms.lean`, and each is also
model-checked (`Videos/Check.lean`).

| Claim | Theorem |
| --- | --- |
| A private video is its owner's alone: in every run of the system, under every environment model, an output that shows one is addressed to its owner; and of every input, only in an answer to a session of the owner that let the request in when it arrived, open and not past its lifetime | `Videos.private_to_owner`, `Videos.Site.handle_private` |
| A like counts each member once: in every reachable state of the system, under every environment model, no video's likes name a member twice, so the count shown is the number of distinct likers | `Videos.likes_distinct`, `Videos.count_distinct` |
| A deleted video is never served again: once a delete is answered, no output of any later input or start shows it, however the store answers the delete (late, refused, `unknown`, never) | `Videos.Site.deleted_never_served`, `Videos.Site.Gone.run` |
| A video is shown only once the store confirmed its upload: an output that shows a video comes after an output asking the store about it under some call, and after the store's `found` to that call | `Videos.Site.listed_confirmed` (the seeded bugs off: `Config.Honest`) |
| What an output shows is a ready video of the site, and a private one only to a session of its owner that let the request in | `Videos.Site.shows_handle` |

The last three are about runs of the spec's functions, `Site.handle` and `Site.recover`, which is
what the actor runs; the first two are about the system's runs. The theorem that turns a run of
the system into the run of the spec its actor performed is not written (as for rookery).

### What the claims rest on

- **The bridge** (`Videos/Web.lean`) is tested, not proved: that a request names a member only
  through a cookie it verified, that a form needs its token, that the time is the server's
  (`bridge:` tests, and over HTTP).
- **Links handed out before a delete are the store's.** A watch link lasts six hours and an upload
  link fifteen minutes. A link signed before the delete still works until it expires or the
  store's delete lands, and an upload link used after the delete leaves an object no record
  names. A lifecycle rule on the bucket, or a second delete after the upload link expires, would
  close it.
- **The store** is as `Lanes.ObjectStore` models it, with the browser's upload as a write the
  site grants and never hears answered (`granted`), and its `HEAD` as the model's head
  (`Videos/Check.lean`).

## What is checked

`Videos/Check.lean`, run by `lake test`: two members, at most two videos and one per member, one
pending upload per member, two comments and one per member on a video, one delete in the store,
two attempts. The site beside the browsers, which
follow a script, and the object store's model, which answers each call at most once, late,
never, refused or `unknown`, and lets an upload not answered land at any moment or never; the
actor crashes and starts again anywhere. What each browser is shown is judged as it is shown.

| Scenario | States | Result |
| --- | --- | --- |
| A public video: made, checked twice, watched, liked three times, deleted, asked for during and after the delete | 736,480 | pass |
| A private video: asked for by another member, a stranger and its owner; channels, the feed, a like and a comment by another | 561 | pass |
| A video deleted while its check may be out | 237,289 | pass |
| A session past its lifetime: a private video watched inside it, asked for and liked after it, then watched in a new session | 376 | pass |
| Seeded: the browser's word taken for the upload (`trustBrowser`) | | found in 18 steps |
| Seeded: a check the store did not answer in time taken as found (`readyOnTimeout`) | | found in 21 steps |
| Seeded: sessions that never end (`lifetime := {}`) | | found in 18 steps |

Every bound holds in every state of every scenario, those of one member among them: one member's
videos (`maxOwned`) and comments on one video (`maxCommentsEach`) are bounded far below the site's
(`maxVideos`, `maxComments`), so one member cannot fill them for everyone. `capTests` checks
each at its limit, and that a video's owner takes out anyone's comment on it.

Over HTTP (`Videos/EndToEnd.lean`, 20 checks): the site as `Main` serves it, on a journal, against
the test kit of Lanes (`Lanes.Testing`): its identity provider in GitHub's shape, read by
`GitHub.read`, its fake S3, which checks every signature, the presigned links' included, and its
browser, which keeps the cookies. Three members sign in; a video is made, put
to the store through its link, checked and watched through the `<video>`'s link; likes counted
once, a comment, a forged form, another's delete; a private video seen by its owner alone; an
upload not yet in the store not listed; then the server is stopped and started again on its
journal, and the sessions, likes and comments are there, an upload begun before is checked and
listed, the feed comes a page at a time, a comment is deleted by its author or the video's owner
and by no one else, a delete
removes the video and its object, and a sign-out ends the session.

## Running it

```bash
VIDEOS_BUCKET=my-videos AWS_REGION=eu-west-1 AWS_ACCESS_KEY_ID=... AWS_SECRET_ACCESS_KEY=... \
GITHUB_CLIENT_ID=... GITHUB_CLIENT_SECRET=... \
lake exe videos 8080 videos.journal videos.secrets
```

`Main.lean` lists what it reads: `VIDEOS_URL` (the public origin, from which each provider's
redirect URI `<VIDEOS_URL>/sign-in/<google|github>/callback` is made, and `Secure` cookies when
it is `https:`), `LANES_HOST`, `LANES_IDLE_MS` and `LANES_DRAIN_MS` (as `lanes new` reads
them; SIGTERM drains for that long, `Server.stopOnSignal`), `VIDEOS_BUCKET` (or
`LANES_MEDIA_BUCKET`, as a deployment's unit sets it), `AWS_REGION`,
`VIDEOS_S3_ENDPOINT` (MinIO or LocalStack, as `http://host:port`), the `AWS_*` credentials and
each provider's client. The
bucket's CORS rules must allow `PUT` and `GET` from the site's origin with a `Content-Type`
header. For a local store, MinIO with a bucket and a CORS rule for `http://localhost:8080` will
do; over plain HTTP set nothing else, since `VIDEOS_URL` defaults to `http://localhost:<port>`.

`lake exe videosLive` runs the end-to-end flow against the bucket the same variables name, with
the provider still the test's, under keys `videos-live-<n>/` that it deletes at the end. It is
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
```

and each provider is registered with `https://<DomainName>/sign-in/<google|github>/callback`. The
stack's media bucket already allows the presigned `PUT`, `GET` and `HEAD` from
`https://<DomainName>`. The key in `videos.secrets` is made at the first start; losing it ends
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
4. **An upload's size cannot be bounded.** A presigned `PUT` signs the content type, not a
   length, and S3 takes up to 5 GB in one; a presigned `POST` with a policy
   (`content-length-range`) or multipart uploads would bound it and let large videos resume.
5. **Nothing runs in the background.** A delete the store did not answer is sent again at once,
   up to `maxAttempts`, then given up; an upload never confirmed stays `pending` until its owner
   deletes it. Retries with a backoff, a sweep of what was given up, thumbnails and transcoding
   all want a job with a deadline, and the store's own events (S3 notifications) a way in.
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

Search (no index; a scan of the list), thumbnails and transcoding (jobs and the store's events),
a CDN in front of the bucket (CloudFront's signed URLs need RSA signing, which Lanes does not
do), mail (SES speaks Signature Version 4, but there is no client), view counts (each view would
be a write), live updates (no server push), subscriptions, notifications, moderation and reports,
and a rate limit per member (`Lanes.RateLimit` exists; not used here).
