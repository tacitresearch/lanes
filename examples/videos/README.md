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
  time one signs in. A session is a signed cookie and an entry of the member's `Auth.Sessions`.
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
- **Ops**: `/healthz`, `/readyz`, `/metrics` and the access log (`ServerConfig.ops`).
- **Storage**: the journal, with a snapshot every 256 inputs. No database.

## The claims

Each is a theorem in `Videos/Proofs/`, gated in `Videos/Proofs/Axioms.lean`, and each is also
model-checked (`Videos/Check.lean`).

| Claim | Theorem |
| --- | --- |
| A private video is its owner's alone: in every run of the system, under every environment model, an output that shows one is addressed to its owner; and of every input, only in an answer to a live session of the owner | `Videos.private_to_owner`, `Videos.Site.handle_private` |
| A like counts each member once: in every reachable state of the system, under every environment model, no video's likes name a member twice, so the count shown is the number of distinct likers | `Videos.likes_distinct`, `Videos.count_distinct` |
| A deleted video is never served again: once a delete is answered, no output of any later input or start shows it, however the store answers the delete (late, refused, `unknown`, never) | `Videos.Site.deleted_never_served`, `Videos.Site.Gone.run` |
| A video is shown only once the store confirmed its upload: an output that shows a video comes after an output asking the store about it under some call, and after the store's `found` to that call | `Videos.Site.listed_confirmed` (the seeded bugs off: `Config.Honest`) |
| What an output shows is a ready video of the site, and a private one only to its owner's live session | `Videos.Site.shows_handle` |

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
- **The store** is as `Lanes.ObjectStore` models it, with the browser's upload as a put the site
  hands out and never hears answered, and a `HEAD` as its get (`Videos/Check.lean`).

## What is checked

`Videos/Check.lean`, run by `lake test`: two members, at most two videos, one pending upload per
member, one comment, one delete in the store, two attempts. The site beside the browsers, which
follow a script, and the object store's model, which answers each call at most once, late,
never, refused or `unknown`, and lets an upload not answered land at any moment or never; the
actor crashes and starts again anywhere. What each browser is shown is judged as it is shown.

| Scenario | States | Result |
| --- | --- | --- |
| A public video: made, checked twice, watched, liked three times, deleted, asked for during and after the delete | 741,759 | pass |
| A private video: asked for by another member, a stranger and its owner; channels, the feed, a like and a comment by another | 561 | pass |
| A video deleted while its check may be out | 240,716 | pass |
| Seeded: the browser's word taken for the upload (`trustBrowser`) | | found in 18 steps |
| Seeded: a check the store did not answer in time taken as found (`readyOnTimeout`) | | found in 21 steps |

Over HTTP (`Videos/EndToEnd.lean`, 18 checks): the site as `Main` serves it, on a journal, with a
provider of the test's (a token endpoint and a user API, as GitHub's) and Lanes' fake S3, which
checks every signature, the presigned links' included. Two members sign in; a video is made, put
to the store through its link, checked and watched through the `<video>`'s link; likes counted
once, a comment, a forged form, another's delete; a private video seen by its owner alone; an
upload not yet in the store not listed; then the server is stopped and started again on its
journal, and the sessions, likes and comments are there, an upload begun before is checked and
listed, the feed comes a page at a time, comments are deleted by their author only, a delete
removes the video and its object, and a sign-out ends the session.

## Running it

```bash
VIDEOS_BUCKET=my-videos AWS_REGION=eu-west-1 AWS_ACCESS_KEY_ID=... AWS_SECRET_ACCESS_KEY=... \
GITHUB_CLIENT_ID=... GITHUB_CLIENT_SECRET=... \
lake exe videos 8080 videos.journal videos.secrets
```

`Main.lean` lists what it reads: `VIDEOS_URL` (the public origin, from which each provider's
redirect URI `<VIDEOS_URL>/sign-in/<google|github>/callback` is made, and `Secure` cookies when
it is `https:`), `VIDEOS_HOST`, `VIDEOS_BUCKET`, `AWS_REGION`, `VIDEOS_S3_ENDPOINT` (MinIO or
LocalStack, as `http://host:port`), the `AWS_*` credentials and each provider's client. The
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

Then on the instance, `/etc/lanes/secrets.env` (DEPLOY.md, "Media") holds, besides the media
user's `AWS_ACCESS_KEY_ID`, `AWS_SECRET_ACCESS_KEY` and `AWS_REGION`:

```bash
VIDEOS_BUCKET=<the stack's MediaBucketName output>
VIDEOS_URL=https://<DomainName>
VIDEOS_HOST=0.0.0.0
GOOGLE_CLIENT_ID=...       # and/or GITHUB_CLIENT_ID
GOOGLE_CLIENT_SECRET=...
```

and each provider is registered with `https://<DomainName>/sign-in/<google|github>/callback`. The
stack's media bucket already allows the presigned `PUT`, `GET` and `HEAD` from
`https://<DomainName>`. The key in `videos.secrets` is made at the first start; losing it ends
every session, nothing else.

## Findings

What Lanes made harder than it should be is the report of this example's branch; the ones that
shape the code are:

- `S3.handler` needs the system's `Runtime`, which `serveFronted` keeps private, so
  `Videos/Serve.lean` makes the call itself with `S3.exchange` and `Server.tryInput`, and holds a
  promise of the server for the outputs that come before `serveFronted` returns.
- The bridge's `encode` sees only the output, so the time a link is signed for travels through
  the system (`at_s`), written by `arrive`, and the viewer's session rides in every answer
  (`Out.reply`'s `viewer`) for the form tokens.
- The object store's model has no `HEAD` and no notion of a put the system hands to someone else;
  the check maps `HEAD` to a get and the upload link to a put of a call no one answers.
- Every page view is a request, so it enters the journal and is synced before it is answered.
- The fake S3 and the fake provider are test files of Lanes (`Tests/S3.lean`, `Tests/OAuth.lean`),
  imported from `Tests`: an application outside this repository has no such kit.
