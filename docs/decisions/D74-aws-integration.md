# D74. AWS as an integration: a role's credentials refreshed by a proved policy, and SES as the email model

Status: Partly superseded by new-volatile-actors.md (AWS as a Lake package under `integrations/`: it is `Services/Aws`)

The reference deployment runs the application on one EC2 instance with a role
(`docs/decisions/D70-one-instance-one-volume.md`), but the S3 client read keys only from the
`AWS_*` variables, once, at start (`docs/decisions/D71-s3-and-signature-version-4.md`), so the
stack made an IAM user whose long-lived key was copied onto the instance. D71 left the role's
credentials to an AWS integration because they expire and must be fetched again, which wants a
policy with a deadline, and because the endpoints are AWS's alone. The video site also needs to
send mail, and D65 models an email API with no adapter for one. This adds `integrations/aws`, a
package as D61 and D72 lay them out, with both, and changes `Lanes/` in one place.

## A source of credentials, read at each call

`S3.exchange` and `S3.handler` take a `SigV4.Source` (`Lanes/Web/IO/S3.lean`): an `IO` action
read at every call, which gives the credentials to sign with or none, and then nothing is sent
and the call is answered `unknown`. A fixed value is a source (`Source.fixed`, and a coercion,
so code that passed credentials compiles unchanged). Nothing in `Lanes/` knows where a source's
credentials come from: the instance's role is the integration's, and so is SES, which takes the
same source.

## The refresh policy is a pure machine

`Aws.Refresh.step` (`integrations/aws/Aws/Refresh.lean`) decides everything: when to fetch, what
an answer or a timeout does, and which credentials may be handed out. Every message carries the
clock's reading, so the machine has no clock; a fetch is an `Rpc.Call` with a deadline, answered
with the credentials or `unknown`, as D65's models of services are. Its configuration:
`margin_ms` (fetch this long before expiry; five minutes), `jitter_ms` (and up to this much
earlier, drawn by the edge; a minute), `skew_ms` (hand nothing out this close to expiry; a
minute), `deadline_ms` (ten seconds), and a backoff from `backoff_ms` doubling to
`maxBackoff_ms` (one second to a minute). `Config.Valid` is the condition under which the
refresh can win: `deadline_ms + skew_ms < margin_ms`.

Proved, with an axiom gate (`integrations/aws/Aws/Axioms.lean`):

- `current_fresh`: what is handed out is held and good for more than `skew_ms` after now; with
  `current_answered`, it is a credential an answer gave. Expired credentials are never handed
  out, whatever the clock, the service and the order of messages.
- `refresh_in_time`: credentials held, the next fetch due at `w` no later than the margin before
  they expire: ticked at `w`, the machine fetches; until the fetch's deadline the old ones are
  handed out; and an answer by then, with credentials of more than the margin, is handed out
  from that moment and leaves the machine in the same shape, so by induction the edge that ticks
  when asked, against a service that answers in time, never lacks credentials once it has some.
  `accept_due` is the step that sets the next fetch at the margin, and `tick_early` says a tick
  before it changes nothing.
- `backoff_le` and `retry_within`: the wait between failed fetches never passes
  `maxBackoff_ms`, and a fetch given up or answered `unknown` is tried again within it, and not
  at once. The credentials held are kept and handed out while they last.

Credentials good for less than the margin are held but count as a failure for the backoff, so a
service that keeps answering the same credentials near their expiry (the metadata service gives
new ones at least five minutes before) is not asked in a loop.

Model-checked first (`integrations/aws/Checks/Refresh.lean`, rule 5.1): the machine as an actor,
restarted empty after a crash as a process is, against `Rpc.outside` of a metadata service that
answers each fetch once with credentials it issues (some good for less than the margin),
`unknown`, late or never, and a clock that reads any time from the last on. Every reachable state
of the small instance satisfies the four properties above, 2.4 million states in about ten
seconds; a service that always answers within the deadline, with a clock that never passes the
wake asked for, never leaves the machine without credentials once it has some; and with the
margin shorter than the deadline and the skew the checker finds the moment without them.

## The edge only performs

`Aws/IO/Credentials.lean` is a task that reads the wall clock, ticks the machine, makes the fetch it
says and tells it the answer with a jitter it draws, then sleeps until the wake or a second,
whichever is sooner, so a clock that jumps is seen within a second. The state is a pure value in
a reference; `Provider.source` reads it at each call. A failure's reason is kept
(`Provider.failure`), and holds no value.

Where the credentials are is `Aws/Imds.lean`, pure: the calls of each source in turn and what
each answer means (`Flow.call`, `Flow.next`), and the JSON both sources answer
(`readCredentials`).

- **IMDSv2** (`Source.instance`): `PUT /latest/api/token` with a time to live of six hours, then
  the role's name and its credentials with the token. IMDSv1 is never used, so an instance that
  requires tokens, as `infra/app/lanes-app.yaml` makes it, answers; a container behind a hop
  limit of one does not reach it, which is the hop limit's purpose.
- **A container's endpoint** (`Source.container`, `containerSource?`): ECS's
  `AWS_CONTAINER_CREDENTIALS_RELATIVE_URI` under `169.254.170.2`, or
  `AWS_CONTAINER_CREDENTIALS_FULL_URI`, over plain HTTP only to loopback, `169.254.170.2` or
  EKS Pod Identity's `169.254.170.23` (as AWS's SDKs allow), with the token of
  `AWS_CONTAINER_AUTHORIZATION_TOKEN` or the file `_TOKEN_FILE` names. It cost one call and the
  same reader, so it is here. `Credentials.detect` takes it when the environment names one.

Not here: the `AWS_*` variables (they stay `S3.credentialsFromEnv`'s), profiles and
`~/.aws/credentials`, SSO, `AssumeRole` and web identity through STS, and IPv6 endpoints
(`[fd00:ec2::254]`), which the HTTP client cannot reach.

## SES, as D65's email model says

`Aws/Ses.lean`: SES API v2's `SendEmail`, a JSON document posted to
`email.<region>.amazonaws.com/v2/email/outbound-emails` and signed for the service `ses` with the
same `SigV4.sign` as S3. A message is a sender, one to 50 recipients (SES's limit), a subject
without a line break, and a text body, an HTML body or both (`Body`, so a message without one
cannot be built). Lanes has no mail address code; `Address.of?` takes a dot-atom local part of
ASCII and a domain of two LDH labels or more, without display names, comments or quoted local
parts, which covers the site's mail and refuses anything that could carry a header. Proved: the
body is JSON that reads back as the document (`json_parse`, from `Json.parse_compress`), and the
recipients read from it are exactly those given, in order (`toAddresses_json`).

How the answers map onto `Lanes.Email` (`Answer.modelled`, `modelPort`):

- `200` with a `MessageId`: `made (message id) accepted`.
- A `4xx` (`MessageRejected`, `MailFromDomainNotVerifiedException`, `AccountSuspendedException`,
  `SendingPausedException`, `TooManyRequestsException`, `BadRequestException`, a signature
  refused): SES did not send it, so `made (unsent call) rejected`, the message named by the call
  that sent it, since SES gives it no id. A throttled message is rejected in the model's terms
  (not sent); the adapter's own answer keeps the code, so a system can retry it.
- A `5xx`, a `200` without a `MessageId`, or no answer by the deadline: `unknown`. A `500` from
  an AWS API may or may not have been executed.

**Idempotency.** SES takes no idempotency key. D65 wrote that for such an API "a resend may send
the message twice, which the model does not describe"; it does describe it, as a request without
a key, which `Idempotent.server` gives a slot of its own each time it is sent. So the adapter's
calls carry no key, by type (`modelPort` maps every call to `key := none`), and the model counts
each send as a message SES may have sent: a resend after `unknown` may send twice, and
`Effects.at_most_once` does not apply. A system that must not send a mail twice must not resend
after `unknown`; one that may (a notification) can. Webhooks (SES's event destinations through
SNS or EventBridge) are not wired, so the model's `sent`, `delivered` and `bounced` are never
reported here.

## Checked, without AWS

`integrations/aws/Check.lean`, run by `lake test` and CI's examples job:

- The model checks above.
- The answers AWS documents (the EC2 and ECS documentation's JSON, as remembered: neither could be
  fetched here), and the calls of each source.
- A fake metadata service in the test, which refuses a request without a token, names one role,
  and issues new credentials at each fetch that expire in four seconds: the provider fetches at
  once with a token, again before expiry, and is never without credentials meanwhile; after
  three `500`s it backs off and recovers; with nothing listening it has none and says why. A
  container's endpoint that checks its token gives credentials, and refuses a wrong token.
- The S3 client with the provider's credentials against Lanes's fake S3 (`Tests/S3.lean`), which
  checks each signature and the session token from the bytes it received; its check now takes
  the scope, so the fake SES uses it for `ses`.
- A fake SES that checks each signature, reads the recipients from the JSON and answers a
  `MessageId`, `MessageRejected`, a `500` or nothing; a forged secret and a missing token are
  refused. A system sending through `Ses.handler` records a run that `Ses.outside`, the email
  model, allows (`Outside.allows`), and the model refuses the run with an answer given twice.

## The stack

`infra/app/lanes-app.yaml` makes the instance role the default path: `MediaUser` is `false` by
default, kept for a client that reads `AWS_*`, and `MailIdentity` (empty by default) grants the
role `ses:SendEmail` on that identity only. `app-instance.sh` writes the region, and the identity
when there is one, to `/etc/lanes/app.env`. `docs/DEPLOY.md` says how.

## Not done, and not verified

- Nothing here has run against AWS. Not verified: that IMDS and ECS answer as documented
  (the shapes are remembered, the fakes are written from them); that a token's time to live of
  six hours and a `PUT` with hop limit one work from the systemd unit's sandbox; SES's error
  names and the header that carries them; that SES v2 accepts the document as written; the
  `ses:SendEmail` grant on an identity ARN; the stack with `MediaUser` false.
- SES's event webhooks, attachments and raw messages, templates, configuration sets, and
  display names in addresses.
- The credentials are in memory only: a restart fetches again, which takes one round trip.

## For the owner

- Whether `SigV4.Source` should live in `Lanes/Web/IO/S3.lean`, as here, or a module of its own
  once a second client in `Lanes/` uses it.
- Whether SES's `TooManyRequestsException` should be `rejected` in the model (not sent) or a
  refusal of its own: the email model has no "try again later".
- Whether the integration's `Checks` should import Lanes's `Tests.S3` for the fake's signature
  check, as here, or the check should move into `Lanes/` as a pure `SigV4.verify` with theorems.
