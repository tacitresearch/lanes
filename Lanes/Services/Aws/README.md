# AWS

Status: SES is **checked: model plus oracle**; the role credentials, SQS and CloudFront are
**client only** (`docs/decisions/D74-aws-integration.md`, `docs/decisions/D113-service-models.md`).
Its tests are in `Tests/Aws/`.

| Part | Client | Model | Oracle | Status |
| --- | --- | --- | --- | --- |
| Credentials | `IO/Credentials.lean`: keys in the environment, else a container's endpoint, else the metadata service (IMDSv2), in the SDKs' order (`Imds.chain`); a role's refreshed by the proved machine `Refresh.lean` | None of the service; the refresh is model-checked against a model of the metadata service in the test (`Tests/Aws/Refresh.lean`) | None: fakes of the metadata service and of a container's endpoint, written from AWS's documentation (`Tests/Aws/Imds.lean`) | client only |
| SES | `Ses.lean`, `IO/Ses.lean` | Email, `Lanes/Outside/Effects/Email.lean` | moto's SES (`oracles/moto/ses.jsonl`); the address check against Go's `net/mail` (`oracles/go/mail`) | checked: model plus oracle |
| SQS | `Sqs.lean`: the calls, with no handler yet | None of its own; paired with the core's queue shape, `Lanes/Outside/Queue.lean` | The pairing against moto's SQS (`oracles/moto/sqs.jsonl`, `Tests/Aws/SqsMoto.lean`) | client only |
| CloudFront | `CloudFront.lean`: signed URLs and cookies, a pure signing function | None: no service is called | Tested against botocore's `CloudFrontSigner` (`oracles/botocore/cloudfront.jsonl`) | client only |

## Sending an email once

SES takes no idempotency key, so a send made again may send the message twice. An email that
must be sent once is a job of an outbox (`Lanes/Db/Jobs.lean`), written in the transaction that
causes it, and sent by the outbox's worker (`Lanes/Db/Worker.lean`) through `Ses.perform`, with
`Ses.classify` reading the answer. Each attempt is numbered by the job's id and lease
(`Ses.jobPort`); the id is not sent, since SES has nothing that would dedupe by it.

- With `attempts_max := 1` and no period, each email is sent at most once. The claim that takes
  a job counts its one attempt, and every later claim fails the job instead of taking it again
  (`Jobs.Config.claimed`, `Queue.claim_attempts`). This rests on the database, not on SES. The
  cost: an attempt whose answer is lost, a `5xx` or throttling leaves the job failed, the email
  sent or not, and nothing tries again.
- With more attempts, an email is sent until SES takes it, and an attempt made again after a
  lost answer, a `5xx` or a restart of the worker may send it twice.

Both are model-checked beside SES's model, with crashes, a restart and lost answers
(`Tests/Worker.lean`). Instances are replaceable: what is sent is in the database, not on their
disks.

moto is an emulator, not AWS; `oracles/moto/run.sh` runs it, and CI runs that nightly.

## Running on AWS without long-lived keys

`Aws.Credentials.find` reads the environment once and returns what to sign with: keys in it
(`AWS_ACCESS_KEY_ID`, `AWS_SECRET_ACCESS_KEY`, `AWS_SESSION_TOKEN`), used as they are; else a
provider on the container's endpoint (`AWS_CONTAINER_CREDENTIALS_RELATIVE_URI` or `_FULL_URI`,
with `AWS_CONTAINER_AUTHORIZATION_TOKEN` or its `_FILE`); else a provider on the instance's
metadata service, unless `AWS_EC2_METADATA_DISABLED` is `true`. A provider fetches the role's
credentials at once and again before they expire (`Refresh.refresh_in_time`). Its
`Found.source` is what the S3 client and SES read at each call.

S3's links and forms for a browser are signed with the credentials of the moment, their session
token included, by `S3.presignNow` and `S3.Post.formNow`, where IO runs (an `arrive`, a
handler). Each lasts as long as asked or until those credentials expire, whichever is sooner
(`S3.expiryWithin_le`), since S3 refuses a request signed with credentials that have expired.
With the defaults of `Refresh.Config`, a role's credentials are replaced five to six minutes
before they expire, so a link signed just before that lasts at least that long. A pure bridge,
given credentials once at start, still needs keys that do not expire (#188). CloudFront's
signed links are signed with a key pair of CloudFront's, not with a role, and need none of this.

Not taken from the environment: profiles (`~/.aws/credentials`, `AWS_PROFILE`), SSO, and STS's
`AssumeRole` and `AssumeRoleWithWebIdentity` (EKS's IRSA); EKS Pod Identity comes through the
container's endpoint.
