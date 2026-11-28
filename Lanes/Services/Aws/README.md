# AWS

Status: SES is **checked: model plus oracle**; the role credentials, SQS and CloudFront are
**client only** (`docs/decisions/D74-aws-integration.md`, `docs/decisions/D113-service-models.md`).
Its tests are in `Tests/Aws/`.

| Part | Client | Model | Oracle | Status |
| --- | --- | --- | --- | --- |
| Role credentials | `IO/Credentials.lean`, from the metadata service (IMDSv2, `Imds.lean`) or a container's endpoint, refreshed by the proved machine `Refresh.lean` | None of the service; the refresh is model-checked against a model of the metadata service in the test (`Tests/Aws/Refresh.lean`) | None: fakes of the metadata service and of a container's endpoint, written from AWS's documentation (`Tests/Aws/Imds.lean`) | client only |
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
