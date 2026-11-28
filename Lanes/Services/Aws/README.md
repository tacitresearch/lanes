# AWS

Status: SES is **checked: model plus oracle**; the role credentials, SQS and CloudFront are
**client only** (`docs/decisions/D74-aws-integration.md`, `docs/decisions/new-service-models.md`).
Its tests are in `Tests/Aws/`.

| Part | Client | Model | Oracle | Status |
| --- | --- | --- | --- | --- |
| Role credentials | `IO/Credentials.lean`, from the metadata service (IMDSv2, `Imds.lean`) or a container's endpoint, refreshed by the proved machine `Refresh.lean` | None of the service; the refresh is model-checked against a model of the metadata service in the test (`Tests/Aws/Refresh.lean`) | None: fakes of the metadata service and of a container's endpoint, written from AWS's documentation (`Tests/Aws/Imds.lean`) | client only |
| SES | `Ses.lean`, `IO/Ses.lean` | Email, `Lanes/Outside/Effects/Email.lean` | moto's SES (`oracles/moto/ses.jsonl`); the address check against Go's `net/mail` (`oracles/go/mail`) | checked: model plus oracle |
| SQS | `Sqs.lean`: the calls, with no handler yet | None of its own; paired with the core's queue shape, `Lanes/Outside/Queue.lean` | The pairing against moto's SQS (`oracles/moto/sqs.jsonl`, `Tests/Aws/SqsMoto.lean`) | client only |
| CloudFront | `CloudFront.lean`: signed URLs and cookies, a pure signing function | None: no service is called | Tested against botocore's `CloudFrontSigner` (`oracles/botocore/cloudfront.jsonl`) | client only |

moto is an emulator, not AWS; `oracles/moto/run.sh` runs it, and CI runs that nightly.
