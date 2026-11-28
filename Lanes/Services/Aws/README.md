# AWS

Status: **checked**, but for the role credentials, which are **experimental**
(`docs/decisions/D74-aws-integration.md`). Its tests are in `Tests/Aws/`.

| Part | Client | Model | Oracle | Status |
| --- | --- | --- | --- | --- |
| Role credentials | `IO/Credentials.lean`, from the metadata service (IMDSv2, `Imds.lean`) or a container's endpoint, refreshed by the proved policy `Refresh.lean` | The refresh is model-checked against a model of the metadata service (`Tests/Aws/Refresh.lean`) | None: fakes of the metadata service and of a container's endpoint, written from AWS's documentation (`Tests/Aws/Imds.lean`) | experimental |
| SES | `Ses.lean`, `IO/Ses.lean` | Email, `Lanes/Outside/Effects/Email.lean` | moto's SES (`oracles/moto/ses.jsonl`); the address check against Go's `net/mail` (`oracles/go/mail`) | checked |
| SQS | `Sqs.lean`: the calls, with no handler yet | The queue, `Lanes/Outside/Queue.lean` | moto's SQS (`oracles/moto/sqs.jsonl`) | checked |
| CloudFront | `CloudFront.lean`: signed URLs and cookies, pure | None: no service is called | botocore's `CloudFrontSigner` (`oracles/botocore/cloudfront.jsonl`) | checked |

moto is an emulator, not AWS; `oracles/moto/run.sh` runs it, and CI runs that nightly.
