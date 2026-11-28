# Integrations

What a particular vendor needs, kept out of `Lanes/` (`docs/decisions/D61-models-of-external-systems.md`):
each is a Lake package of its own that requires Lanes by path and is checked against what the
vendor publishes, recorded or written from its documentation, never against the vendor live.

| Package | What it is | Checked against |
| --- | --- | --- |
| `google` | Sign-in with Google: its OpenID Connect provider | Its discovery document and JWK Set as recorded in `google/recorded/` |
| `github` | Sign-in with GitHub: its OAuth app, and an identity read from its user API | Answers in the shapes GitHub's documentation gives, written by hand |
| `aws` | An instance's or a container's role credentials, fetched from the metadata service (IMDSv2) or the container's endpoint and refreshed before they expire by a proved policy; email through SES; CloudFront's signed URLs and cookies | The refresh policy model-checked against a model of the metadata service; fakes of the metadata service, of a container's endpoint and of SES, written from AWS's documentation, run in the test; a run through SES checked against the email model; CloudFront's links, signatures included, against botocore's `CloudFrontSigner` |

Build and check one as an example is (`examples/README.md`): link the repository's packages into
its `.lake`, then `lake build` and `lake test`.
