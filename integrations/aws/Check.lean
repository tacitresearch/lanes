/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Checks.Refresh
import Checks.Imds
import Checks.Ses
import Checks.Mail
import Checks.CloudFront
import Checks.SesMoto
import Checks.SqsMoto
import Tests.Durable
import Lanes.Testing

/-!
The AWS integration's checks, run by `lake test`: the refresh policy model-checked, and the
credentials, S3 and SES against fakes run here, the answers of Go's `net/mail` recorded in
`oracles/go/mail/answers.jsonl` replayed against the address check, botocore's CloudFront links
recorded in `oracles/botocore/cloudfront.jsonl` replayed against ours, and the runs recorded against
moto's SES and SQS, `oracles/moto/ses.jsonl` and `oracles/moto/sqs.jsonl`, checked against the
email and queue models. Nothing calls AWS.
-/

open Tests.Durable (safely)

def main (args : List String) : IO UInt32 := do
  unless Lanes.Testing.wantsJson args do IO.println Checks.Refresh.report
  let live := (← safely "credentials" Checks.Imds.live) ++ (← safely "ses" Checks.Ses.live)
  let replayed := (← Checks.Mail.package.replay "../..") ++ (← Checks.CloudFront.package.replay "../..") ++ (← Checks.SesMoto.oracle.replayFile "../..")
    ++ (← Checks.SqsMoto.oracle.replayFile "../..")
  let tests := Checks.Imds.unitTests ++ Checks.Ses.tests ++ Checks.CloudFront.tests
    ++ Checks.SqsMoto.unitTests ++ replayed ++ live
  Lanes.Testing.report args (Lanes.Testing.Result.tests Checks.Refresh.tests .check
    ++ Lanes.Testing.Result.tests tests)
