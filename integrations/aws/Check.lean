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
import Tests.Durable

/-!
The AWS integration's checks, run by `lake test`: the refresh policy model-checked, and the
credentials, S3 and SES against fakes run here, the answers of Go's `net/mail` recorded in
`oracles/go/mail/answers.jsonl` replayed against the address check, botocore's CloudFront links
recorded in `oracles/botocore/cloudfront.jsonl` replayed against ours, and the run recorded against
moto's SES, `oracles/moto/ses.jsonl`, checked against the email model. Nothing calls AWS.
-/

open Tests.Durable (safely)

def main : IO UInt32 := do
  IO.println Checks.Refresh.report
  let live := (← safely "credentials" Checks.Imds.live) ++ (← safely "ses" Checks.Ses.live)
  let replayed := (← Checks.Mail.package.replay "../..") ++ (← Checks.CloudFront.package.replay "../..") ++ (← Checks.SesMoto.oracle.replayFile "../..")
  let tests := Checks.Refresh.tests ++ Checks.Imds.unitTests ++ Checks.Ses.tests
    ++ Checks.CloudFront.tests ++ replayed ++ live
  let failed := tests.filter (!·.2)
  for (name, ok) in tests do IO.println s!"{if ok then "ok  " else "FAIL"} {name}"
  IO.println s!"{tests.length - failed.length} passed, {failed.length} failed"
  return if failed.isEmpty then 0 else 1
