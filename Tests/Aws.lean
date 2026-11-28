/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Aws.Refresh
import Tests.Aws.Imds
import Tests.Aws.Ses
import Tests.Aws.CloudFront
import Tests.Aws.SqsMoto
import Tests.Live

/-!
The AWS service's tests, run by `lake test`: the refresh policy model-checked, and the
credentials and SES against fakes run here. Nothing calls AWS. Its oracles are with the others:
Go's `net/mail` and botocore's CloudFront links (`Tests/Oracle/All.lean`), and moto's SES and SQS
(`Tests/Oracle/Service/All.lean`).
-/

namespace Checks

open Tests.Live (safely)

def tests : List (String × Bool) :=
  Refresh.tests ++ Imds.unitTests ++ Imds.chainTests ++ Ses.tests ++ CloudFront.tests ++ SqsMoto.unitTests

def live : IO (List (String × Bool)) :=
  return (← safely "credentials" Imds.live) ++ (← safely "ses" Ses.live)

end Checks
