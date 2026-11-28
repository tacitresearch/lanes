/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Services.Aws.CloudFront
public import Lanes.Services.Aws.IO.Credentials
public import Lanes.Services.Aws.IO.Ses
public import Lanes.Services.Aws.Imds
public import Lanes.Services.Aws.Refresh
public import Lanes.Services.Aws.Ses
public import Lanes.Services.Aws.Sqs

/-!
AWS: a role's credentials, refreshed before they expire; email through SES; SQS's calls; and
CloudFront's signed links (`Lanes/Services/Aws/README.md`).
-/
