/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes
public import Lanes.Services.Aws
public import Lanes.Services.Aws.CloudFrontSound
public import Lanes.Services.Aws.SesSound
public import Lanes.Services.Oidc
public import Lanes.Services.Postgres
public import Lanes.Services.Postgres.ConnSound
public import Lanes.Services.Postgres.MessageSound
public import Lanes.Services.S3
public import Lanes.Services.S3.PostSound
public import Lanes.Services.Stripe

/-!
Every service, with its soundness theorems (`Lanes/Services/README.md`). `import Lanes` leaves
the services out: an application imports the ones it calls, such as `Lanes.Services.Postgres`,
and Lake builds only those. A service imports the core; the core never imports a service (lint
`layering`).
-/
