# Services

What a particular vendor needs (`docs/decisions/D110-volatile-actors.md`, "The environment, in
three layers"). Each service is a folder here, in the same Lake package as the core, with a
README that names its client, its model and its oracle, and says which of two it is
(`docs/decisions/new-service-models.md`):

- **checked: model plus oracle**: a client, a model of the service built from a shape of the
  core (`Lanes/Outside/`), and an oracle that checks the model against the real service or an
  emulator (`oracles/README.md`). A service is checked when an application's proof depends on
  how it behaves.
- **client only**: a client with tests, and no model of its own. It may still be paired with a
  shape of the core when an application needs it.

| Service | What it is | Status |
| --- | --- | --- |
| `Lanes/Services/Postgres/` | PostgreSQL's client, and the typed store's driver | checked: model plus oracle |
| `Lanes/Services/S3/` | S3, for any S3-compatible store: calls, multipart and browser uploads | checked: model plus oracle |
| `Lanes/Services/Aws/` | AWS: SES; role credentials, SQS's calls, CloudFront's signed links | SES checked: model plus oracle; the rest client only |
| `Lanes/Services/Oidc/` | Sign-in presets: Google and GitHub | client only |
| `Lanes/Services/Stripe/` | Payments in the shape of Stripe's PaymentIntent | checked: model plus oracle, with the client and the oracle still owed |

The rules:

- A service imports the core; the core never imports a service (lint `layering`,
  `LanesCli/Layers.lean`).
- `import Lanes` leaves the services out. A program imports the services it calls
  (`import Lanes.Services.Postgres`), and Lake builds only the modules a program imports, so a
  service it does not use costs it nothing. `import Lanes.Services` imports every service with
  its soundness theorems.
- A protocol (HTTP, Signature Version 4, OAuth and OpenID Connect) and a shape (a store, a queue,
  a lifecycle) are core. What only one vendor does (S3's multipart uploads, Stripe's statuses) is
  the vendor's service.
- A service's fake for tests is in its folder (`Lanes/Services/S3/Testing.lean`), and its tests
  are in `Tests/` (`Tests/Aws/`, `Tests/Oidc/`, `Tests/S3.lean`).
- A service becomes a Lake package of its own only when it brings a heavy dependency (a new C
  library, a large package) or needs its own release cadence.
