# Deploying to AWS

How to take an application from `lanes new` to a site on HTTPS on AWS, deploy it again, change
its types, back it up and restore it, and watch it. One stack makes everything
(`infra/app/lanes-app.yaml`), one script sets the machine up (`infra/app/app-instance.sh`), and
one workflow deploys (`.github/workflows/deploy-example.yml`). Why the shape is one machine and a
disk is `docs/decisions/D70-one-instance-one-volume.md`.

None of this has run on AWS yet: what has been checked, and what has not, is at the end.

## What you get

```
browser ──HTTPS──▶ load balancer ──HTTP──▶ one EC2 instance ──▶ /srv/lanes: the journal (EBS)
   │               (ACM certificate,        (systemd: the app,       │
   │                /readyz checks,          as user `lanes`)        └─ snapshots (DLM)
   │                /metrics refused)              ├──▶ backup bucket: the journal's segments
   └──signed POST, PUT, GET──▶ media bucket ◀──────┘──▶ CloudWatch: logs, metrics, alarms
                                                    └──▶ PostgreSQL (RDS), optional
```

- **One instance holds the shard.** The application is a Lanes process: its state is a journal
  and a snapshot on local disk, replayed at every start (`docs/ARCHITECTURE.md`, "Journal,
  snapshots and the disk model"). The disk is an EBS volume of its own, mounted at `/srv/lanes`,
  that outlives the instance and is snapshotted every day, and the journal is shipped to a
  backup bucket as it is written ("The journal shipped to S3").
- **The load balancer** ends TLS (Lanes has no TLS server), redirects HTTP to HTTPS, sends
  traffic to the instance only once its readiness page answers 200, and answers 404 for the
  metrics page, which the application itself answers only to the machine it runs on.
- **Calls out over HTTPS** verify the server against Ubuntu's trust store, which the instance
  has (the TLS client: `docs/decisions/D67-a-tls-client-from-the-openssl-lean-ships.md`).
- **Media does not pass through the application.** The browser uploads to S3 with a form under
  a signed policy that bounds its size (`POST`), or by parts with presigned `PUT`s, and reads with
  a presigned GET; the application signs, S3 carries the bytes.
- **Deploys** build the executable on GitHub, put it in a release bucket under its commit, and
  have the instance fetch it, check its SHA-256, switch to it and restart, through Systems
  Manager. No AWS key is stored in GitHub, and the instance takes no connection but the load
  balancer's.

## Before you start

- An AWS account, a region (each region has its prices; `us-east-1` is the cheapest of the
  large ones), and in that account the right to create IAM roles.
- A domain you control, and either a Route 53 hosted zone for it (then the stack makes the
  certificate and the DNS record by itself) or access to its DNS (you add two records by hand).
- The application in a GitHub repository, made with `lanes new` (`README.md`, "Quick start").
- On your machine, nothing more: the build happens on GitHub. To try the systemd unit's command
  line locally, `infra/app/smoke.sh` needs a built executable.

## 1. Make the application deployable

The `main` that `lanes new` writes reads where to listen and how to stop from the environment,
and the unit sets it (`infra/app/app-instance.sh`): `LANES_HOST=0.0.0.0`, since the load balancer
cannot reach `127.0.0.1`, the default; `LANES_IDLE_MS=75000`, longer than the load balancer keeps
an idle connection (60 s), so that the application never closes a connection the load balancer
is about to reuse, which the client would see as a `502`; and `LANES_DRAIN_MS`, `DrainSeconds` in
milliseconds ("What a stop does"). Nothing in the code changes for the address. The unit's
environment file also gives the site's origin, `LANES_URL=https://<DomainName>`, from which an
application that signs in or checks that a form comes from its own site makes its redirect URIs
and its `Secure` cookies (`docs/TUTORIAL-WEB.md`, step 6). A `main` of your own reads the same
variables as the template's does, or sets them in code, and ends in `Server.stopOnSignal` rather
than `Server.wait`:

```lean
  let config : Http.ServerConfig :=
    { host := "0.0.0.0", port := port.toUInt16, journal, system := "my-app 1", idle_ms := 75000 }
  let server ← (Http.serve (system {}) bridge config {} saving).block
  Lanes.block (server.stopOnSignal 15000)
```

Keep the `system` name your `main` has: it is the version of the step functions, and a journal
written under another name is refused. The gate's settings (`ServerConfig.gate`) are not part of
it: the journal holds only the requests the gate admitted, so it is read behind any gate. A
journal written while the gate was an actor of the system is refused, saying why
(`Lanes/Web/Http/JournalName.lean`).

The instance's security group admits that port from the load balancer only.

Then the operators' pages of `ServerConfig.ops` (`docs/decisions/D69-observability.md`), which
are what the application answers and so are set in `main`, as the `main` of `lanes new` sets
them: readiness, which the load balancer and every deploy ask; liveness; metrics, which the
CloudWatch agent reads on the machine, and which the server answers to a peer on the loopback
address only ("Logs and metrics"); and the access log on stderr, one JSON object a line, which
reaches CloudWatch Logs:

```lean
    ops := { readinessPath := some "/readyz", livenessPath := some "/healthz",
             metricsPath := some "/metrics", accessLog := .stderr, requestIds := true }
```

A `main` without them sets the stack's `HealthCheckPath` to a page that answers 200, such as `/`, and
`MetricsPath` to nothing. Every check is then a request the journal keeps: about one every five
seconds from the load balancer's nodes, which a snapshot cuts if the application gives `serve` its
`saving`.

The journal's path comes from the command line (`[port] [journal]`, as `lanes new` writes `main`).
A file the application keeps beside it, such as rookery's secrets, goes in the journal's
directory: `{data}` in `AppArguments`. That directory is the only one the application may write.

## 2. The stack

In the AWS console, pick the region (top right), then **CloudFormation → Stacks → Create stack
→ With new resources (standard) → Upload a template file**, upload `infra/app/lanes-app.yaml`,
and name the stack after the application. The parameters:

| Parameter | Default | What it is |
| --- | --- | --- |
| `AppName` | | Lowercase name: tags, log groups `/lanes/<AppName>`, the release prefix |
| `BinaryName` | | The executable as the lakefile names it |
| `AppArguments` | `{port} {journal}` | The executable's arguments: `{port}`, `{journal}` (`/srv/lanes/journal/<AppName>.journal`), `{data}` (its directory) |
| `AppPort` | 8080 | The port it listens on, on `0.0.0.0` (`LANES_HOST`) |
| `HealthCheckPath` | `/readyz` | Asked by the load balancer and by each deploy |
| `MetricsPath` | `/metrics` | Scraped on the machine, 404 from the internet; empty for none |
| `DrainSeconds` | 15 | How long a stop waits for the requests in flight (`LANES_DRAIN_MS`), and the target group's deregistration delay; systemd's stop timeout is ten more |
| `DomainName` | | The site, such as `video.example.com`: the application is told `LANES_URL=https://<it>`, and media uploads are allowed from it |
| `CertificateArn` | empty | An ACM certificate in this region, or empty to make one |
| `HostedZoneId` | empty | The domain's Route 53 zone: the certificate and the record are then made for you |
| `InstanceType` | `t3.small` | x86-64, Nitro; see "Choosing the instance" |
| `JournalVolumeSize` | 20 | GiB of gp3 for the journal; it can grow, not shrink |
| `RootVolumeSize` | 20 | GiB for the system, the releases and the logs |
| `ImageId` | empty | A fixed AMI; empty for the newest Ubuntu 24.04 (see "Updating the stack") |
| `KeyName` | empty | An EC2 key pair, optional: Session Manager gives a shell |
| `VpcCidr` | `10.80.0.0/16` | The VPC's addresses |
| `ReleaseBucket`, `ReleasePrefix` | empty | An existing bucket and prefix to share; empty to make a bucket, prefix `AppName` |
| `GitHubRepository` | | `owner/name` of the application's repository |
| `GitHubOwnerId`, `GitHubRepositoryId` | empty | Only if your repository's OIDC subject names repositories by id |
| `DeployBranch` | `main` | The only branch whose runs may deploy |
| `DeployWorkflow` | `deploy.yml` | The only workflow file that may deploy, as it is on `DeployBranch` (the role checks the token's `job_workflow_ref`) |
| `ExistingOidcProviderArn` | empty | The account's GitHub OIDC provider, if it has one (IAM → Identity providers) |
| `ScriptRepository` | `tacitresearch/lanes` | The repository the instance fetches `infra/app/app-instance.sh` from |
| `ScriptRef`, `ScriptSha256` | | The commit of that script and its SHA-256, both required (below) |
| `SnapshotIntervalHours`, `SnapshotRetainCount` | 24, 7 | Snapshots of the journal's volume |
| `JournalSnapshotId` | empty | A snapshot to restore (see "Restore") |
| `BackupVersionDays` | 30 | How long the backup bucket keeps an older version of an object overwritten or deleted (see "The journal shipped to S3") |
| `LogRetentionDays` | 30 | How long log lines are kept |
| `AlarmEmail` | empty | Who is told when the site has no healthy target, the disk fills or the host fails |
| `MediaUser` | `false` | `true` for an IAM user, for an S3 client that reads a key from the environment (see "Media") |
| `MailIdentity` | empty | An SES identity the instance may send email from (see "Email") |
| `DatabaseEngine` | `none` | `postgres` adds RDS PostgreSQL (see "The database") |
| `DatabaseCaBundleSha256` | the bundle's of 2026-10-14 | The SHA-256 of RDS's bundle of authorities, which the instance fetches (see "The database") |

The script sets the machine up as root, at the first boot and at each `configure`, so the stack
names it by a commit, never a branch, and by its hash, and the instance runs no other: a script
whose SHA-256 differs is refused before it runs. Take both from a commit you have read, such as
the release of Lanes the application builds with:

```bash
git rev-parse HEAD                      # ScriptRef
sha256sum infra/app/app-instance.sh     # ScriptSha256, the first field
```

To move the instance to a newer script, update the stack with the new pair and run the document's
`configure`.

**Next**, **Next**, tick **I acknowledge that AWS CloudFormation might create IAM resources**,
**Submit**. Without `HostedZoneId`, the stack waits on the certificate: **Certificate Manager →
the certificate → Domains** shows a CNAME record, which you add at your DNS; and once the stack
is done, point `DomainName` at the output `LoadBalancerDns` (a CNAME). It takes ten minutes or
so. The instance then sets itself up (`/var/log/lanes-setup.log`, also in the log group) and
waits for its first release; until then the load balancer has no healthy target.

## 3. GitHub

Copy `.github/workflows/deploy-example.yml` into the application's repository, under the same
directory, as `deploy.yml`, and set its `app-dir` default to `.`. Then, in the repository,
**Settings → Secrets and variables → Actions → Variables → New repository variable**:
`LANES_DEPLOY`, the stack's output `GitHubVariable` (one line of JSON: the role, the region, the
release location, the document and the readiness URL). Without it the workflow does nothing.

The deploy role trusts tokens for `repo:<owner>/<name>:ref:refs/heads/<DeployBranch>` only: a
run on another branch, a pull request or a fork cannot assume it. It also checks the token's
`job_workflow_ref`, `<owner>/<name>/.github/workflows/<DeployWorkflow>@refs/heads/<DeployBranch>`:
another workflow of the repository, even one on that branch, cannot assume it either. A
workflow file of another name than `deploy.yml` is given as `DeployWorkflow`. AWS STS takes
GitHub's `job_workflow_ref` as a condition key only since 2026, and no real stack has checked it
("What has not been checked"): a role that refuses a run whose subject is right is the place to
look. A repository whose OIDC subject
names repositories by id (as `tacitresearch/lanes` does, `infra/README.md`) gives
`GitHubOwnerId` and `GitHubRepositoryId`.

## 4. The first deploy

**Actions → Deploy → Run workflow** on `main`. The workflow:

1. builds the executable with `lake build <BinaryName>` on Ubuntu 24.04 and strips it. Lean links
   its runtime, OpenSSL included, into it, so it needs only the C
   library (glibc 2.25 or later for `examples/counter`; the workflow checks with `ldd` that
   nothing else is needed);
2. puts it at `s3://<bucket>/<prefix>/releases/<commit>/<BinaryName>`;
3. runs the stack's Systems Manager document on the instance: `app-instance.sh deploy <commit>
   <sha256>` fetches the file, refuses it unless its SHA-256 is the one the build computed,
   points `/opt/lanes/current` at it (a rename, so it is never missing), keeps the old target as
   `/opt/lanes/previous`, restarts the unit and asks `http://127.0.0.1:<port><HealthCheckPath>`
   for up to 180 s; if it never answers 200, it switches back and fails;
4. asks `https://<DomainName><HealthCheckPath>` through the load balancer until it answers 200,
   for `ready-seconds` (180); if it does not, it runs the document's `rollback` and fails;
5. writes `<prefix>/current`, the commit and SHA-256, which a new instance starts by itself.

The first build fetches Lanes's dependencies, Mathlib among them (Lake clones every package of
the manifest, though the executable needs none of the proof layer), and keeps them in the
Actions cache. Then `https://<DomainName>` is the site.

## Later deploys

The same: run the workflow. A deploy is a restart of the new executable on the same disk, so the
site is down from the old process's end to the new one's readiness: the start replays the
journal after its snapshot, a fraction of a second for a small journal. Releases are kept on the
instance (the newest five, and the current and previous ones), so a rollback fetches nothing:
**Systems Manager → Run Command → Run a command → the stack's document**, `Action` `rollback`,
the instance. `Action` `configure` reads the stack's configuration again and rewrites the units,
after a stack update.

To run a command on the instance, **EC2 → the instance → Connect → Session Manager**:
`sudo systemctl status lanes-app`, `sudo journalctl -u lanes-app`, `ls -l /opt/lanes`.

## Changing a persisted type

A release whose state or message types changed reads the old version's files through an upgrade
(`docs/decisions/D66-a-migration-carries-the-kernel-across.md`, `examples/migration`): the start
replays the old files with the old step functions, migrates the kernel, and saves it under the
new version. Nothing else is needed from the deploy: it is a restart of the new executable on the
same disk, and readiness answers 200 once the migration is done, so `ready-seconds` must cover
it.

What changes is the rollback. After a migration the files carry the new version, and the
previous executable refuses them (it leaves them as they are, so nothing is lost, but it does
not start). Switching back the link then leaves the site down. So before a deploy that migrates,
snapshot the journal's volume (**EC2 → Volumes → the volume tagged `lanes-journal` → Actions →
Create snapshot**). To go back after it: deploy forward with a fix, or restore that snapshot and
then roll back, losing what the new version wrote.

## Backups and restore

Data Lifecycle Manager snapshots the volume tagged `lanes-journal=<AppName>` every
`SnapshotIntervalHours` and keeps `SnapshotRetainCount` (snapshots are incremental: each costs
what changed since the one before). A snapshot is crash-consistent: it holds what a loss of power
at that moment would leave on the disk. That is what a Lanes start is built for: a journal cut at
any byte opens and gives the entries written before the cut (`Journal.open?_cut`), and dying
anywhere in an append or a save leaves files that load as the kernel the shard had
(`Journal.Disk.Holds.append_crash`, `Journal.Disk.Holds.save_crash`); that ext4 and EBS behave as
the disk model says is trusted (`TRUSTED.md`). So a restore is a start: a volume made from the
snapshot, mounted, and the journal replayed on it. What was written after the snapshot is lost.

**Restore** on the same stack:

1. **EC2 → Snapshots**, filter on the tag `lanes-snapshot` = `<AppName>`, and copy the id of the
   one to restore.
2. Update the stack (**CloudFormation → the stack → Update → Use existing template**) with
   `JournalSnapshotId` set to it. CloudFormation makes a new volume from the snapshot, keeps the
   old one (`UpdateReplacePolicy: Retain`), and names the new one in the instance's tag
   `lanes-journal-volume`.
3. Reboot the instance (**EC2 → the instance → Instance state → Reboot**). At boot
   `lanes-volume.service` attaches the volume the tag names and mounts it; a volume made from a
   snapshot is never formatted.
4. When the site is right, detach and delete the old volume (it still has the `lanes-journal`
   tag, so it is still snapshotted until then). To undo, set `JournalSnapshotId` back and reboot.

A stack in another zone or region from a snapshot is a new stack with `JournalSnapshotId` (copy
the snapshot to that region first); it gets new buckets, so the media must be copied or pointed
at. It has not been tried.

A copy of production restored into staging must not act for production. Start it the first time
with `Journal.Store.restored` set: the outputs the files owe are marked handed over and not
handed over, and the journal takes a new id, so no output of the copy has the id of one of
production's (`TRUSTED.md`, the journal's files). Jobs in flight in the copy are attempted again
when their deadlines pass, by staging's workers and with staging's credentials. Leave it unset
for the starts after: each start with it drops what the shard owes.

### The journal shipped to S3

The volume's snapshots are a day apart, so a lost volume or zone loses up to a day. Shipping the
journal makes that seconds. The stack makes a backup bucket (output `BackupBucketName`), and the
unit names it to the application as `LANES_BACKUP_BUCKET`. The application ships its journal
there as it writes it (`Journal.Store.ship`, `Lanes/Durable/Ship.lean`), after Litestream:

- The journal is written and synced on the volume as before, and no request waits for S3.
- What is written is sealed into segments: when 4096 entries wait, when the first of them has
  waited 10 seconds, and at each save, when the segment ends with the save's mark and the
  snapshot is shipped after it. Each object is put once, under
  `backups/<journal id>/segment/<first>-<stop>-<SHA-256>` or
  `backups/<journal id>/snapshot/<mark>-<SHA-256>`, with `If-None-Match: *`, so it is never
  written twice. The journal's id is in its `.id` file (`docs/decisions/D105-output-ids.md`).
- A put that fails is tried again, after 200 ms, doubling to a minute. At most 256 uploads wait;
  one more drops the oldest that is not being put, a new snapshot replaces one still waiting,
  and the process logs each failure.
- A restart ships what the journal file holds and the shipper had not yet stored (the file
  `.shipped` beside the journal says how far it got), and the snapshot again, which S3 refuses as
  there already. A stop waits up to 5 seconds for what is pending (`Ship.Config.close_ms`).

So a lost volume loses what was written in the last 10 seconds or so, and more while S3 is
unreachable. What S3 has is what the journal had: every segment holds the entries at the
positions its name gives (`Journal.Ship.Holds.put`). All of these are fields of
`Journal.Ship.Config`.

In `main`, with the role's credentials as in "Media", the stack's region (`us-east-2` here) and
the bucket from the environment:

```lean
  let creds ← Aws.Credentials.start (← Aws.Credentials.detect)
  let backups : S3.Bucket :=
    { name := "<LANES_BACKUP_BUCKET>", region := "us-east-2",
      endpoint := S3.Endpoint.aws "us-east-2" }
  let ship := S3.backup backups creds.source "backups/"
  let config : Http.ServerConfig := { journal, system := "my-app 1", ship := some ship }
```

The instance role may put and get objects under `backups/` and list them; it may not delete
them. The bucket is versioned, so an object overwritten or deleted by anything else is kept for
`BackupVersionDays`. Nothing expires the current objects: a restore needs the newest snapshot,
which a quiet application may not have replaced for a long time.

**Restore to a point** on a new volume, or anywhere: start the application's executable once
with no journal at its path and call, before `serve`,

```lean
  let restored ← Http.restoreJournal (system {}) bridge config ship .latest
```

with `.position n` (the history's first `n` entries) or `.time t` (what S3 had stored by `t`,
in nanoseconds from the epoch) for an earlier point, and the journal's id as the last argument
when the bucket holds several (by default, the one written last). It lists the journal's
objects, picks the newest snapshot at or before the point with an unbroken run of segments after
it, checks each object against the SHA-256 in its name, and writes the journal and the snapshot.
It refuses to write over a journal or a snapshot that is there. A start from the files it
writes has the state the journal had at that point (`Journal.Restore.journal_restores`). The
copy is a restore under D105: its journal ends with a `handed` mark and it has no `.id`, so its
first start hands nothing over and takes a new id, and it ships under that id. A point in a gap
that a dropped upload left is refused; `.latest` gives the furthest that can be reached.

## Logs and metrics

The application's stdout and stderr go to journald (`journalctl -u lanes-app`), and
`lanes-log.service` copies its lines unchanged to `/var/log/lanes/app.log`, which the CloudWatch
agent sends to the log group `/lanes/<AppName>`, one stream per instance; the setup log goes to
the same group. The access log is JSON, so **CloudWatch → Logs Insights** reads its fields:

```
fields @timestamp, method, path, status, duration_ms, request_id
| filter ispresent(status) and status >= 500
| sort @timestamp desc
```

```
filter ispresent(duration_ms)
| stats count(*) as requests, pct(duration_ms, 50) as p50, pct(duration_ms, 99) as p99 by bin(5m)
```

The agent also sends, to the namespace `Lanes/<AppName>`, the disk used on `/` and on
`/srv/lanes` and the memory used, and, with a metrics page, reads it every minute (the
Prometheus support of the CloudWatch agent) and sends the gauges and counters as metrics: in
flight, connections, the inbox's depth, ready, connections refused, journal appends, entries and
saves, and requests by status class. The latency histogram is not sent (each bucket would be a
metric of its own); latency comes from the access log, as above. The load balancer's own metrics
(`AWS/ApplicationELB`: requests, `5xx`, target response time, healthy hosts) are there without
anything set.

The server answers the metrics page only to a peer on a loopback address
(`OpsConfig.metricsAccess`, `.loopback` by default; `Http.Ops.route?_metrics`), which the agent,
on the instance, is. A request from anywhere else at that path, however it is written, is
answered `404` as if there were no page. That is what keeps the page from the internet. The load
balancer's rule that answers 404 at `MetricsPath` stays, as a second guard, but it matches the
path as the client wrote it while the server matches it after decoding percent-escapes, so on its
own it would let `/%6Detrics` by. To scrape from another machine, set `metricsAccess := .token
"<secret>"` and send `Authorization: Bearer <secret>`, or `.anyone` where nothing else reaches
the port.

Alarms, with `AlarmEmail`: no healthy target for three minutes, the journal's disk over 80%, and
the host failing AWS's status checks, which also recovers the instance onto other hardware (it
keeps its id, its addresses and its volumes) whether or not an address is given.

## Media

The media bucket blocks public access, refuses requests without TLS, allows a form's `POST` and
a presigned `PUT`, `GET` and `HEAD` from `https://<DomainName>` (CORS, exposing `ETag`, which a
browser reads from each part it puts), and aborts multipart uploads left incomplete for two
days. The instance role may read and write it. The unit gives
the application the bucket's name and its region in `/etc/lanes/app.env`, as
`LANES_MEDIA_BUCKET` and `AWS_REGION`; `/etc/lanes/secrets.env`, read after it, may set either
again.

The S3 client (`Lanes/Web/IO/S3.lean`) reads its credentials from a source at every call
(`SigV4.Source`). The default path is the instance role's credentials, which the AWS integration
(`integrations/aws`, `docs/decisions/D74-aws-integration.md`) fetches from the metadata service
with IMDSv2, as the instance requires, and fetches again five minutes before they expire. Nothing
is stored on the instance and nothing needs rotating. Require the package in the application's
lakefile (`path` or `git`, as `examples/sign-in` requires Google's and GitHub's), and in `main`:

```lean
  let creds ← Aws.Credentials.start (← Aws.Credentials.detect)
  let media : S3.Bucket :=
    { name := "<LANES_MEDIA_BUCKET>", region := "<AWS_REGION>",
      endpoint := S3.Endpoint.aws "<AWS_REGION>" }
  -- In the handler of the system's outputs:
  S3.handler port media creds.source {} rt out
```

A URL presigned with the role's credentials lasts no longer than those credentials, a few hours
at most, whatever its `Expiry`.

An upload form or a presigned link signed in the bridge, which is pure, is signed with
credentials the bridge is given once, at start; the role's expire within hours, so such an
application, as the tutorial's shelf and `examples/videos` are, needs a key that lasts. It reads
`AWS_ACCESS_KEY_ID`, `AWS_SECRET_ACCESS_KEY` and `AWS_SESSION_TOKEN` (`S3.credentialsFromEnv`,
once, at start), and the key is the media user's: with `MediaUser` true
the stack makes an IAM user whose only rights are the media bucket's (output `MediaUserName`);
make its access key (**IAM → Users → the user → Security credentials → Create access key**), and
on the instance, as root:

```bash
sudo install -m 600 /dev/null /etc/lanes/secrets.env
sudo tee /etc/lanes/secrets.env >/dev/null <<'EOF'
AWS_ACCESS_KEY_ID=...
AWS_SECRET_ACCESS_KEY=...
EOF
sudo systemctl restart lanes-app
```

systemd reads the file as root and hands the values to the application; the `lanes` user cannot
read it. The key does not expire: rotate it by hand, or move to the instance role and then
delete the file and the key and set `MediaUser` to false.

## Email

With `MailIdentity` set to an identity verified in SES in the stack's region (a domain, such as
`videos.example`, or an address), the instance role may call `ses:SendEmail` from that identity
and no other, and `/etc/lanes/app.env` gives `LANES_MAIL_IDENTITY`. The AWS integration's SES
adapter (`Aws.Ses`, SES API v2's `SendEmail`) sends a message with the same credentials:

```lean
  let mail := Aws.Ses.Endpoint.aws "<region>"
  -- In the handler of the system's outputs:
  Aws.Ses.handler port mail creds.source {} rt out
```

`Aws.Ses.handlerOnce` takes the output's id as well (`Runtime.startWith`, `Http.serveFronted`)
and a state opened with `Aws.Ses.Once.open` on a file beside the journal: an output handed over
again after a restart is then not sent again, and is answered `unknown`.

Verify the identity first (**Amazon SES → Identities → Create identity**; a domain takes DNS
records, which Route 53 can add). A new account is in SES's sandbox: it sends only to verified
addresses, at most 200 messages a day, until you ask AWS for production access (**Amazon SES →
Account dashboard → Request production access**). SES takes no idempotency key, so a send whose
answer never came may have been sent: resending it may send it twice (the decision on the AWS
integration).

## The database

With `DatabaseEngine` `postgres`, the stack adds RDS PostgreSQL (`db.t4g.micro`, 20 GiB of gp3,
one zone, seven days of automated backups, a final snapshot when it is deleted, deletion
protection on) in two private subnets, reachable on 5432 from the instance only. Its password is
made by Secrets Manager. Before each start of the application, as root, the unit writes the
password to `/run/lanes-app/db-password`, readable by the application only. `/etc/lanes/app.env`
gives `LANES_DB_HOST` (the endpoint's name), `LANES_DB_PORT`, `LANES_DB_NAME` (`lanes`),
`LANES_DB_USER` (`lanes`), `LANES_DB_PASSWORD_FILE` and `LANES_DB_CA`, beside `AWS_REGION`.

The application's `main` connects with one line:

```lean
  let db ← Postgres.Client.fromEnv
```

`Postgres.Client.fromEnv` (`Lanes/Lib/Postgres/IO/Client.lean`) reads libpq's variables
(`PGHOST`, `PGPORT`, `PGUSER`, `PGPASSWORD` or `PGPASSFILE`, `PGDATABASE`, `PGSSLMODE`,
`PGSSLROOTCERT`, `PGCHANNELBINDING`), then the deploy's `LANES_DB_*`. On the instance it
connects to the endpoint by name, over TLS, checks RDS's certificate against the bundle the
instance installed, and binds SCRAM to that certificate. Each new connection resolves the name
again, so it follows RDS to a new address after a failover or a maintenance; the pool
(`Postgres.Pool`, `Lanes/Lib/Postgres/IO/Pool.lean`) closes a connection that broke and opens a
new one. On a developer's machine the same line reaches `localhost` without TLS. A setting can be
changed after: `{ (← Postgres.Client.fromEnv) with timeout_ms := 5000 }`.

What the client does by default (`SslMode.defaultFor`, `Lanes/Lib/Postgres/Settings.lean`):

| Host | TLS |
| --- | --- |
| `localhost`, `127.0.0.0/8`, `::1` | none, unless `PGSSLMODE` or `sslmode` asks for it |
| any other address or name | required; the certificate must chain to the authorities and be for the host's name; SCRAM is bound to it when the server offers `SCRAM-SHA-256-PLUS` |

The authorities are `PGSSLROOTCERT`, else `LANES_DB_CA`, else `/etc/lanes/db-ca.pem` when it is
there, else the system's. `PGSSLMODE` `allow` and `prefer`, which give TLS up when the server
refuses it, are refused.

AWS adds authorities to RDS's bundle from time to time (for new regions). Setup and `configure`
then stop with `does not have the SHA-256`, and the bundle installed before is kept: update the
stack's parameter `DatabaseCaBundleSha256` to the new bundle's SHA-256, after checking it as
below.

**For auditors.** The stack's parameter group sets `rds.force_ssl` to 1 and
`password_encryption` to SCRAM. At setup and at each `configure`, the instance fetches RDS's
global bundle of authorities,
`https://truststore.pki.rds.amazonaws.com/global/global-bundle.pem`, checks that it has the
SHA-256 of `DatabaseCaBundleSha256`, and installs it as `/etc/lanes/db-ca.pem` (`LANES_DB_CA`);
a bundle with another hash is refused. The application trusts every authority in that file and
no other. To check a new bundle, `curl -fsSL <url> | sha256sum` gives its hash, and
`openssl crl2pkcs7 -nocrl -certfile global-bundle.pem | openssl pkcs7 -print_certs -noout`
lists its authorities. Channel binding (`SCRAM-SHA-256-PLUS`) means that a party in the middle
with a certificate from one of the bundle's authorities is refused by the server; a client that
could have bound and was not offered it says so, and a server that did offer it then refuses it,
so the binding cannot be stripped. `docs/decisions/D83-postgres-over-tls.md` says why.

## What a stop does

systemd stops or restarts the application with SIGTERM, and kills it ten seconds after
`DrainSeconds` (`TimeoutStopSec`). The `main` of `lanes new` ends in `Server.stopOnSignal`: at
SIGTERM or SIGINT readiness answers `503` (`Server.drain`), the requests the shard has taken are
answered as they finish, for at most `LANES_DRAIN_MS`, and then `Server.stop` answers the ones
left `503`, closes the connections, and `main` returns 0 (`infra/app/smoke.sh` shows status 0).

- **Requests in flight are answered** if they finish within the drain, and `503` if not. While
  it drains the server goes on serving: on one instance there is no other target, and the load
  balancer sends requests until its health checks have seen readiness fail.
- **The data is safe in any case.** The runtime is crash-only (rule 3.3): every answer leaves
  only after the entries that produce it are synced (`Batch.run_sound`), and a start mends what a
  death left. A kill, by systemd at the timeout or by a second SIGTERM during the drain, is a
  start like any other. Its requests in flight are dropped and the load balancer answers them
  `502`; one whose input was journalled before the kill may have taken effect though its client
  saw `502` (rule 3.4: a request that may be retried needs an id, D48).
- **A `main` that waits with `Server.wait`** installs no handler, and Lean's runtime installs none
  for SIGTERM, so SIGTERM's default action ends it at once, as a kill (smoke: status 143).

A drain lets the requests in flight finish; on one instance it does not keep the site up while
the process restarts, since there is no other target to send new requests to.

## Availability: what one instance means

There is one instance, so there is one copy of the running application.

- **A deploy, a restart or a crash** is a gap of seconds: the process ends, the new one replays
  the journal and listens. Requests then get `502`.
- **The instance dies or its host fails.** systemd restarts a process that dies (`Restart=always`);
  the recovery alarm moves an instance whose host fails AWS's checks to other hardware with the
  same volumes, in minutes. While it is gone the load balancer has no healthy target and answers
  `502` or `503`; EBS keeps the journal, and nothing that was answered is lost.
- **The instance is replaced** (a new image, a stack update that needs it): the new instance
  boots, waits until the old one has let go of the volume, attaches it and starts the current
  release. A few minutes without the site.
- **The zone fails.** The volume is in one zone; the site is down until the zone comes back, or
  until you restore into a new stack elsewhere: from the backup bucket, losing the last seconds,
  or from the last snapshot, losing what came after it.
- **The volume fails.** EBS volumes are replicated within their zone; a lost volume is restored
  from the backup bucket, or from the last snapshot.

## Choosing the instance

A shard runs its actors on one thread (`docs/ARCHITECTURE.md`), so one fast core matters more
than many; the server's connections use four threads more (`ServerConfig.ioThreads`). Media
bytes do not pass through the instance. `t3.small` (2 vCPUs, 2 GiB) is enough to start; a t3
earns CPU credits and in its default unlimited mode is charged for sustained use beyond them, so
for a steady load prefer `m7a.medium` or `c7a.large`. Each batch of requests is one `fsync` on
EBS, which takes on the order of a millisecond: the journal's write rate, not the CPU, bounds a
small instance (`README.md`, "Performance").

## Costs

A rough month in `us-east-1` at list prices as last known, 730 hours, for the defaults, little
traffic and no database. Check the AWS pricing pages; prices differ by region.

| Item | Assumption | A month |
| --- | --- | ---: |
| EC2 `t3.small` | on demand, within its CPU credits | $15.20 |
| EBS gp3 | 20 GiB root + 20 GiB journal, $0.08 a GiB | $3.20 |
| EBS snapshots | a few GiB changed over the seven kept, $0.05 a GiB | under $1 |
| Load balancer | $0.0225 an hour, and about one LCU at $0.008 | $22.30 |
| Public IPv4 addresses | the instance's and the load balancer's two, $0.005 an hour each | $10.95 |
| CloudWatch | 1 GiB of logs, about 15 metrics, 3 alarms | $5.30 |
| Route 53 | one hosted zone, if used | $0.50 |
| S3, Systems Manager, DLM, ACM, the VPC and its S3 endpoint | releases are small; the rest is free | about $0 |
| **Total** | | **about $58** |

Not in it: media storage ($0.023 a GiB a month) and, above all, what reaching it costs: data out
to the internet is about $0.09 a GiB after the first 100 GiB a month, so a terabyte of video
watched is about $80; a CDN (CloudFront) in front of the media bucket is cheaper per GiB at that
scale and is not part of this stack. The database adds about $14.40 (`db.t4g.micro` $11.70, 20
GiB $2.30, the secret $0.40). A larger instance is the main lever: `m7a.medium` about $42,
`c7a.large` about $75.

## Updating the stack

Most parameters change in place. The configuration the instance reads (the arguments, the port,
the paths) is a Systems Manager parameter: after an update, run the document's `configure`. Two
things replace the instance: `KeyName`, and a new image. With `ImageId` empty, CloudFormation
reads Canonical's newest Ubuntu 24.04 at every update, so any update after Canonical publishes
one replaces the instance (a few minutes without the site, as above). After the first deploy, put
the output `ImageId` in the parameter; Ubuntu's unattended upgrades patch the system in place, and
a kernel update waits for a reboot you choose.

Deleting the stack keeps the journal's volume, the media bucket, the release bucket, the
database's final snapshot and its secret.

## Not covered

- **More than one instance.** One shard is one process on one disk; there is no second copy to
  fail over to, no autoscaling, and no blue/green or rolling deploy, since two versions cannot
  hold one journal at once (the journal's lock refuses a second process). Lanes can run shards in
  several processes joined by TCP (`docs/ARCHITECTURE.md`, "Composition"), and
  `examples/raft-kv` replicates a store across nodes; neither is deployed by this stack.
- **Graviton.** The template allows x86-64 only; an arm64 build and instance are untried.
- **A CDN, a WAF, load balancer access logs, private subnets with a NAT gateway.** Each is a
  stack change of its own.

## What has not been checked

Nothing here could run where it was written: that container has no AWS credentials. Checked:
the template with `cfn-lint` (no error, warning or informational finding, in three regions); the
scripts and the workflow's scripts with `shellcheck` and `actionlint`; the rendered units with
`systemd-analyze verify` (systemd 255, as on Ubuntu 24.04); the CloudWatch agent's configuration
as JSON and the Prometheus configuration as YAML; `infra/app/smoke.sh` against `examples/counter`
built from this branch, with the unit's environment (it starts in the journal's directory,
answers, writes its journal there, drains at SIGTERM and exits with status 0, and starts again on
the same journal); the counter with the operators' pages on, on `0.0.0.0`, answering on an
address other than loopback, where the metrics page is `404` written plainly or percent-encoded
and readiness answers, while on loopback the page is served; and deploy, rollback,
the refusal of a wrong SHA-256 and the rollback of a release that never becomes ready, with
stubs of `aws` and `systemctl`.

Not checked: the deploy role's condition on `job_workflow_ref` against a real token; the AWS integration on an instance (the role's credentials fetched from the
metadata service from inside the unit's sandbox, refreshed, and used by S3), SES with a verified
identity and the `ses:SendEmail` grant, and the stack with `MediaUser` false and `MailIdentity`
set; a real stack, instance, role, certificate, load balancer and its rule, Data
Lifecycle Manager policy and restore, the instance attaching its own volume (the
`ec2:SourceInstanceARN` condition) and a replaced instance taking it over; the CloudWatch agent's
Prometheus support on EC2 and the metrics it sends; the Systems Manager document, the
`ssm:resourceTag` condition on the deploy role, and the workflow as a whole; the systemd
sandboxing with a Lanes executable (`MemoryDenyWriteExecute`, `RestrictAddressFamilies` and the
rest, run as `lanes`); RDS with the Lanes PostgreSQL client; shipping the journal to a real S3, and the backup
bucket's policy (the shipper and restores are checked against the test kit's fake S3 and
against moto: `Tests/Ship.lean`, `Tests/Oracle/Service/S3Backup.lean`); and the prices.
