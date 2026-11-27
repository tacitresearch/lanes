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
   │                /metrics refused)              │
   └──presigned PUT and GET──▶ media bucket ◀──────┘──▶ CloudWatch: logs, metrics, alarms
                                                    └──▶ PostgreSQL (RDS), optional
```

- **One instance holds the shard.** The application is a Lanes process: its state is a journal
  and a snapshot on local disk, replayed at every start (`docs/ARCHITECTURE.md`, "Journal,
  snapshots and the disk model"). The disk is an EBS volume of its own, mounted at `/srv/lanes`,
  that outlives the instance and is snapshotted every day.
- **The load balancer** ends TLS (Lanes has no TLS server), redirects HTTP to HTTPS, sends
  traffic to the instance only once its readiness page answers 200, and answers 404 for the
  metrics page, which the application itself answers only to the machine it runs on.
- **Calls out over HTTPS** verify the server against Ubuntu's trust store, which the instance
  has (the TLS client: `docs/decisions/D67-a-tls-client-from-the-openssl-lean-ships.md`).
- **Media does not pass through the application.** The browser uploads to S3 with a presigned
  PUT and reads with a presigned GET; the application signs, S3 carries the bytes.
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
milliseconds ("What a stop does"). Nothing in the code changes for the address. A `main` of your
own reads the same variables as the template's does, or sets them in code, and ends in
`Server.stopOnSignal` rather than `Server.wait`:

```lean
  let config : Http.ServerConfig :=
    { host := "0.0.0.0", port := port.toUInt16, journal, system := "my-app 1", idle_ms := 75000 }
  let server ← (Http.serve (system {}) bridge config {} saving).block
  Lanes.block (server.stopOnSignal 15000)
```

Keep the `system` name your `main` has: a journal written under another name is refused.

The instance's security group admits that port from the load balancer only.

Then the operators' pages of `ServerConfig.ops` (`docs/decisions/D69-observability.md`), which
are what the application answers and so are set in `main`: readiness, which the load balancer
and every deploy ask; liveness; metrics, which the CloudWatch agent reads on the machine, and
which the server answers to a peer on the loopback address only ("Logs and metrics"); and the
access log on stderr, one JSON object a line, which reaches CloudWatch Logs:

```lean
    ops := { readinessPath := some "/readyz", livenessPath := some "/healthz",
             metricsPath := some "/metrics", accessLog := .stderr, requestIds := true }
```

Without them, set the stack's `HealthCheckPath` to a page that answers 200, such as `/`, and
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
| `DomainName` | | The site, such as `video.example.com`; media uploads are allowed from it |
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
| `ExistingOidcProviderArn` | empty | The account's GitHub OIDC provider, if it has one (IAM → Identity providers) |
| `ScriptRepository`, `ScriptRef`, `ScriptSha256` | `tacitresearch/lanes`, `main`, empty | Where the instance fetches `infra/app/app-instance.sh`; pin a commit and its SHA-256 |
| `SnapshotIntervalHours`, `SnapshotRetainCount` | 24, 7 | Snapshots of the journal's volume |
| `JournalSnapshotId` | empty | A snapshot to restore (see "Restore") |
| `LogRetentionDays` | 30 | How long log lines are kept |
| `AlarmEmail` | empty | Who is told when the site has no healthy target, the disk fills or the host fails |
| `MediaUser` | `true` | An IAM user for an S3 client that reads keys from the environment (see "Media") |
| `DatabaseEngine` | `none` | `postgres` adds RDS PostgreSQL (see "The database") |

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
run on another branch, a pull request or a fork cannot assume it. A repository whose OIDC subject
names repositories by id (as `tacitresearch/lanes` does, `docs/RUNNERS.md`) gives
`GitHubOwnerId` and `GitHubRepositoryId`.

## 4. The first deploy

**Actions → Deploy → Run workflow** on `main`. The workflow:

1. builds the executable with `lake build <BinaryName>` on Ubuntu 24.04 and strips it. Lean links
   its runtime (OpenSSL included) and Lanes links libsodium into it, so it needs only the C
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

The media bucket blocks public access, refuses requests without TLS, allows a presigned `PUT`,
`GET` and `HEAD` from `https://<DomainName>` (CORS, exposing `ETag`), and aborts multipart
uploads left incomplete for two days. The instance role may read and write it.

Lanes's S3 client (SigV4 and presigned URLs, in progress) reads its credentials from
`AWS_ACCESS_KEY_ID`, `AWS_SECRET_ACCESS_KEY` and `AWS_SESSION_TOKEN`, once, at start. Until it
reads the instance role's credentials from the metadata service (IMDSv2, which the instance
requires), give it a key of its own: with `MediaUser` true the stack makes an IAM user whose only
rights are the media bucket's (output `MediaUserName`); make its access key (**IAM → Users → the
user → Security credentials → Create access key**), and on the instance, as root:

```bash
sudo install -m 600 /dev/null /etc/lanes/secrets.env
sudo tee /etc/lanes/secrets.env >/dev/null <<'EOF'
AWS_ACCESS_KEY_ID=...
AWS_SECRET_ACCESS_KEY=...
AWS_REGION=us-east-1
EOF
sudo systemctl restart lanes-app
```

systemd reads the file as root and hands the values to the application; the `lanes` user cannot
read it. The key does not expire: rotate it by hand. Once the client takes the instance role,
delete the file and the key and set `MediaUser` to false. A URL presigned with the role's
credentials lasts no longer than those credentials, a few hours.

## The database

With `DatabaseEngine` `postgres`, the stack adds RDS PostgreSQL (`db.t4g.micro`, 20 GiB of gp3,
one zone, seven days of automated backups, a final snapshot when it is deleted, deletion
protection on) in two private subnets, reachable on 5432 from the instance only. Its password is
made by Secrets Manager. Before each start of the application, as root, the unit writes the
database's IPv4 address and password to `/run/lanes-app/db-address` and `/run/lanes-app/db-password`,
readable by the application only, and `/etc/lanes/app.env` gives `LANES_DB_HOST`, `LANES_DB_PORT`
and `LANES_DB_NAME` (`lanes`); the user is `lanes`. The application's `main` reads them into
the client's configuration (`Lanes/Lib/Postgres/IO/Client.lean`,
`docs/decisions/D68-postgres-protocol-in-lean.md`). That client takes an IPv4 address, not a
name, and speaks plain TCP, so the stack's parameter group turns off `rds.force_ssl`, which RDS
sets from PostgreSQL 15 on: the traffic stays inside the VPC, unencrypted. RDS may move the
database to another address (a maintenance, a replaced host); the next start of the application
reads the new one.

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
  until you restore the last snapshot into a new stack elsewhere (losing what came after it).
- **The volume fails.** EBS volumes are replicated within their zone; a lost volume is restored
  from the last snapshot.

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

Not checked: a real stack, instance, role, certificate, load balancer and its rule, Data
Lifecycle Manager policy and restore, the instance attaching its own volume (the
`ec2:SourceInstanceARN` condition) and a replaced instance taking it over; the CloudWatch agent's
Prometheus support on EC2 and the metrics it sends; the Systems Manager document, the
`ssm:resourceTag` condition on the deploy role, and the workflow as a whole; the systemd
sandboxing with a Lanes executable (`MemoryDenyWriteExecute`, `RestrictAddressFamilies` and the
rest, run as `lanes`); RDS with the Lanes PostgreSQL client; and the prices.
