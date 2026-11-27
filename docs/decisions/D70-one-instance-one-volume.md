# D70. An application is deployed as one instance with its journal on a volume of its own, behind a load balancer

A Lanes application is a process that holds a shard: a journal and a snapshot on local disk,
replayed at every start (D24, D29), and a lock beside them so that only one process writes them.
Its state is the disk. The reference deployment on AWS (`infra/app/lanes-app.yaml`,
`docs/DEPLOY.md`) is shaped by that: one EC2 instance runs the process, the journal is on an EBS
volume that is not the instance's, an application load balancer ends TLS in front, and media goes
from the browser to S3 without passing through the process.

## The shape

- **One instance, one shard.** The process is the only writer of its journal, so there is one
  of it. A second instance would need a second shard, joined by the transport (D30), or a
  replicated system (`examples/raft-kv`); either is an application's design, not a deployment's.
- **The journal on a volume of its own.** A gp3 volume made by the stack, kept when the stack is
  deleted or the volume replaced, never deleted with the instance, and found by the instance at
  every boot from its tag. The instance attaches it to itself (it may attach that volume, to
  itself only), so a replaced instance waits until the old one lets go, takes it and starts the
  current release, with no one acting. A restore is a new volume from a snapshot named in the
  same tag and a reboot.
- **Snapshots are the backup.** An EBS snapshot is crash-consistent, the state a loss of power
  leaves; a Lanes start is built for exactly that state (`Journal.open?_cut`,
  `Journal.Disk.Holds.append_crash`), so no quiescing, no agent and no application hook is needed.
- **Crash-only on the machine too.** systemd restarts the process whenever it ends; the unit
  needs the mounted volume and starts in the journal's directory, which exists only on it, so a
  missing volume stops the start rather than letting the application begin an empty journal.
- **Deploys are a restart on the same disk.** The release is fetched, checked by SHA-256, and a
  link switched; a changed type is read through an upgrade (D66). A rollback switches the link
  back, which works until a migration has rewritten the files.
- **Media skips the process.** Presigned URLs keep video bytes off the shard's thread, off the
  journal and off the instance's network.

## Why not the alternatives

- **ECS on Fargate.** A task's disk is ephemeral and goes with the task; Fargate attaches EBS
  only as a volume made at the task's start (from a snapshot, at best), so the journal would be
  restored, not kept, at every deploy and every task replacement, and writes since the last
  snapshot lost. EFS is a network file system: each `fsync` is a round trip, the throughput of an
  application that syncs every batch falls with it, and that NFS behaves as the disk model
  assumes (an append stops at a byte, a rename is atomic) is a larger trust than a local ext4. A
  rolling deploy also starts the new task before the old stops, and the journal's lock would
  refuse it.
- **ECS on EC2.** Possible, with a host volume and placement pinned to one instance; it is this
  design with a scheduler and an agent added, and the scheduler's strengths (packing, rolling
  replacement) do not apply to one stateful task.
- **Lambda.** No local disk that lasts beyond an invocation, no long-lived process to hold a
  shard, timers and connections, and concurrent invocations would be concurrent writers.
- **App Runner, Elastic Beanstalk.** The first has no persistent disk; the second is EC2 with
  conventions that assume stateless instances behind an autoscaling group.
- **The default VPC.** Its subnets are parameters a template cannot read the zone of without a
  custom resource, and the volume must be in the instance's zone; the load balancer needs two
  zones and the database a subnet group. A VPC of its own costs nothing, has no NAT gateway (the
  instance has a public address and admits only the load balancer), and is deleted with the stack.
- **A static key for deploys.** GitHub's OIDC provider and a role that may only put releases
  under one prefix and run one Systems Manager document on instances tagged for the application,
  as `infra/lanes-ci.yaml` does for CI. The document's parameters are patterns (a commit, a
  SHA-256), so the role cannot run an arbitrary command.

## What it costs

One instance is one failure domain: a deploy is seconds without the site, a lost host minutes (the
recovery alarm moves it), a lost zone until the zone returns or a snapshot is restored elsewhere.
`docs/DEPLOY.md` says so under "Availability". The design makes that cost explicit rather than
hiding it behind a scheduler that cannot remove it for a single writer.

Not done: SIGTERM ends a Lanes process at once, as SIGKILL would (no handler is installed), so a
stop drops the requests in flight. The data is safe (rule 3.3). A drain, SIGTERM then
`Server.drain`, then `Server.stop` once nothing is in flight or a deadline passes, is proposed in
`docs/DEPLOY.md`, and the unit's stop timeout and the target group's deregistration delay are
already sized for it.

*Amendment: a stop drains.* The `main` of `lanes new` ends in `Server.stopOnSignal`, which at
SIGTERM drains for up to `LANES_DRAIN_MS` and exits 0; the unit sets it to `DrainSeconds`, and
the address and the idle time with `LANES_HOST` and `LANES_IDLE_MS`, so a deployment needs no
change to `main` but its operators' pages (`docs/DEPLOY.md`, "What a stop does").
