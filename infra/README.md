# Runners

The heavy CI jobs — the mutation gate above all (`.github/workflows/mutants.yml`: every mutant
of `scripts/mutants.py`, each a rebuild and a test run) — need more cores than GitHub's runners or a shared container
give. The recommended way is one warm EC2 machine of runners that the workflows start and stop
themselves, through GitHub's OIDC provider, with no AWS keys stored anywhere.

This project's AWS account works in **us-east-2**: the CI machine (`lanes-ci`), deploys and the
build cache. Workflows read the region from `LANES_AWS_REGION`; nothing assumes us-east-1.

## Set up (once)

1. **A GitHub token for the machine.** On GitHub: your picture, **Settings → Developer settings →
   Personal access tokens → Fine-grained tokens → Generate new token**.
   - Resource owner: `tacitresearch`. Expiration: the longest the organization allows; the
     machine stops registering runners when it expires (see "When the token expires").
   - Repository access: **Only select repositories** → `tacitresearch/lanes`.
   - Repository permissions: **Administration: Read and write** (to register runners) and
     **Contents: Read-only** (to clone the repository and fetch its setup script). Metadata:
     Read-only is added by itself. Nothing else.
   - If the organization requires approval of fine-grained tokens, an owner approves it under
     the organization's **Settings → Personal access tokens → Pending requests**.
2. **The stack.** In the AWS console, pick the region first (top right; c7a is in us-east-1,
   us-east-2, us-west-2, eu-west-1 and others), then **CloudFormation → Stacks → Create stack →
   With new resources (standard) → Choose an existing template → Upload a template file**, and
   upload `infra/lanes-ci.yaml`. Name it `lanes-ci`. Parameters:
   - `GitHubToken`: the token of step 1.
   - `ExistingOidcProviderArn`: empty, unless **IAM → Identity providers** already lists
     `token.actions.githubusercontent.com`; then its ARN (an account has at most one).
   - `ScriptRef`: `main`, once this file is on `main`; before that, the branch that has
     `infra/ec2-runner.sh`.
   - Everything else as it is (`c7a.16xlarge`, 200 GiB, one runner per 4 vCPUs, stop after 2
     idle hours).

   **Next**, **Next**, tick **I acknowledge that AWS CloudFormation might create IAM resources**,
   **Submit**. It takes a few minutes. The machine then sets itself up and warms (the toolchain and
   a first build), and stops itself two hours after its last job.
   A new account's quota of on-demand vCPUs may be below 64: **Service Quotas → Amazon EC2 →
   Running On-Demand Standard (A, C, D, H, I, M, R, T, Z) instances**, request 64 or more.
3. **The values for GitHub.** The stack's **Outputs** tab has three values. In the repository on
   GitHub, **Settings → Secrets and variables → Actions**:
   - **Variables → New repository variable**, three times: `LANES_AWS_ROLE_ARN` (output
     `RoleArn`), `LANES_AWS_INSTANCE_ID` (output `InstanceId`), `LANES_AWS_REGION` (output
     `Region`).
   - **Secrets → New repository secret**: `LANES_RUNNER_PAT`, the token of step 1. It lets the
     workflow wait until the runners are online; without it the jobs just queue until they are.
4. **Done.** **Actions → Mutants → Run workflow** runs the gate on the machine; so do the
   nightly run and pull requests labelled `mutants`. From a terminal:
   `gh workflow run mutants.yml -f shards=16`.

To take it all away: delete the stack (**CloudFormation → lanes-ci → Delete**), the three
variables and the secret, and the runners under **Settings → Actions → Runners** (GitHub also
drops runners that have been offline for 14 days).

## How it works

The role trusts a token whose subject names the repository by its ids as well as its name:
GitHub writes it `repo:tacitresearch@316370654/lanes@1472755265:ref:refs/heads/main`, so a
repository made later under the same name cannot assume the role. The stack's `GitHubOwnerId`
and `GitHubRepositoryId` are those ids; another repository's are the `repository_owner_id` and
`repository_id` claims of its tokens.

`mutants.yml` decides where to run in its first job (`.github/actions/runner`):

| Variables set | Route | Jobs run on |
| --- | --- | --- |
| `LANES_AWS_ROLE_ARN`, `LANES_AWS_REGION`, `LANES_AWS_INSTANCE_ID` | `box` | the warm machine, label `lanes` |
| `LANES_AWS_ROLE_ARN`, `LANES_AWS_REGION`, `LANES_AWS_INSTANCE_TYPE` | `fresh` | a machine launched for the run |
| `LANES_RUNNER` only | `manual` | runners someone keeps up (a label, or a JSON list such as `["self-hosted", "lanes"]`) |
| none, a fork's pull request, or **Run workflow** with `hosted` ticked | `hosted` | `ubuntu-latest` |

On the box route, `start` (on `ubuntu-latest`) assumes the role through OIDC
(`aws-actions/configure-aws-credentials`), starts the instance (waiting first if it is still
stopping), and waits until its runners are online; `build` and the shards run on `lanes`;
`verdict` collects the shards on `ubuntu-latest`; `stop` runs whatever happened before it
(`if: always()`) and stops the instance, unless another run of `ci.yml` or `mutants.yml` is
queued or under way, or one of its runners is busy: then the last run to end stops it. A run that
starts while the machine is stopping waits for it to stop and starts it again. One race remains:
a run whose `start` job passes in the second between another run's check and its stop call finds
its jobs waiting for runners; the idle shutdown does not help there, re-running does.

`ci.yml` reads only `LANES_RUNNER` and does not start the machine: it stays on GitHub's runners
unless you point `LANES_RUNNER` at runners that are up. Its jobs build once (`compile`) and then run
lint and tests (`test`), the model checks (`check`), `examples/raft-kv` and `examples/ledger` in
parallel, each restoring the build from the Actions cache. The benchmark workflow (`bench.yml`) uses the box
the same way as `mutants.yml`: its `start` and `stop` jobs are `.github/actions/box`.

On the machine (`infra/ec2-runner.sh`):

- **Runners.** One per 4 vCPUs (16 on a c7a.16xlarge), each with its own directory and work
  directory under `/opt/lanes/runners`, all labelled `lanes`, run as systemd services by the user
  `runner`. They are long-lived, not ephemeral: an ephemeral runner takes one job and needs a new
  registration for the next, and the machine is kept warm on purpose. Its jobs come only from
  this repository, and only from its own branches and pull requests (the runner action never
  picks it for a fork).
- **Warm state.** elan and the toolchain live in `/opt/lanes/elan`, shared, installed under a
  lock. The warm build lives in `/opt/lanes/shared/<key>`, where `<key>` hashes
  `lean-toolchain` and `lake-manifest.json` (`.github/actions/lean`). The checkout keeps each work directory's
  `.lake/build` between jobs (`clean: false`), so a job rebuilds only what changed since that
  runner's last job; a work directory with no build yet starts from the warm one. `sudo /opt/lanes/ec2-runner.sh warm`
  refreshes the warm build from `main`. The runners do not share Lake's artifact cache: each job
  starts an empty one in its work directory (`.github/actions/lean`), because Lake does not
  replay the warnings of a module it takes from the cache, and `--wfail` must see them.
- **Registration across stops.** The token of step 1 is kept in Secrets Manager. At every boot
  `lanes-register.service` asks GitHub which runners it knows and registers again any it has
  removed (GitHub removes runners offline for 14 days), with a registration token it makes from
  that token. So a stop, a start, a reboot, a month stopped, or a replaced instance needs nothing
  from anyone. The other design, a registration token pasted as a stack parameter, registers the
  runners once: they survive stops and reboots, but not 14 days stopped nor a replaced instance,
  and the token expires an hour after it is made, so each of those would need someone again.
- **Who can read the token.** Only root. Jobs run as `runner`, which a firewall rule keeps from
  the instance metadata service, so a job cannot take the instance's credentials and read the
  secret. The token is never on a command line. The instance accepts no inbound connections; a
  shell is **EC2 → the instance → Connect → Session Manager** (or SSH, with `KeyName` and your
  own inbound rule).
- **Safety stop.** A timer powers the machine off once no job has run for `IdleHours` (2), in
  case a `stop` job never ran.

## Choosing the instance

Lean elaborates a file on one thread, and Lake builds files in parallel; the mutation gate runs
16 shards in parallel, each rebuilding a few files and running tests. So both single-core speed
and cores count, and a runner should get 4 real cores.

| Type | vCPUs | Cores | RAM | On-demand, us-east-1 | Runners | Notes |
| --- | --- | --- | --- | --- | --- | --- |
| c7a.8xlarge | 32 | 32 | 64 GiB | about $1.64/h | 8 | AMD Genoa, 3.7 GHz, one core per vCPU |
| **c7a.16xlarge** | 64 | 64 | 128 GiB | about $3.28/h | 16 | **the default**: one shard per runner |
| c7a.24xlarge | 96 | 96 | 192 GiB | about $4.93/h | 24 | more than the gate can use |
| c7i.8xlarge | 32 | 16 | 64 GiB | about $1.43/h | 8 | Intel Sapphire Rapids; two vCPUs per core |
| c7i.16xlarge | 64 | 32 | 128 GiB | about $2.86/h | 16 | cheaper per vCPU, dearer per core |
| c7i.24xlarge | 96 | 48 | 192 GiB | about $4.28/h | 24 | |

Prices are list prices as I last knew them; check them on the EC2 pricing page, and look at the
newer c8a and c8i where your region has them. c7a gives each vCPU a whole core and runs faster
per core than c7i, so 4 vCPUs of c7a are about twice the compute of 4 of c7i at a little more
money: it is the better buy for Lean. 2 GiB per vCPU is plenty (a Lean process rarely passes
4 GiB). Graviton (c7g, c8g) should work, as elan and the runner have arm64 builds, but is untried
here.

Cost: running, a c7a.16xlarge is about $3.28 an hour; a run of the gate should take well under
an hour on it (not measured yet: it needs the machine). Stopped, only its disk is paid: 200 GiB
of gp3 is about $16 a month, plus $0.40 for the secret. The idle stop bounds a forgotten machine
at two hours.

## Security

- A public repository must never run untrusted code on a self-hosted runner: a fork's pull
  request could leave anything behind on the machine. Here a pull request from a fork always runs
  on `ubuntu-latest`, whatever the variables say, and the role cannot be assumed from one (the
  trust policy admits `repo:tacitresearch/lanes:ref:refs/heads/*` and
  `repo:tacitresearch/lanes:pull_request`, and a fork's run gets no OIDC token or secrets).
  Keep **Settings → Actions → General → Fork pull request workflows → Require approval for all
  external contributors** on as well. A merge queue's group may hold a fork's pull request, so CI
  runs it on `ubuntu-latest` too.
- What runs on the machine is code from the repository's own branches: whoever can push a branch
  can run code there, and that code can see what other jobs left in their work directories and
  in the shared build. That is the same trust as push access.
- The role can start, stop and describe instances, and the start and stop are limited to the one
  instance tagged `lanes-ci=box`. It holds no other right; nothing in GitHub holds AWS keys.

## Other routes

**A fresh machine for each run** (`fresh`; slower: each run fetches the toolchain
and builds Lanes before its first job). Set `LANES_AWS_INSTANCE_TYPE` (say `c7a.16xlarge`)
instead of `LANES_AWS_INSTANCE_ID`, and optionally `LANES_AWS_SUBNET`,
`LANES_AWS_SECURITY_GROUP` and `LANES_AWS_AMI` (Ubuntu 24.04 by default). `start` makes a
registration token with `LANES_RUNNER_PAT` (required here), launches the machine with
`infra/ec2-runner.sh` as its user data under the label `lanes-run-<run>-<attempt>`, and `stop`
terminates it and removes its runners. It powers itself off, and so terminates, after an idle
hour or six hours in all. The role then needs, in addition to the stack's policy:

```json
[
  { "Effect": "Allow", "Action": "ec2:RunInstances",
    "Resource": ["arn:aws:ec2:*:*:instance/*", "arn:aws:ec2:*:*:volume/*"],
    "Condition": { "StringEquals": { "aws:RequestTag/lanes-ci": "fresh" },
                   "StringLike": { "ec2:InstanceType": ["c7a.*", "c7i.*"] } } },
  { "Effect": "Allow", "Action": "ec2:RunInstances",
    "Resource": ["arn:aws:ec2:*::image/*", "arn:aws:ec2:*:*:subnet/*",
                 "arn:aws:ec2:*:*:network-interface/*", "arn:aws:ec2:*:*:security-group/*"] },
  { "Effect": "Allow", "Action": "ec2:CreateTags",
    "Resource": ["arn:aws:ec2:*:*:instance/*", "arn:aws:ec2:*:*:volume/*"],
    "Condition": { "StringEquals": { "ec2:CreateAction": "RunInstances" } } },
  { "Effect": "Allow", "Action": "ec2:TerminateInstances", "Resource": "arn:aws:ec2:*:*:instance/*",
    "Condition": { "StringEquals": { "aws:ResourceTag/lanes-ci": "fresh" } } },
  { "Effect": "Allow", "Action": "ssm:GetParameters",
    "Resource": "arn:aws:ssm:*::parameter/aws/service/canonical/*" }
]
```

No instance profile is needed, so no `iam:PassRole`.

**A machine you keep up yourself** (`manual`). Get a registration token (**Settings → Actions →
Runners → New self-hosted runner** shows one, or `gh api -X POST
repos/tacitresearch/lanes/actions/runners/registration-token --jq .token`; it lasts an hour),
then launch Ubuntu 24.04 with the script as user data:

```bash
TOKEN=$(gh api -X POST repos/tacitresearch/lanes/actions/runners/registration-token --jq .token)
{ echo '#!/bin/bash'
  echo "cat >/root/ec2-runner.sh <<'LANES_EOF'"; cat infra/ec2-runner.sh; echo LANES_EOF
  echo "REPO=tacitresearch/lanes TOKEN=$TOKEN bash /root/ec2-runner.sh"
} | gzip -9 >user-data.gz
aws ec2 run-instances --instance-type c7a.16xlarge \
  --image-id resolve:ssm:/aws/service/canonical/ubuntu/server/24.04/stable/current/amd64/hvm/ebs-gp3/ami-id \
  --block-device-mappings 'DeviceName=/dev/sda1,Ebs={VolumeSize=200,VolumeType=gp3}' \
  --user-data fileb://user-data.gz \
  --tag-specifications 'ResourceType=instance,Tags=[{Key=Name,Value=lanes-runners}]'
gh variable set LANES_RUNNER --body lanes      # CI and the gate now run there
```

In the console the same is **EC2 → Launch instance**: Ubuntu Server 24.04, the type, 200 GiB
gp3, and under **Advanced details → User data** the script with `REPO=... TOKEN=...` lines in
front. The token is in the user data, which processes on the machine can read for the hour it
is valid. Stop or terminate the instance in **EC2 → Instances**, and `gh variable delete
LANES_RUNNER` at once: while the variable names runners that are not there, CI waits for them.

### When the token expires

The machine's runners stay registered when the token expires, and go on taking jobs; only
registering again (after 14 days stopped, or on a new instance) fails. Make a new token as in
step 1 and put it in the secret: **Secrets Manager → the secret of the `lanes-ci` stack →
Retrieve secret value → Edit**, and in the repository secret `LANES_RUNNER_PAT`. Updating the
stack with a new `GitHubToken` works too, but resolves the Ubuntu image again and so replaces
the instance when Canonical has published a newer one; the new instance registers and warms
itself, under the old runner names, and `LANES_AWS_INSTANCE_ID` must then be set to the new
`InstanceId`.

## What has not been checked

None of this could run where it was written: that container has no AWS credentials, and its
network reaches neither the GitHub API nor Claude's installer. Checked: the workflows with
`actionlint` (and `shellcheck` on their scripts); the template with `cfn-lint`; the scripts with
`bash -n` and `shellcheck`; the runner download against the real release (v2.338.2, its
SHA-256, a wrong SHA-256 refused); the parsing of the checksum out of a release body in the
published format; the registration logic, the start and stop logic and the shared-packages step
against stubs of GitHub, AWS and the runner. Not checked: a real stack, instance, OIDC role,
runner registration, start and stop; the `aws-cli` snap and Secrets Manager call on the
instance; Claude Code's installer (`https://claude.ai/install.sh`, the one its documentation
gives) and Remote Control (`claude remote-control`, as its documentation describes it) on a
machine of your own; and how long the gate takes on the box.
