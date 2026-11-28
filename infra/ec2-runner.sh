#!/bin/bash
# GitHub Actions runners for Lanes on one Ubuntu 24.04 machine: EC2 user-data, or run with sudo.
# infra/lanes-ci.yaml runs it on the warm runner machine; infra/README.md says how and why.
#
#   REPO=owner/name TOKEN=<registration token> ec2-runner.sh    # set up; safe to run again
#   REPO=owner/name TOKEN_SECRET=<secret> ec2-runner.sh         # the same, registering by itself
#   sudo /opt/lanes/ec2-runner.sh register                      # what each boot runs then
#   sudo /opt/lanes/ec2-runner.sh warm                          # warm the shared state again
#   ec2-runner.sh --fetch-runner DIR                            # only fetch and check the runner
#
# Set up installs build-essential, git, curl, python3, zstd, iptables, libssl-dev, pkg-config
# and openssl, a user `runner`, elan
# with no default toolchain, and RUNNERS runner processes (vCPUs / 4 by default), each in its own
# directory with its own work directory, labelled LABELS, registered against REPO as
# NAME-r1, NAME-r2, ..., and run as systemd services.
#
# Registration. With TOKEN, a registration token (it expires an hour after it is made), runners
# are registered once; a runner registered already is kept. With TOKEN_SECRET, the name or ARN
# of an AWS Secrets Manager secret in AWS_REGION that holds a fine-grained GitHub token with
# Administration (read and write) and Contents (read) on REPO, the machine makes its own
# registration tokens: at set up and at every boot (`register`) it registers each runner that
# is not registered, or that GitHub has removed (it removes runners offline for 14 days), so a
# stop, a start, a reboot or a long pause needs nothing from anyone. Only root reads the secret:
# the runner user, which runs the jobs, cannot reach the instance metadata service and so cannot
# take the instance's credentials.
#
# The runners are not ephemeral: an ephemeral runner takes one job and needs a new registration
# for the next, and a machine kept warm is the point.
#
# Warming (WARM=1, the default, and `warm`) clones REPO into /opt/lanes/shared/src, installs the
# toolchain of its lean-toolchain, and builds Lanes and what the mutation gate runs of
# examples/raft-kv into /opt/lanes/shared/<key>, where <key> is a hash of lean-toolchain and
# lake-manifest.json. Jobs start from that build (.github/actions/lean).
# A private REPO is cloned with CLONE_TOKEN, or with the token of TOKEN_SECRET; neither is
# stored.
#
# IDLE_HOURS (2; 0 for never) powers the machine off once no job has run for that long: an
# instance stops, or terminates if launched with --instance-initiated-shutdown-behavior
# terminate. MAX_HOURS (0, never) powers it off that long after set up, whatever runs.
set -euo pipefail

BASE=${BASE:-/opt/lanes}
# shellcheck source=/dev/null
if [ -z "${REPO:-}" ] && [ -f "$BASE/lanes.conf" ]; then . "$BASE/lanes.conf"; fi
REPO=${REPO:-}
TOKEN=${TOKEN:-}
TOKEN_SECRET=${TOKEN_SECRET:-}
AWS_REGION=${AWS_REGION:-}
RUNNERS=${RUNNERS:-}
LABELS=${LABELS:-lanes}
NAME=${NAME:-$(hostname -s)}
BRANCH=${BRANCH:-main}
WARM=${WARM:-1}
IDLE_HOURS=${IDLE_HOURS:-2}
MAX_HOURS=${MAX_HOURS:-0}
CLONE_TOKEN=${CLONE_TOKEN:-}
RUNNER_VERSION=${RUNNER_VERSION:-}
RUNNER_SHA256=${RUNNER_SHA256:-}
RUNNER_USER=runner
ELAN_DIR=$BASE/elan
# elan's release, and the SHA-256 of its archives: an installer from a branch could change.
ELAN_VERSION=v4.4.0
ELAN_SHA256_X86_64=0e8250aa2be86c7af929ade68db617af9edc8b9ccf6eaf5ece228250d0d032e2
ELAN_SHA256_AARCH64=45cde3006f82f98804c94cf2ca4949d117060a5f3cc8afa62f523759947ee21f
SHARED=$BASE/shared
API=https://api.github.com

say() { echo "ec2-runner: $*" >&2; }
die() { say "$*"; exit 1; }

runner_arch() {
  case "$(uname -m)" in
    x86_64) echo x64 ;;
    aarch64) echo arm64 ;;
    *) die "no runner for $(uname -m)" ;;
  esac
}

# The SHA-256 a release of actions/runner publishes for the Linux package of ARCH, read from the
# release's JSON on stdin; the release notes carry it between `BEGIN SHA` and `END SHA` marks.
published_sha() {
  python3 -c '
import json, re, sys
body = json.load(sys.stdin).get("body") or ""
arch = sys.argv[1]
m = re.search(rf"<!-- BEGIN SHA linux-{arch} -->([0-9a-f]{{64}})<!-- END SHA linux-{arch} -->", body)
print(m.group(1) if m else "")' "$1"
}

release_version() {
  python3 -c 'import json, sys; print(json.load(sys.stdin)["tag_name"].removeprefix("v"))'
}

# Downloads the runner package into DIR, checks it against the published SHA-256 (or
# RUNNER_SHA256), and prints its path.
fetch_runner() {
  local dir=$1 arch version sha json file
  arch=$(runner_arch)
  version=$RUNNER_VERSION
  sha=$RUNNER_SHA256
  if [ -z "$version" ] || [ -z "$sha" ]; then
    local release=latest
    [ -n "$version" ] && release="tags/v$version"
    json=$(curl -fsSL "$API/repos/actions/runner/releases/$release")
    [ -n "$version" ] || version=$(release_version <<<"$json")
    [ -n "$sha" ] || sha=$(published_sha "$arch" <<<"$json")
  fi
  [ -n "$sha" ] || die "release $version publishes no SHA-256 for linux-$arch; set RUNNER_SHA256"
  file="actions-runner-linux-$arch-$version.tar.gz"
  mkdir -p "$dir"
  if ! [ -f "$dir/$file" ] || ! echo "$sha  $dir/$file" | sha256sum -c --status -; then
    curl -fsSL -o "$dir/$file.part" \
      "https://github.com/actions/runner/releases/download/v$version/$file"
    if ! echo "$sha  $dir/$file.part" | sha256sum -c --status -; then
      rm -f "$dir/$file.part"
      die "$file does not have the SHA-256 $sha"
    fi
    mv "$dir/$file.part" "$dir/$file"
  fi
  echo "$dir/$file"
}

as_runner() {
  sudo -u "$RUNNER_USER" -H env ELAN_HOME="$ELAN_DIR" PATH="$ELAN_DIR/bin:/usr/local/bin:/usr/bin:/bin" "$@"
}

aws_cli() {
  if command -v aws >/dev/null; then aws "$@"; else /snap/bin/aws "$@"; fi
}

# The GitHub token of TOKEN_SECRET; empty without one.
github_pat() {
  [ -n "$TOKEN_SECRET" ] || return 0
  aws_cli secretsmanager get-secret-value --region "$AWS_REGION" --secret-id "$TOKEN_SECRET" \
    --query SecretString --output text
}

github_api() {
  local pat=$1 method=$2 path=$3
  # The header is read from a pipe, so that the token is in no command line.
  curl -fsSL -X "$method" -H @<(printf 'Authorization: Bearer %s\n' "$pat") \
    -H "Accept: application/vnd.github+json" -H "X-GitHub-Api-Version: 2022-11-28" "$API$path"
}

registration_token() {
  local pat=$1
  if [ -n "$TOKEN" ]; then echo "$TOKEN"; return; fi
  [ -n "$pat" ] || die "a runner is not registered, and neither TOKEN nor TOKEN_SECRET is given"
  github_api "$pat" POST "/repos/$REPO/actions/runners/registration-token" \
    | python3 -c 'import json, sys; print(json.load(sys.stdin)["token"])'
}

# The names of the runners GitHub has for REPO, one a line.
registered_names() {
  github_api "$1" GET "/repos/$REPO/actions/runners?per_page=100" \
    | python3 -c 'import json, sys; print("\n".join(r["name"] for r in json.load(sys.stdin)["runners"]))'
}

install_packages() {
  export DEBIAN_FRONTEND=noninteractive
  apt-get update -q
  apt-get install -yq build-essential git curl ca-certificates python3 zstd util-linux sudo iptables \
    libssl-dev pkg-config openssl
  if [ -n "$TOKEN_SECRET" ] && ! command -v aws >/dev/null && ! [ -x /snap/bin/aws ]; then
    snap install aws-cli --classic
  fi
}

install_elan() {
  id "$RUNNER_USER" >/dev/null 2>&1 || useradd --create-home --shell /bin/bash "$RUNNER_USER"
  mkdir -p "$BASE/runners" "$SHARED" "$ELAN_DIR"
  chown "$RUNNER_USER:" "$SHARED" "$ELAN_DIR"
  if ! [ -x "$ELAN_DIR/bin/elan" ]; then
    local target sha tmp
    case "$(uname -m)" in
      x86_64) target=x86_64-unknown-linux-gnu sha=$ELAN_SHA256_X86_64 ;;
      aarch64) target=aarch64-unknown-linux-gnu sha=$ELAN_SHA256_AARCH64 ;;
      *) die "no elan for $(uname -m)" ;;
    esac
    tmp=$(mktemp -d)
    curl -fsSL --retry 5 -o "$tmp/elan.tar.gz" \
      "https://github.com/leanprover/elan/releases/download/$ELAN_VERSION/elan-$target.tar.gz"
    echo "$sha  $tmp/elan.tar.gz" | sha256sum -c --status - \
      || die "elan $ELAN_VERSION for $target does not have the SHA-256 $sha"
    tar -xzf "$tmp/elan.tar.gz" -C "$tmp"
    chmod 755 "$tmp" "$tmp/elan-init"
    as_runner "$tmp/elan-init" -y --no-modify-path --default-toolchain none
    rm -rf "$tmp"
  fi
}

# Jobs run as the runner user; with the instance's credentials they could read TOKEN_SECRET.
# The rule does not survive a reboot, so a unit puts it back before the network is up, and each
# runner's service requires that unit: after any boot, no job runs before the rule is there.
block_metadata() {
  local rule="OUTPUT -d 169.254.169.254 -m owner --uid-owner $RUNNER_USER -j REJECT"
  # shellcheck disable=SC2086
  iptables -C $rule 2>/dev/null || iptables -A $rule
  printf '%s\n' '[Unit]' \
    "Description=Keep the Lanes runners' jobs from the instance's credentials" \
    'DefaultDependencies=no' 'Before=network-pre.target' 'Wants=network-pre.target' \
    '[Service]' 'Type=oneshot' 'RemainAfterExit=yes' \
    "ExecStart=/bin/sh -c 'iptables -C $rule 2>/dev/null || iptables -A $rule'" \
    '[Install]' 'WantedBy=sysinit.target' >/etc/systemd/system/lanes-block-metadata.service
  systemctl daemon-reload
  systemctl enable lanes-block-metadata.service
}

# The service of the runner in $1 starts only after the rule is in place, and not if it failed.
order_after_block() {
  local unit
  unit=$(cat "$1/.service")
  mkdir -p "/etc/systemd/system/$unit.d"
  printf '%s\n' '[Unit]' 'Requires=lanes-block-metadata.service' \
    'After=lanes-block-metadata.service' >"/etc/systemd/system/$unit.d/lanes.conf"
  systemctl daemon-reload
}

setup_runners() {
  local count tarball i dir name pat registered=""
  count=${RUNNERS:-0}
  [ "$count" -ge 1 ] || count=$(( $(nproc) / 4 ))
  [ "$count" -ge 1 ] || count=1
  pat=$(github_pat)
  [ -z "$pat" ] || registered=$(registered_names "$pat")
  for i in $(seq 1 "$count"); do
    dir="$BASE/runners/r$i"
    name="$NAME-r$i"
    if ! [ -x "$dir/config.sh" ]; then
      [ -n "${tarball:-}" ] || tarball=$(fetch_runner "$BASE/download")
      rm -rf "$dir"
      mkdir -p "$dir"
      tar xzf "$tarball" -C "$dir"
      [ "$i" -gt 1 ] || "$dir/bin/installdependencies.sh" >/dev/null
      chown -R "$RUNNER_USER:" "$dir"
    fi
    if [ -f "$dir/.runner" ] && [ -n "$pat" ] && ! grep -qx "$name" <<<"$registered"; then
      say "$name is no longer registered on GitHub: registering it again"
      if [ -f "$dir/.service" ]; then (cd "$dir" && ./svc.sh stop) || true; fi
      rm -f "$dir/.runner" "$dir/.credentials" "$dir/.credentials_rsaparams"
    fi
    if ! [ -f "$dir/.runner" ]; then
      (cd "$dir" && as_runner ./config.sh --unattended --replace --url "https://github.com/$REPO" \
        --token "$(registration_token "$pat")" --name "$name" --labels "$LABELS" --work _work)
    fi
    for kv in "ELAN_HOME=$ELAN_DIR" "LANES_SHARED=$SHARED"; do
      grep -qx "$kv" "$dir/.env" 2>/dev/null || echo "$kv" >>"$dir/.env"
    done
    (cd "$dir" && { [ -f .service ] || ./svc.sh install "$RUNNER_USER"; })
    order_after_block "$dir"
    (cd "$dir" && ./svc.sh start)
  done
  say "$count runners labelled $LABELS for $REPO"
}

# With TOKEN_SECRET, each boot checks the registrations before the runners need them.
setup_boot() {
  if [ -z "$TOKEN_SECRET" ]; then return; fi
  cat >/etc/systemd/system/lanes-register.service <<EOF
[Unit]
Description=Register the Lanes runners that GitHub does not know
Wants=network-online.target
After=network-online.target
[Service]
Type=oneshot
ExecStart=$BASE/ec2-runner.sh register
[Install]
WantedBy=multi-user.target
EOF
  systemctl daemon-reload
  systemctl enable lanes-register.service
}

# Powers off once no runner has had a job (a Runner.Worker process) for IDLE_HOURS.
setup_idle_shutdown() {
  rm -f /etc/systemd/system/lanes-idle.timer /etc/systemd/system/lanes-idle.service
  if [ "$IDLE_HOURS" -gt 0 ]; then
    cat >/usr/local/sbin/lanes-idle <<EOF
#!/bin/bash
stamp=/run/lanes-busy
if pgrep -f Runner.Worker >/dev/null || ! [ -f \$stamp ]; then touch \$stamp; exit 0; fi
if [ \$(( \$(date +%s) - \$(stat -c %Y \$stamp) )) -ge $(( IDLE_HOURS * 3600 )) ]; then
  logger "lanes-idle: no job for $IDLE_HOURS h, powering off"
  systemctl poweroff
fi
EOF
    chmod 755 /usr/local/sbin/lanes-idle
    cat >/etc/systemd/system/lanes-idle.service <<'EOF'
[Unit]
Description=Power off when no CI job has run for a while
[Service]
Type=oneshot
ExecStart=/usr/local/sbin/lanes-idle
EOF
    cat >/etc/systemd/system/lanes-idle.timer <<'EOF'
[Unit]
Description=Check every five minutes whether a CI job runs
[Timer]
OnBootSec=5min
OnUnitActiveSec=5min
[Install]
WantedBy=timers.target
EOF
  fi
  systemctl daemon-reload
  if [ "$IDLE_HOURS" -gt 0 ]; then systemctl enable --now lanes-idle.timer; fi
  if [ "$MAX_HOURS" -gt 0 ]; then shutdown -h "+$(( MAX_HOURS * 60 ))" "lanes: MAX_HOURS reached"; fi
}

# Clones or updates REPO in $SHARED/src as root, so that the token is only in the environment of
# root's git, which the runner user cannot read.
fetch_source() {
  local src=$SHARED/src token=$CLONE_TOKEN
  [ -n "$token" ] || token=$(github_pat)
  local env=(GIT_CONFIG_COUNT=1 GIT_CONFIG_KEY_0=safe.directory GIT_CONFIG_VALUE_0="$src")
  if [ -n "$token" ]; then
    env=(GIT_CONFIG_COUNT=2 GIT_CONFIG_KEY_0=safe.directory GIT_CONFIG_VALUE_0="$src"
      GIT_CONFIG_KEY_1=http.extraHeader
      GIT_CONFIG_VALUE_1="Authorization: Basic $(printf 'x-access-token:%s' "$token" | base64 -w0)")
  fi
  if [ -d "$src/.git" ]; then
    env "${env[@]}" git -C "$src" fetch -q origin "$BRANCH"
    env "${env[@]}" git -C "$src" checkout -q --detach FETCH_HEAD
  else
    env "${env[@]}" git clone -q --branch "$BRANCH" "https://github.com/$REPO" "$src"
  fi
  chown -R "$RUNNER_USER:" "$src"
}

# The warm-up, as the runner user. Idempotent: what is there already is kept.
warm_as_runner() {
  local src=$SHARED/src key dir
  cd "$src"
  flock "$ELAN_DIR/.lanes-toolchain.lock" elan toolchain install "$(cat lean-toolchain)"
  key=$(cat lean-toolchain lake-manifest.json | sha256sum | cut -c1-16)
  dir=$SHARED/$key
  exec 9>"$SHARED/lock"
  lake build
  (cd examples/raft-kv && lake build raftNode raftProcs raftLive)
  flock 9
  mkdir -p "$dir"
  rm -rf "$dir/build.new" "$dir/systems.new"
  cp -a .lake/build "$dir/build.new"
  mkdir -p "$dir/systems.new/raft-kv"
  cp -a examples/raft-kv/.lake/build "$dir/systems.new/raft-kv/build"
  rm -rf "$dir/build" "$dir/systems"
  mv "$dir/build.new" "$dir/build"
  mv "$dir/systems.new" "$dir/systems"
  flock -u 9
  say "warm: $(git rev-parse --short HEAD), build in $dir"
}

warm() {
  fetch_source
  as_runner env BASE="$BASE" bash "$BASE/ec2-runner.sh" --warm-as-runner
}

setup() {
  install_packages
  install_elan
  if [ "$(realpath "$0")" != "$BASE/ec2-runner.sh" ]; then install -m 755 "$0" "$BASE/ec2-runner.sh"; fi
  printf '%s=%q\n' REPO "$REPO" BRANCH "$BRANCH" LABELS "$LABELS" NAME "$NAME" \
    RUNNERS "$RUNNERS" TOKEN_SECRET "$TOKEN_SECRET" AWS_REGION "$AWS_REGION" >"$BASE/lanes.conf"
  block_metadata
  setup_runners
  setup_boot
  setup_idle_shutdown
  if [ "$WARM" = 1 ]; then warm; fi
}

main() {
  case "${1:-}" in
    --fetch-runner) fetch_runner "${2:?a directory}"; return ;;
    --warm-as-runner) warm_as_runner; return ;;
  esac
  [ "$(id -u)" -eq 0 ] || die "${1:-set up} runs as root"
  [ -n "$REPO" ] || die "REPO (owner/name) is not set"
  case "${1:-}" in
    "") setup ;;
    register) block_metadata; setup_runners ;;
    warm) warm ;;
    *) die "unknown argument $1" ;;
  esac
}

if [ "${BASH_SOURCE[0]}" = "$0" ]; then
  main "$@"
fi
