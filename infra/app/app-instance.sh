#!/bin/bash
# One Lanes application on one Ubuntu 24.04 machine: EC2 user data, or run with sudo.
# infra/app/lanes-app.yaml runs it at the instance's first boot; docs/DEPLOY.md says how and why.
#
#   CONFIG_PARAMETER=<name> AWS_REGION=<region> app-instance.sh setup   # set up; safe to run again
#   sudo /opt/lanes/app-instance.sh configure           # read the configuration again, rewrite the units
#   sudo /opt/lanes/app-instance.sh volume              # attach and mount the journal's volume (each boot)
#   sudo /opt/lanes/app-instance.sh deploy SHA SHA256   # fetch a release, check it, switch to it, restart
#   sudo /opt/lanes/app-instance.sh rollback            # back to the release before
#   CONF=<file> app-instance.sh unit                    # print the application's systemd unit
#
# The configuration is the SSM parameter CONFIG_PARAMETER, lines KEY=value that the stack
# writes; setup and `configure` copy it to /etc/lanes/app.conf, which everything else reads.
#
# Set up installs the AWS CLI and the CloudWatch agent, makes the user `lanes`, which runs the
# application and owns nothing else, and installs three units:
#
# - lanes-volume.service, at every boot: attaches the volume named by the instance's tag
#   lanes-journal-volume to this instance (waiting while another instance holds it, as when the
#   stack replaces the instance), makes a file system on it only if it is new and empty, and
#   mounts it at /srv/lanes. The mount point is immutable, so nothing is written there while the
#   volume is not mounted.
# - lanes-app.service: the application, as `lanes`, in /srv/lanes/journal, the one directory it
#   may write. It needs lanes-volume.service and the mount, so an application whose volume is
#   missing does not start (rather than begin an empty journal).
# - lanes-log.service: copies the application's lines from journald to /var/log/lanes/app.log,
#   which the CloudWatch agent sends to the log group as they are (the access log is JSON).
#
# Releases are /opt/lanes/releases/<commit>/<binary>; /opt/lanes/current and /opt/lanes/previous
# are symbolic links to two of them, each replaced by a rename. A deploy checks the binary's
# SHA-256, switches `current`, restarts, and rolls back if READY_PATH does not answer 200 within
# READY_SECONDS. On a new instance, setup starts the release named by RELEASES/current, which
# the deploy workflow writes once the site is ready.
set -euo pipefail

BASE=${BASE:-/opt/lanes}
DATA=${DATA:-/srv/lanes}
JOURNAL_DIR=$DATA/journal
CONF=${CONF:-/etc/lanes/app.conf}
BOOT_CONF=$BASE/bootstrap.conf
APP_USER=lanes
UNIT_DIR=${UNIT_DIR:-/etc/systemd/system}
READY_SECONDS=${READY_SECONDS:-180}
KEEP_RELEASES=${KEEP_RELEASES:-5}
CW_AGENT=/opt/aws/amazon-cloudwatch-agent

say() { echo "app-instance: $*" >&2; }
die() { say "$*"; exit 1; }

# The keys the configuration may set, and nothing else.
CONF_KEYS=(APP BINARY ARGS PORT READY_PATH METRICS_PATH DRAIN_SECONDS RELEASES LOG_GROUP
  METRICS_LOG_GROUP METRICS_NAMESPACE SCRIPT_URL SCRIPT_SHA256 DB_HOST DB_PORT DB_NAME DB_SECRET
  MAIL_IDENTITY MEDIA_BUCKET)

load_conf() {
  # shellcheck source=/dev/null
  if [ -f "$BOOT_CONF" ]; then . "$BOOT_CONF"; fi
  # shellcheck source=/dev/null
  if [ -f "$CONF" ]; then . "$CONF"; fi
  APP=${APP:-}
  BINARY=${BINARY:-}
  ARGS=${ARGS-"{port} {journal}"}
  PORT=${PORT:-8080}
  READY_PATH=${READY_PATH:-/readyz}
  METRICS_PATH=${METRICS_PATH:-}
  DRAIN_SECONDS=${DRAIN_SECONDS:-15}
  RELEASES=${RELEASES:-}
  LOG_GROUP=${LOG_GROUP:-}
  METRICS_LOG_GROUP=${METRICS_LOG_GROUP:-}
  METRICS_NAMESPACE=${METRICS_NAMESPACE:-}
  SCRIPT_URL=${SCRIPT_URL:-}
  SCRIPT_SHA256=${SCRIPT_SHA256:-}
  DB_HOST=${DB_HOST:-}
  DB_PORT=${DB_PORT:-}
  DB_NAME=${DB_NAME:-}
  DB_SECRET=${DB_SECRET:-}
  MAIL_IDENTITY=${MAIL_IDENTITY:-}
  MEDIA_BUCKET=${MEDIA_BUCKET:-}
  CONFIG_PARAMETER=${CONFIG_PARAMETER:-}
  AWS_REGION=${AWS_REGION:-}
}

# What goes into a unit file or a command line is checked first: no quotes, `$`, `%` or `\`.
check_conf() {
  [[ $APP =~ ^[a-z][a-z0-9-]{1,30}$ ]] || die "APP '$APP' is not a lowercase name"
  [[ $BINARY =~ ^[A-Za-z0-9_.-]{1,64}$ ]] || die "BINARY '$BINARY' is not a file name"
  [[ $ARGS =~ ^[A-Za-z0-9\ _./:{}=,+-]*$ ]] || die "ARGS has a character other than letters, digits and _./:{}=,+-"
  [[ $PORT =~ ^[0-9]{4,5}$ ]] || die "PORT '$PORT' is not a port"
  [[ $READY_PATH =~ ^/[A-Za-z0-9_./-]*$ ]] || die "READY_PATH '$READY_PATH' is not a path"
  [[ $METRICS_PATH =~ ^(/[A-Za-z0-9_./-]*)?$ ]] || die "METRICS_PATH '$METRICS_PATH' is not a path"
  [[ $DRAIN_SECONDS =~ ^[0-9]{1,3}$ ]] || die "DRAIN_SECONDS '$DRAIN_SECONDS' is not a number"
  [[ $MAIL_IDENTITY =~ ^([A-Za-z0-9._+-]+@)?([A-Za-z0-9-]+\.)*[A-Za-z0-9-]*$ ]] \
    || die "MAIL_IDENTITY '$MAIL_IDENTITY' is not an address or a domain"
  [[ $MEDIA_BUCKET =~ ^([a-z0-9][a-z0-9.-]{1,61}[a-z0-9])?$ ]] \
    || die "MEDIA_BUCKET '$MEDIA_BUCKET' is not a bucket name"
}

# The arguments the application is started with.
app_args() {
  local a=$ARGS
  a=${a//\{port\}/$PORT}
  a=${a//\{journal\}/$JOURNAL_DIR/$APP.journal}
  a=${a//\{data\}/$JOURNAL_DIR}
  echo "$a"
}

aws_cli() {
  if command -v aws >/dev/null; then aws "$@"; else /snap/bin/aws "$@"; fi
}

# A path of the instance metadata service, with an IMDSv2 token.
imds() {
  local token
  token=$(curl -fsS -X PUT -H "X-aws-ec2-metadata-token-ttl-seconds: 300" http://169.254.169.254/latest/api/token)
  curl -fsS -H "X-aws-ec2-metadata-token: $token" "http://169.254.169.254/latest/$1"
}

region() {
  if [ -n "$AWS_REGION" ]; then echo "$AWS_REGION"; else imds meta-data/placement/region; fi
}

install_packages() {
  export DEBIAN_FRONTEND=noninteractive
  apt-get update -q
  apt-get install -yq curl ca-certificates python3 util-linux e2fsprogs logrotate
  if ! command -v aws >/dev/null && ! [ -x /snap/bin/aws ]; then snap install aws-cli --classic; fi
}

# Copies CONFIG_PARAMETER to CONF, keeping only the known keys, each value quoted.
fetch_config() {
  [ -n "$CONFIG_PARAMETER" ] || die "CONFIG_PARAMETER is not set"
  local text line key value tmp
  text=$(aws_cli ssm get-parameter --region "$(region)" --name "$CONFIG_PARAMETER" \
    --query Parameter.Value --output text)
  mkdir -p "$(dirname "$CONF")"
  tmp=$(mktemp "$CONF.XXXXXX")
  while IFS= read -r line; do
    [ -n "$line" ] || continue
    key=${line%%=*}
    value=${line#*=}
    if [[ " ${CONF_KEYS[*]} " == *" $key "* ]]; then printf '%s=%q\n' "$key" "$value" >>"$tmp"; fi
  done <<<"$text"
  chmod 644 "$tmp"
  mv "$tmp" "$CONF"
  # shellcheck source=/dev/null
  . "$CONF"
  check_conf
}

# Installs this script from SCRIPT_URL, which must have the SHA-256 SCRIPT_SHA256: it runs as
# root, so one fetched without its hash, or with another, is refused. Without a URL, the running
# copy.
install_script() {
  local tmp
  if [ -n "$SCRIPT_URL" ] && ! [[ $SCRIPT_SHA256 =~ ^[0-9a-f]{64}$ ]]; then
    die "SCRIPT_URL is given without SCRIPT_SHA256: a script is not run unchecked"
  fi
  tmp=$(mktemp "$BASE/.app-instance.XXXXXX")
  if [ -n "$SCRIPT_URL" ]; then curl -fsSL --retry 5 -o "$tmp" "$SCRIPT_URL"; else cp "$0" "$tmp"; fi
  if [ -n "$SCRIPT_URL" ] && ! echo "$SCRIPT_SHA256  $tmp" | sha256sum -c --status -; then
    rm -f "$tmp"
    die "$SCRIPT_URL does not have the SHA-256 $SCRIPT_SHA256"
  fi
  chmod 755 "$tmp"
  mv "$tmp" "$BASE/app-instance.sh"
}

make_user() {
  id "$APP_USER" >/dev/null 2>&1 || useradd --system --user-group --no-create-home \
    --home-dir /nonexistent --shell /usr/sbin/nologin "$APP_USER"
  mkdir -p "$BASE/releases" /etc/lanes /var/log/lanes
  if ! mountpoint -q "$DATA"; then
    mkdir -p "$DATA"
    chattr +i "$DATA"
  fi
}

render_volume_unit() {
  cat <<EOF
[Unit]
Description=Attach and mount the journal's volume of the Lanes application at $DATA
Wants=network-online.target
After=network-online.target
[Service]
Type=oneshot
RemainAfterExit=yes
TimeoutStartSec=3700
ExecStart=$BASE/app-instance.sh volume
[Install]
WantedBy=multi-user.target
EOF
}

# The application's unit. The environment is what the `main` of `lanes new` reads: listen on every
# address, keep idle connections longer than the load balancer (60 s), and at SIGTERM drain for up
# to DRAIN_SECONDS (Server.stopOnSignal, docs/DEPLOY.md); the stop timeout is ten seconds more.
render_app_unit() {
  cat <<EOF
[Unit]
Description=The Lanes application $APP
Documentation=https://github.com/tacitresearch/lanes/blob/main/docs/DEPLOY.md
Requires=lanes-volume.service
After=lanes-volume.service network-online.target
Wants=network-online.target
ConditionPathExists=$BASE/current/$BINARY
StartLimitIntervalSec=0

[Service]
Type=exec
User=$APP_USER
Group=$APP_USER
WorkingDirectory=$JOURNAL_DIR
Environment=LANES_HOST=0.0.0.0 LANES_IDLE_MS=75000 LANES_DRAIN_MS=$((DRAIN_SECONDS * 1000))
EnvironmentFile=-/etc/lanes/app.env
EnvironmentFile=-/etc/lanes/secrets.env
RuntimeDirectory=lanes-app
RuntimeDirectoryMode=0700
ExecStartPre=/usr/bin/mountpoint -q $DATA
ExecStartPre=+$BASE/app-instance.sh database
ExecStart=$BASE/current/$BINARY $(app_args)
Restart=always
RestartSec=2
KillSignal=SIGTERM
TimeoutStopSec=$((DRAIN_SECONDS + 10))
StandardOutput=journal
StandardError=journal
SyslogIdentifier=$APP
LimitNOFILE=65536
UMask=0077

NoNewPrivileges=yes
ProtectSystem=strict
ReadWritePaths=$JOURNAL_DIR
PrivateTmp=yes
PrivateDevices=yes
ProtectHome=yes
ProtectProc=invisible
ProtectKernelTunables=yes
ProtectKernelModules=yes
ProtectKernelLogs=yes
ProtectControlGroups=yes
ProtectClock=yes
ProtectHostname=yes
CapabilityBoundingSet=
AmbientCapabilities=
RestrictAddressFamilies=AF_INET AF_INET6 AF_UNIX AF_NETLINK
RestrictNamespaces=yes
RestrictRealtime=yes
RestrictSUIDSGID=yes
LockPersonality=yes
MemoryDenyWriteExecute=yes
RemoveIPC=yes
SystemCallArchitectures=native

[Install]
WantedBy=multi-user.target
EOF
}

render_log_unit() {
  cat <<EOF
[Unit]
Description=Copy the Lanes application's lines from journald to /var/log/lanes/app.log
After=systemd-journald.service
[Service]
StateDirectory=lanes-log
ExecStart=/bin/sh -c 'exec journalctl --follow --output=cat --unit=lanes-app.service --cursor-file=/var/lib/lanes-log/cursor >>/var/log/lanes/app.log'
Restart=always
RestartSec=5
[Install]
WantedBy=multi-user.target
EOF
}

write_units() {
  render_volume_unit >"$UNIT_DIR/lanes-volume.service"
  render_app_unit >"$UNIT_DIR/lanes-app.service"
  render_log_unit >"$UNIT_DIR/lanes-log.service"
  cat >/etc/logrotate.d/lanes <<'EOF'
/var/log/lanes/*.log {
  daily
  rotate 7
  maxsize 200M
  missingok
  notifempty
  compress
  delaycompress
  copytruncate
}
EOF
  # The region, for the role's credentials (which the application fetches from the metadata
  # service itself), S3 and SES; the media bucket, and the database and the mail identity when
  # there are. secrets.env, read after, may set any of it again.
  {
    printf '%s=%s\n' AWS_REGION "$(region)"
    if [ -n "$MEDIA_BUCKET" ]; then printf '%s=%s\n' LANES_MEDIA_BUCKET "$MEDIA_BUCKET"; fi
    if [ -n "$DB_HOST" ]; then
      printf '%s=%s\n' LANES_DB_HOST "$DB_HOST" LANES_DB_PORT "$DB_PORT" LANES_DB_NAME "$DB_NAME"
    fi
    if [ -n "$MAIL_IDENTITY" ]; then printf '%s=%s\n' LANES_MAIL_IDENTITY "$MAIL_IDENTITY"; fi
  } >/etc/lanes/app.env
  systemctl daemon-reload
  systemctl enable lanes-volume.service lanes-app.service lanes-log.service
}

install_cloudwatch_agent() {
  local arch
  case "$(uname -m)" in
    x86_64) arch=amd64 ;;
    aarch64) arch=arm64 ;;
    *) die "no CloudWatch agent for $(uname -m)" ;;
  esac
  if ! [ -x "$CW_AGENT/bin/amazon-cloudwatch-agent-ctl" ]; then
    curl -fsSL --retry 5 -o /tmp/amazon-cloudwatch-agent.deb \
      "https://amazoncloudwatch-agent.s3.amazonaws.com/ubuntu/$arch/latest/amazon-cloudwatch-agent.deb"
    dpkg -i -E /tmp/amazon-cloudwatch-agent.deb
    rm -f /tmp/amazon-cloudwatch-agent.deb
  fi
}

# The agent sends the application's lines and the setup log to LOG_GROUP, the disk and memory
# used to METRICS_NAMESPACE, and, with a metrics page, its counters and gauges as metrics.
render_cloudwatch_config() {
  local prometheus=""
  if [ -n "$METRICS_PATH" ]; then
    prometheus=$(cat <<EOF
,
    "metrics_collected": {
      "prometheus": {
        "cluster_name": "$APP",
        "log_group_name": "$METRICS_LOG_GROUP",
        "prometheus_config_path": "$CW_AGENT/etc/prometheus.yaml",
        "emf_processor": {
          "metric_declaration_dedup": true,
          "metric_namespace": "$METRICS_NAMESPACE",
          "metric_declaration": [
            {
              "source_labels": ["job"],
              "label_matcher": "^lanes$",
              "dimensions": [["job"]],
              "metric_selectors": [
                "^lanes_http_requests_in_flight$", "^lanes_http_connections$",
                "^lanes_runtime_inbox_depth$", "^lanes_ready$",
                "^lanes_http_connections_refused_total$", "^lanes_journal_appends_total$",
                "^lanes_journal_entries_total$", "^lanes_journal_saves_total$"
              ]
            },
            {
              "source_labels": ["job"],
              "label_matcher": "^lanes$",
              "dimensions": [["job", "status_class"]],
              "metric_selectors": ["^lanes_http_requests_total$"]
            }
          ]
        }
      }
    }
EOF
)
  fi
  cat <<EOF
{
  "agent": { "run_as_user": "cwagent" },
  "metrics": {
    "namespace": "$METRICS_NAMESPACE",
    "aggregation_dimensions": [["path"], []],
    "metrics_collected": {
      "disk": { "measurement": ["used_percent"], "resources": ["/", "$DATA"], "drop_device": true },
      "mem": { "measurement": ["used_percent"] }
    }
  },
  "logs": {
    "logs_collected": {
      "files": {
        "collect_list": [
          { "file_path": "/var/log/lanes/app.log", "log_group_name": "$LOG_GROUP",
            "log_stream_name": "{instance_id}" },
          { "file_path": "/var/log/lanes-setup.log", "log_group_name": "$LOG_GROUP",
            "log_stream_name": "{instance_id}-setup" }
        ]
      }
    }$prometheus
  }
}
EOF
}

render_prometheus_config() {
  cat <<EOF
global:
  scrape_interval: 1m
  scrape_timeout: 10s
scrape_configs:
  - job_name: lanes
    metrics_path: $METRICS_PATH
    static_configs:
      - targets: ["127.0.0.1:$PORT"]
EOF
}

configure_cloudwatch_agent() {
  # Readable by root and the agent alone: an access line names paths and peers.
  touch /var/log/lanes/app.log /var/log/lanes-setup.log
  chgrp cwagent /var/log/lanes/app.log /var/log/lanes-setup.log
  chmod 640 /var/log/lanes/app.log /var/log/lanes-setup.log
  render_cloudwatch_config >"$CW_AGENT/etc/lanes.json"
  if [ -n "$METRICS_PATH" ]; then render_prometheus_config >"$CW_AGENT/etc/prometheus.yaml"; fi
  "$CW_AGENT/bin/amazon-cloudwatch-agent-ctl" -a fetch-config -m ec2 -s -c "file:$CW_AGENT/etc/lanes.json"
}

# The device of a volume on a Nitro instance: its NVMe serial is the id without the dash.
volume_device() {
  echo "/dev/disk/by-id/nvme-Amazon_Elastic_Block_Store_${1//-/}"
}

# Attaches volume $1 to this instance, waiting up to an hour while it is attached elsewhere.
attach_volume() {
  local vol=$1 me deadline state attached err d
  me=$(imds meta-data/instance-id)
  deadline=$(( $(date +%s) + 3600 ))
  while :; do
    read -r state attached < <(aws_cli ec2 describe-volumes --region "$(region)" --volume-ids "$vol" \
      --query 'Volumes[0].[State,Attachments[0].InstanceId]' --output text)
    if [ "$state" = in-use ] && [ "$attached" = "$me" ]; then return 0; fi
    if [ "$state" = available ]; then
      for d in f g h i j k l m n o p; do
        if err=$(aws_cli ec2 attach-volume --region "$(region)" --volume-id "$vol" --instance-id "$me" \
            --device "/dev/sd$d" 2>&1 >/dev/null); then return 0; fi
      done
      say "attaching $vol failed: $err"
    fi
    [ "$(date +%s)" -lt "$deadline" ] || die "$vol is still $state (attached to $attached) after an hour"
    say "waiting for $vol: $state, attached to $attached"
    sleep 10
  done
}

# At every boot, and after a restore: mounts the volume of the tag lanes-journal-volume at DATA.
volume() {
  local vol dev snap stopped=""
  vol=$(imds meta-data/tags/instance/lanes-journal-volume)
  [[ $vol =~ ^vol-[0-9a-f]+$ ]] || die "the tag lanes-journal-volume ('$vol') names no volume"
  dev=$(volume_device "$vol")
  if ! [ -e "$dev" ]; then
    attach_volume "$vol"
    for _ in $(seq 1 120); do [ -e "$dev" ] && break; sleep 1; done
    [ -e "$dev" ] || die "$vol is attached but $dev did not appear"
  fi
  if mountpoint -q "$DATA"; then
    if [ "$(findmnt -n -o SOURCE "$DATA")" = "$(readlink -f "$dev")" ]; then return 0; fi
    say "$DATA holds another volume: stopping the application to mount $vol"
    systemctl stop lanes-app.service
    stopped=1
    umount "$DATA"
  fi
  if [ -z "$(blkid -o value -s TYPE "$dev" || true)" ]; then
    snap=$(aws_cli ec2 describe-volumes --region "$(region)" --volume-ids "$vol" \
      --query 'Volumes[0].SnapshotId' --output text)
    # A volume made from a snapshot has the snapshot's file system; it is never made again.
    case "$snap" in ""|None) ;; *) die "$vol was made from $snap but has no file system" ;; esac
    say "making a file system on the new volume $vol"
    mkfs.ext4 -q -L lanes-journal "$dev"
  fi
  mount -o noatime,nodev,nosuid,noexec "$dev" "$DATA"
  mkdir -p "$JOURNAL_DIR"
  chown "$APP_USER:$APP_USER" "$JOURNAL_DIR"
  chmod 700 "$JOURNAL_DIR"
  say "$vol is mounted at $DATA"
  if [ -n "$stopped" ]; then systemctl start lanes-app.service; fi
}

# Before each start, as root: the database's address (the Lanes client takes an IPv4 address)
# and password, in files only the application reads.
database() {
  local dir=/run/lanes-app address
  [ -n "$DB_HOST" ] || return 0
  address=$(getent ahostsv4 "$DB_HOST" | awk 'NR == 1 { print $1 }')
  [ -n "$address" ] || die "$DB_HOST has no IPv4 address"
  echo "$address" >"$dir/db-address"
  aws_cli secretsmanager get-secret-value --region "$(region)" --secret-id "$DB_SECRET" \
    --query SecretString --output text \
    | python3 -c 'import json, sys; sys.stdout.write(json.load(sys.stdin)["password"])' >"$dir/db-password"
  chown "$APP_USER:$APP_USER" "$dir/db-address" "$dir/db-password"
  chmod 400 "$dir/db-address" "$dir/db-password"
}

# Points link $1 at $2 by a rename, so that it is never missing.
relink() {
  ln -sfn "$2" "$1.new"
  mv -T "$1.new" "$1"
}

ready() {
  curl -fs -o /dev/null --max-time 2 "http://127.0.0.1:$PORT$READY_PATH"
}

restart_and_wait() {
  local deadline
  systemctl restart lanes-app.service
  deadline=$(( $(date +%s) + READY_SECONDS ))
  while [ "$(date +%s)" -lt "$deadline" ]; do
    if ready; then return 0; fi
    sleep 1
  done
  return 1
}

# The release of commit $1 with SHA-256 $2, fetched unless it is here already.
fetch_release() {
  local release=$1 sha=$2 dir=$BASE/releases/$1 tmp
  if [ -f "$dir/$BINARY" ] && echo "$sha  $dir/$BINARY" | sha256sum -c --status -; then return 0; fi
  [ -n "$RELEASES" ] || die "RELEASES is not set"
  tmp=$(mktemp -d "$BASE/releases/.fetch.XXXXXX")
  aws_cli s3 cp --only-show-errors --region "$(region)" "$RELEASES/releases/$release/$BINARY" "$tmp/$BINARY"
  if ! echo "$sha  $tmp/$BINARY" | sha256sum -c --status -; then
    rm -rf "$tmp"
    die "$RELEASES/releases/$release/$BINARY does not have the SHA-256 $sha"
  fi
  chmod 755 "$tmp/$BINARY"
  rm -rf "$dir"
  mv "$tmp" "$dir"
}

# Keeps `current`, `previous` and the newest KEEP_RELEASES releases.
prune() {
  local keep_a keep_b dir
  keep_a=$(readlink -f "$BASE/current" || true)
  keep_b=$(readlink -f "$BASE/previous" || true)
  # shellcheck disable=SC2012
  ls -1dt "$BASE"/releases/*/ 2>/dev/null | tail -n +$((KEEP_RELEASES + 1)) | while read -r dir; do
    dir=${dir%/}
    if [ "$dir" != "$keep_a" ] && [ "$dir" != "$keep_b" ]; then rm -rf "$dir"; fi
  done
}

lock() {
  exec 9>/run/lanes-deploy.lock
  flock -w 900 9 || die "another deploy holds the lock"
}

deploy() {
  local release=${1:-} sha=${2:-} old old_prev
  [[ $release =~ ^[0-9a-f]{40}([0-9a-f]{24})?$ ]] || die "deploy takes a commit, not '$release'"
  [[ $sha =~ ^[0-9a-f]{64}$ ]] || die "deploy takes a SHA-256, not '$sha'"
  lock
  fetch_release "$release" "$sha"
  old=$(readlink "$BASE/current" || true)
  old_prev=$(readlink "$BASE/previous" || true)
  if [ -n "$old" ] && [ "$old" != "$BASE/releases/$release" ]; then relink "$BASE/previous" "$old"; fi
  relink "$BASE/current" "$BASE/releases/$release"
  if restart_and_wait; then
    say "$release is ready"
    prune
    return 0
  fi
  say "$release did not answer 200 at $READY_PATH within $READY_SECONDS s"
  journalctl -u lanes-app.service -n 30 --no-pager >&2 || true
  if [ -n "$old" ]; then
    relink "$BASE/current" "$old"
    if [ -n "$old_prev" ]; then relink "$BASE/previous" "$old_prev"; else rm -f "$BASE/previous"; fi
    if restart_and_wait; then say "rolled back to $(basename "$old")"; else say "$(basename "$old") is not ready either"; fi
  fi
  die "deploy of $release failed"
}

rollback() {
  local cur prev
  lock
  prev=$(readlink "$BASE/previous" || true)
  [ -n "$prev" ] && [ -d "$prev" ] || die "there is no release before this one"
  cur=$(readlink "$BASE/current" || true)
  relink "$BASE/current" "$prev"
  if [ -n "$cur" ]; then relink "$BASE/previous" "$cur"; fi
  restart_and_wait || die "$(basename "$prev") did not answer 200 at $READY_PATH within $READY_SECONDS s"
  say "rolled back to $(basename "$prev")"
}

# On a new instance: the release the deploy workflow last made current, if there is one.
start_current_release() {
  local line release sha
  [ -e "$BASE/current" ] && return 0
  [ -n "$RELEASES" ] || return 0
  line=$(aws_cli s3 cp --only-show-errors --region "$(region)" "$RELEASES/current" - 2>/dev/null || true)
  read -r release sha <<<"$line"
  if [ -z "${release:-}" ]; then say "no release deployed yet"; return 0; fi
  deploy "$release" "$sha" || say "the current release $release did not start"
}

# The units are written by the script just installed, which may be newer than this one.
configure() {
  fetch_config
  install_script
  exec "$BASE/app-instance.sh" reconfigure
}

reconfigure() {
  write_units
  configure_cloudwatch_agent
  systemctl start lanes-volume.service lanes-log.service
  if [ -e "$BASE/current" ]; then systemctl restart lanes-app.service; fi
}

setup() {
  install_packages
  make_user
  printf '%s=%q\n' CONFIG_PARAMETER "$CONFIG_PARAMETER" AWS_REGION "$(region)" >"$BOOT_CONF"
  fetch_config
  install_cloudwatch_agent
  install_script
  write_units
  configure_cloudwatch_agent
  systemctl start lanes-volume.service lanes-log.service
  start_current_release
  say "set up $APP"
}

main() {
  load_conf
  case "${1:-}" in
    unit) check_conf; render_app_unit; return ;;
    args) check_conf; app_args; return ;;
  esac
  [ "$(id -u)" -eq 0 ] || die "${1:-setup} runs as root"
  case "${1:-}" in
    setup|"") setup ;;
    configure) configure ;;
    reconfigure) check_conf; reconfigure ;;
    volume) volume ;;
    database) database ;;
    deploy) check_conf; deploy "${2:-}" "${3:-}" ;;
    rollback) check_conf; rollback ;;
    *) die "unknown argument $1" ;;
  esac
}

if [ "${BASH_SOURCE[0]}" = "$0" ]; then
  main "$@"
fi
