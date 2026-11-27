#!/bin/bash
# Starts or stops the runner machine of a workflow run: see action.yml beside this file.
set -euo pipefail

say() { echo "box: $*" >&2; }
die() { echo "::error::box: $*" >&2; exit 1; }

api() {
  local method=$1 path=$2 token=${3:-$RUNNER_TOKEN}
  curl -fsSL -X "$method" -H @<(printf 'Authorization: Bearer %s\n' "$token") \
    -H "Accept: application/vnd.github+json" -H "X-GitHub-Api-Version: 2022-11-28" \
    "$GITHUB_API_URL$path"
}

# The repository's runners that carry every label of LABELS: "id status busy name" a line.
runners() {
  api GET "/repos/$GITHUB_REPOSITORY/actions/runners?per_page=100" | python3 -c '
import json, os, sys
want = json.loads(os.environ["LABELS"])
want = {l.lower() for l in ([want] if isinstance(want, str) else want)}
for r in json.load(sys.stdin)["runners"]:
    if want <= {l["name"].lower() for l in r["labels"]}:
        print(r["id"], r["status"], str(r["busy"]).lower(), r["name"])'
}

wait_online() {
  if [ -z "$RUNNER_TOKEN" ]; then
    say "no LANES_RUNNER_PAT: the jobs wait for the runners to connect"
    return
  fi
  local deadline=$(( $(date +%s) + WAIT_MINUTES * 60 )) list online total
  while :; do
    list=$(runners)
    total=$(grep -c . <<<"$list" || true)
    online=$(grep -c ' online ' <<<"$list" || true)
    say "$online of $total runners online"
    if [ "$online" -gt 0 ] && { [ "$ROUTE" = fresh ] || [ "$online" -eq "$total" ]; }; then return; fi
    if [ "$(date +%s)" -ge "$deadline" ]; then
      [ "$online" -gt 0 ] && { echo "::warning::only $online of $total runners came online"; return; }
      die "no runner with the labels $LABELS came online in $WAIT_MINUTES minutes"
    fi
    sleep 10
  done
}

state() {
  aws ec2 describe-instances --instance-ids "$1" \
    --query 'Reservations[0].Instances[0].State.Name' --output text
}

start_box() {
  local s
  s=$(state "$INSTANCE_ID")
  say "$INSTANCE_ID is $s"
  case "$s" in
    stopping)
      aws ec2 wait instance-stopped --instance-ids "$INSTANCE_ID"
      aws ec2 start-instances --instance-ids "$INSTANCE_ID" >/dev/null ;;
    stopped) aws ec2 start-instances --instance-ids "$INSTANCE_ID" >/dev/null ;;
    pending | running) ;;
    *) die "$INSTANCE_ID is $s" ;;
  esac
  aws ec2 wait instance-running --instance-ids "$INSTANCE_ID"
  wait_online
}

# Leaves the machine running while another run of WORKFLOWS is queued or under way, or one
# of its runners is busy: the last run to end stops it.
stop_box() {
  local others busy
  others=$(
    for status in queued in_progress; do
      api GET "/repos/$GITHUB_REPOSITORY/actions/runs?status=$status&per_page=100" "$GITHUB_TOKEN"
      echo
    done | python3 -c '
import json, os, sys
mine, workflows = os.environ["GITHUB_RUN_ID"], os.environ["WORKFLOWS"].split()
text, decoder, at, pages = sys.stdin.read(), json.JSONDecoder(), 0, []
while text[at:].strip():
    page, at = decoder.raw_decode(text, len(text) - len(text[at:].lstrip()))
    pages.append(page)
for page in pages:
    for run in page["workflow_runs"]:
        name = run["path"].split("@")[0].rsplit("/", 1)[-1]
        if str(run["id"]) != mine and name in workflows:
            print(run["id"], name, run["status"])'
  )
  if [ -n "$others" ]; then
    say "left running for other runs:"$'\n'"$others"
    return
  fi
  if [ -n "$RUNNER_TOKEN" ]; then
    busy=$(runners | awk '$3 == "true"')
    if [ -n "$busy" ]; then
      say "left running for runners still busy:"$'\n'"$busy"
      return
    fi
  fi
  say "stopping $INSTANCE_ID"
  aws ec2 stop-instances --instance-ids "$INSTANCE_ID" >/dev/null
}

start_fresh() {
  [ -n "$RUNNER_TOKEN" ] || die "a machine for each run needs the secret LANES_RUNNER_PAT"
  local token userdata network=() id
  token=$(api POST "/repos/$GITHUB_REPOSITORY/actions/runners/registration-token" \
    | python3 -c 'import json, sys; print(json.load(sys.stdin)["token"])')
  echo "::add-mask::$token"
  userdata=$(mktemp)
  {
    echo '#!/bin/bash'
    echo "cat >/root/ec2-runner.sh <<'LANES_EOF'"
    cat "$GITHUB_WORKSPACE/infra/ec2-runner.sh"
    echo 'LANES_EOF'
    printf 'REPO=%q TOKEN=%q LABELS=%q NAME=%q WARM=0 IDLE_HOURS=1 MAX_HOURS=%q bash /root/ec2-runner.sh\n' \
      "$GITHUB_REPOSITORY" "$token" "$RUN_LABEL" "$RUN_LABEL" "$MAX_HOURS"
  } | gzip -9 >"$userdata"
  [ -z "$SUBNET" ] || network+=(--subnet-id "$SUBNET")
  [ -z "$SECURITY_GROUP" ] || network+=(--security-group-ids "$SECURITY_GROUP")
  local tags="{Key=lanes-ci,Value=fresh},{Key=lanes-ci-run,Value=$RUN_LABEL}"
  id=$(aws ec2 run-instances --image-id "$IMAGE" --instance-type "$INSTANCE_TYPE" --count 1 \
    --instance-initiated-shutdown-behavior terminate --user-data "fileb://$userdata" \
    --metadata-options HttpTokens=required,HttpPutResponseHopLimit=1 \
    --block-device-mappings "DeviceName=/dev/sda1,Ebs={VolumeSize=$VOLUME_GB,VolumeType=gp3,DeleteOnTermination=true,Encrypted=true}" \
    --tag-specifications "ResourceType=instance,Tags=[{Key=Name,Value=$RUN_LABEL},$tags]" \
    "ResourceType=volume,Tags=[$tags]" "${network[@]}" \
    --query 'Instances[0].InstanceId' --output text)
  rm -f "$userdata"
  say "launched $id"
  aws ec2 wait instance-running --instance-ids "$id"
  wait_online
}

stop_fresh() {
  local ids id
  ids=$(aws ec2 describe-instances \
    --filters "Name=tag:lanes-ci-run,Values=$RUN_LABEL" \
    "Name=instance-state-name,Values=pending,running,stopping,stopped" \
    --query 'Reservations[].Instances[].InstanceId' --output text)
  if [ -n "$ids" ]; then
    say "terminating $ids"
    # shellcheck disable=SC2086
    aws ec2 terminate-instances --instance-ids $ids >/dev/null
  fi
  if [ -n "$RUNNER_TOKEN" ]; then
    for id in $(LABELS="[\"$RUN_LABEL\"]" runners | awk '{print $1}'); do
      api DELETE "/repos/$GITHUB_REPOSITORY/actions/runners/$id" >/dev/null
    done
  fi
}

case "$MODE-$ROUTE" in
  start-box) start_box ;;
  stop-box) stop_box ;;
  start-fresh) start_fresh ;;
  stop-fresh) stop_fresh ;;
  *) die "nothing to do for mode $MODE and route $ROUTE" ;;
esac
