#!/bin/bash
# A machine to run Claude Code sessions on Lanes directly: Ubuntu 24.04, as EC2 user-data or
# with sudo. See "A machine for Claude Code sessions" in docs/RUNNERS.md.
#
#   REPO=owner/name [DEV_USER=ubuntu] [CLONE_TOKEN=...] [SESSIONS=4] dev-box.sh
#
# Installs build-essential, git, curl, python3, zstd, tmux and ripgrep; elan with no default
# toolchain; Claude Code with its official installer, for DEV_USER; clones REPO into
# ~DEV_USER/lanes (CLONE_TOKEN, a short-lived token, for a private repository: used once, not
# stored) and warms it: the toolchain, Mathlib's build and a first `lake build`. SESSIONS extra
# worktrees, ~/lanes-1 ... ~/lanes-N, share its `.lake/packages`, so that several sessions can
# build at once.
#
# Then, as DEV_USER: `claude` once to log in, and `lanes-claude [N]` to start (or attach to) a
# tmux session running Claude Code with Remote Control in ~/lanes or ~/lanes-N.
set -euo pipefail

REPO=${REPO:?REPO (owner/name) is not set}
DEV_USER=${DEV_USER:-ubuntu}
CLONE_TOKEN=${CLONE_TOKEN:-}
BRANCH=${BRANCH:-main}
SESSIONS=${SESSIONS:-4}

[ "$(id -u)" -eq 0 ] || { echo "dev-box: run as root" >&2; exit 1; }
id "$DEV_USER" >/dev/null 2>&1 || useradd --create-home --shell /bin/bash "$DEV_USER"
home=$(getent passwd "$DEV_USER" | cut -d: -f6)

export DEBIAN_FRONTEND=noninteractive
apt-get update -q
apt-get install -yq build-essential git curl ca-certificates python3 zstd tmux ripgrep sudo

as_dev() { sudo -u "$DEV_USER" -H env PATH="$home/.local/bin:$home/.elan/bin:/usr/local/bin:/usr/bin:/bin" "$@"; }

if ! [ -x "$home/.elan/bin/elan" ]; then
  curl -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o /tmp/elan-init.sh
  as_dev sh /tmp/elan-init.sh -y --default-toolchain none
fi
if ! [ -x "$home/.local/bin/claude" ]; then
  curl -fsSL https://claude.ai/install.sh -o /tmp/claude-install.sh
  as_dev bash /tmp/claude-install.sh
fi

src=$home/lanes
if ! [ -d "$src/.git" ]; then
  env=(GIT_CONFIG_COUNT=0)
  if [ -n "$CLONE_TOKEN" ]; then
    env=(GIT_CONFIG_COUNT=1 GIT_CONFIG_KEY_0=http.extraHeader
      GIT_CONFIG_VALUE_0="Authorization: Basic $(printf 'x-access-token:%s' "$CLONE_TOKEN" | base64 -w0)")
  fi
  env "${env[@]}" git clone -q --branch "$BRANCH" "https://github.com/$REPO" "$src"
  chown -R "$DEV_USER:" "$src"
fi
as_dev bash -c "cd '$src' && lake exe cache get && lake build"

for i in $(seq 1 "$SESSIONS"); do
  tree=$home/lanes-$i
  if ! [ -d "$tree" ]; then
    as_dev git -C "$src" worktree add -q --detach "$tree"
    as_dev mkdir -p "$tree/.lake"
    as_dev ln -s "$src/.lake/packages" "$tree/.lake/packages"
    as_dev cp -a "$src/.lake/build" "$tree/.lake/build"
  fi
done

cat >/usr/local/bin/lanes-claude <<'EOF'
#!/bin/bash
# lanes-claude [N]: attach to the tmux session `lanes-N` (`lanes` without N), starting it first,
# with Claude Code's Remote Control, in ~/lanes-N (or ~/lanes). Detach with C-b d; it goes on.
name=lanes${1:+-$1}
dir=$HOME/$name
[ -d "$dir" ] || { echo "lanes-claude: no $dir" >&2; exit 1; }
if ! tmux has-session -t "$name" 2>/dev/null; then
  tmux new-session -d -s "$name" -c "$dir" "claude remote-control; exec bash"
fi
[ -n "${TMUX:-}" ] || exec tmux attach -t "$name"
EOF
chmod 755 /usr/local/bin/lanes-claude
echo "dev-box: ready. As $DEV_USER: run \`claude\` once to log in, then \`lanes-claude\`." >&2
