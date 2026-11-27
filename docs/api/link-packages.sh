#!/usr/bin/env bash
# Gives docs/api the packages Lanes already has: each package of the root's lake-manifest.json
# becomes a link, in docs/api/.lake/packages, to the root's .lake/packages, so neither Mathlib
# nor anything else Lanes uses is fetched or built twice. Lake fetches doc-gen4 and its own
# dependencies into real directories beside them, and `Cli` too: Lanes only checks it out,
# doc-gen4 builds it, and a build here must not write into the root's packages.
#
# Fails if this package's manifest pins a package of the root's at another revision or URL:
# Lake would then check that revision out in the root's copy.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../.." && pwd)"
own="Cli"

python3 -I - "$root/lake-manifest.json" "$here/lake-manifest.json" <<'EOF'
import json, sys
root = {p["name"]: p for p in json.load(open(sys.argv[1]))["packages"]}
docs = {p["name"]: p for p in json.load(open(sys.argv[2]))["packages"]}
bad = [n for n, p in root.items() if n not in docs
       or (docs[n].get("rev"), docs[n].get("url")) != (p.get("rev"), p.get("url"))]
if bad:
    sys.exit("docs/api/lake-manifest.json does not pin these as the root's manifest does: "
             + ", ".join(bad))
EOF

# A link for the whole directory would put doc-gen4 in the root's packages.
if [ -L "$here/.lake/packages" ]; then
  echo "docs/api/.lake/packages is a link: remove it, this script makes the directory" >&2
  exit 1
fi
mkdir -p "$here/.lake/packages"
for name in $(python3 -I -c 'import json, sys; print(*(p["name"] for p in json.load(open(sys.argv[1]))["packages"]))' "$root/lake-manifest.json"); do
  link="$here/.lake/packages/$name"
  if [[ " $own " == *" $name "* ]]; then
    # Lake clones it here; a link in its place would make the build write into the root's.
    if [ -L "$link" ]; then rm "$link"; fi
    continue
  fi
  if [ ! -e "$root/.lake/packages/$name" ]; then
    echo "$root/.lake/packages/$name is missing: build Lanes first (lake exe cache get, lake build)" >&2
    exit 1
  fi
  if [ -e "$link" ] && [ ! -L "$link" ]; then
    echo "docs/api/.lake/packages/$name is a directory, not a link: remove it" >&2
    exit 1
  fi
  ln -sfn "../../../../.lake/packages/$name" "$link"
done
