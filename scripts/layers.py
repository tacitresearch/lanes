#!/usr/bin/env python3
"""The import graph of `Lanes/` against the layered packages proposed in
`docs/decisions/new-layered-packages.md`.

Every module of `Lanes/` is given the package it would move to, read from `HOME` below by the
longest prefix of its path. An import is an upward edge when the imported module's package is
not the importer's and is not among the packages the importer's package requires (`REQUIRES`,
closed transitively). Each upward edge found today is printed with the fix the decision
proposes (`FIXES`); one with no fix listed is printed as `no fix listed`, and the script then
exits 1.

    python3 scripts/layers.py            # the upward edges, each with its fix
    python3 scripts/layers.py --packages # files, lines and edges between packages
    python3 scripts/layers.py --moves    # every file's old path and new path
    python3 scripts/layers.py --cost     # what the moves would change elsewhere

Run from the repository root. It reads the `import` lines only, as `lanes lint layering`
does, so it needs no build.
"""
import collections
import os
import re
import sys

# The packages, each with the packages it requires directly.
REQUIRES = {
    "model": [],
    "actors": ["model"],
    "std": ["model"],
    "runtime": ["actors"],
    "durable": ["runtime"],
    "web": ["durable", "std"],
    "postgres": ["runtime", "std"],
    "umbrella": ["web", "postgres"],
}

# Each directory of `Lanes/` as it is today, read as the layer its concern belongs to. The
# upward edges under this reading are the ones the decision has to fix.
AREA = [
    ("Lanes/Data/", "model"),
    ("Lanes/Proof/List", "model"),
    ("Lanes/Proof/Utf8.lean", "model"),
    ("Lanes/Proof/ByteArray.lean", "model"),
    ("Lanes/Proof/HashMap.lean", "model"),
    ("Lanes/Check/Search", "model"),
    ("Lanes/Check/Fingerprint.lean", "model"),
    ("Lanes/Semantics/Refinement.lean", "model"),
    ("Lanes/Core/", "actors"),
    ("Lanes/Proof/", "actors"),
    ("Lanes/Check/", "actors"),
    ("Lanes/Behaviours/", "actors"),
    ("Lanes/Outside/", "actors"),
    ("Lanes/Semantics/", "actors"),
    ("Lanes/Runtime/", "runtime"),
    ("Lanes/Net/", "runtime"),
    ("Lanes/Durable/", "durable"),
    ("Lanes/Lib/Postgres/", "postgres"),
    ("Lanes/Lib/", "std"),
    ("Lanes/Web/", "web"),
    ("Lanes/Testing", "web"),
    ("Lanes.lean", "umbrella"),
    ("Lanes/Proofs.lean", "umbrella"),
    ("Lanes/Semantics.lean", "umbrella"),
]

# Where each file of `Lanes/` goes: a path prefix today, its package, and its path inside that
# package. The longest prefix wins. A file that the decision splits in two is listed under the
# package of the part that keeps its name; the other part is in `SPLITS`.
HOME = [
    ("Lanes/Data/", "model", "Lanes/Data/"),
    ("Lanes/Durable/Frame.lean", "model", "Lanes/Data/Frame.lean"),
    ("Lanes/Proof/List/", "model", "Lanes/Proof/List/"),
    ("Lanes/Proof/List.lean", "model", "Lanes/Proof/List.lean"),
    ("Lanes/Proof/Utf8.lean", "model", "Lanes/Proof/Utf8.lean"),
    ("Lanes/Proof/ByteArray.lean", "model", "Lanes/Proof/ByteArray.lean"),
    ("Lanes/Proof/HashMap.lean", "model", "Lanes/Proof/HashMap.lean"),
    ("Lanes/Check/Search.lean", "model", "Lanes/Check/Search.lean"),
    ("Lanes/Check/SearchSound.lean", "model", "Lanes/Check/SearchSound.lean"),
    ("Lanes/Check/Fingerprint.lean", "model", "Lanes/Check/Fingerprint.lean"),
    ("Lanes/Semantics/Refinement.lean", "model", "Lanes/Semantics/Refinement.lean"),
    ("Lanes/Core/", "actors", "Lanes/Core/"),
    ("Lanes/Proof/", "actors", "Lanes/Proof/"),
    ("Lanes/Check/", "actors", "Lanes/Check/"),
    ("Lanes/Behaviours/", "actors", "Lanes/Behaviours/"),
    ("Lanes/Outside/", "actors", "Lanes/Outside/"),
    ("Lanes/Semantics/", "actors", "Lanes/Semantics/"),
    ("Lanes/Runtime/", "runtime", "Lanes/Runtime/"),
    ("Lanes/Net/Courier.lean", "runtime", "Lanes/Peers/Courier.lean"),
    ("Lanes/Net/CourierSound.lean", "runtime", "Lanes/Peers/CourierSound.lean"),
    ("Lanes/Net/IO/Peers.lean", "runtime", "Lanes/Peers/IO/Peers.lean"),
    ("Lanes/Outside/IO/Clock.lean", "runtime", "Lanes/Runtime/IO/Clock.lean"),
    ("Lanes/Behaviours/Jobs/IO/Pool.lean", "runtime", "Lanes/Runtime/IO/Jobs.lean"),
    ("Lanes/Semantics/FairRuns.lean", "runtime", "Lanes/Semantics/FairRuns.lean"),
    ("Lanes/Durable/", "durable", "Lanes/Durable/"),
    ("Lanes/Lib/Net/", "std", "Lanes/Net/"),
    ("Lanes/Web/IO/Tls.lean", "std", "Lanes/Net/IO/Tls.lean"),
    ("Lanes/Lib/Postgres/", "postgres", "Lanes/Postgres/"),
    ("Lanes/Lib/Mime/", "web", "Lanes/Http/"),
    ("Lanes/Lib/", "std", "Lanes/Lib/"),
    ("Lanes/Web/Http/SigV4", "web", "Lanes/S3/SigV4"),
    ("Lanes/Web/Http/", "web", "Lanes/Http/"),
    ("Lanes/Web/Html/", "web", "Lanes/Html/"),
    ("Lanes/Web/Auth/", "web", "Lanes/Auth/"),
    ("Lanes/Web/S3/", "web", "Lanes/S3/"),
    ("Lanes/Web/IO/S3.lean", "web", "Lanes/S3/IO/Client.lean"),
    ("Lanes/Web/IO/SignIn.lean", "web", "Lanes/Auth/IO/SignIn.lean"),
    ("Lanes/Web/IO/", "web", "Lanes/Http/IO/"),
    ("Lanes/Web/Transcode.lean", "web", "Lanes/Http/Transcode.lean"),
    ("Lanes/Net/IO/Node.lean", "web", "Lanes/Http/IO/Node.lean"),
    ("Lanes/Semantics/Front.lean", "web", "Lanes/Semantics/Front.lean"),
    ("Lanes/Testing/", "web", "Lanes/Testing/"),
    ("Lanes/Testing.lean", "web", "Lanes/Testing.lean"),
    ("Lanes.lean", "umbrella", "Lanes.lean"),
    ("Lanes/Proofs.lean", "umbrella", "Lanes/Proofs.lean"),
    ("Lanes/Semantics.lean", "umbrella", "Lanes/Semantics.lean"),
]

# Files split in two: the part that leaves, its package and its new path.
SPLITS = {
    "Lanes/Durable/Journal.lean": ("entries, replay, `recover`, `resume`, turns", "runtime",
                                   "Lanes/Runtime/Log.lean"),
    "Lanes/Behaviours/Jobs/IO/Pool.lean": ("`withHeader` and `call`, the worker over HTTP",
                                           "web", "Lanes/Http/IO/Jobs.lean"),
    "Lanes/Web/Http/Basic.lean": ("percent-encoding, names kept", "std",
                                  "Lanes/Net/Percent.lean"),
}

# The fix of each upward edge found today: (importer, imported) by module name.
FIXES = {
    ("Lanes.Durable.Journal", "Lanes.Runtime.KernelSound"):
        "split: the kernel's log moves to `Lanes.Runtime.Log`; the files stay",
    ("Lanes.Durable.Journal", "Lanes.Runtime.Wave"):
        "split: the kernel's log moves to `Lanes.Runtime.Log`; the files stay",
    ("Lanes.Durable.IO.Journal", "Lanes.Runtime.IO.Shell"):
        "none needed once durable requires runtime (the edge is downward)",
    ("Lanes.Runtime.Batch", "Lanes.Durable.Journal"):
        "import `Lanes.Runtime.Log`, the part of the journal that is the kernel's",
    ("Lanes.Runtime.Shard", "Lanes.Durable.Frame"):
        "move `Frame` to `Lanes/Data/Frame.lean`: the framing of a file and of a link",
    ("Lanes.Behaviours.Jobs.IO.Pool", "Lanes.Runtime.IO.Shell"):
        "move the handler to `Lanes/Runtime/IO/Jobs.lean`",
    ("Lanes.Behaviours.Jobs.IO.Pool", "Lanes.Web.IO.Client"):
        "split: `call` and `withHeader` move to `Lanes/Http/IO/Jobs.lean`",
    ("Lanes.Outside.IO.Clock", "Lanes.Runtime.IO.Shell"):
        "move to `Lanes/Runtime/IO/Clock.lean`: it performs on the runtime",
    ("Lanes.Lib.Net.Url", "Lanes.Web.Http.Basic"):
        "move percent-encoding to `Lanes/Net/Percent.lean`, names kept",
    ("Lanes.Lib.Mime.MediaType", "Lanes.Web.Http.Grammar"):
        "move media types to `Lanes/Http/MediaType.lean` (RFC 9110's)",
    ("Lanes.Lib.Postgres.IO.Client", "Lanes.Web.IO.Tls"):
        "move TLS to `Lanes/Net/IO/Tls.lean`, in std",
    ("Lanes.Net.IO.Node", "Lanes.Web.IO.Server"):
        "move to `Lanes/Http/IO/Node.lean`: a node with an HTTP front is web's",
    ("Lanes.Semantics.FairRuns", "Lanes.Runtime.KernelSound"):
        "move to runtime: fair runs of the kernel",
    ("Lanes.Semantics.Front", "Lanes.Web.Http.FrontSound"):
        "move to web: the liveness of the gate",
    ("Lanes.Testing.Http", "Lanes"):
        "import the web modules it uses, not the umbrella",
    ("Lanes.Proofs", "Lanes"):
        "none: an umbrella module",
    ("Lanes.Semantics", "Lanes"):
        "none: an umbrella module",
    ("Lanes.Semantics", "Lanes.Proofs"):
        "none: an umbrella module",
}

IMPORT = re.compile(r"^(?:public\s+|private\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\S+)")


def modules():
    """Each module of `Lanes/` and `Lanes.lean`: its path, lines and imports."""
    found = {}
    paths = ["Lanes.lean"]
    for root, _, files in os.walk("Lanes"):
        paths += [os.path.join(root, f) for f in files if f.endswith(".lean")]
    for path in sorted(paths):
        with open(path, encoding="utf-8") as f:
            text = f.read().splitlines()
        imports = [m.group(1) for line in text if (m := IMPORT.match(line))]
        found[path[:-5].replace("/", ".")] = (path, len(text), imports)
    return found


def home(path):
    best = max((p for p in HOME if path.startswith(p[0])), key=lambda p: len(p[0]),
               default=None)
    if best is None:
        sys.exit(f"no package for {path}: add it to HOME")
    prefix, package, new = best
    return package, new + path[len(prefix):]


def area(path):
    best = max((p for p in AREA if path.startswith(p[0])), key=lambda p: len(p[0]),
               default=None)
    if best is None:
        sys.exit(f"no layer for {path}: add it to AREA")
    return best[1]


def closure():
    out = {}
    for p in REQUIRES:
        seen, todo = set(), list(REQUIRES[p])
        while todo:
            q = todo.pop()
            if q not in seen:
                seen.add(q)
                todo += REQUIRES[q]
        out[p] = seen
    return out


def upward(mods, place):
    """The imports whose target's package is neither the importer's nor below it."""
    below = closure()
    edges = []
    for name, (path, _, imports) in mods.items():
        p = place(path)
        for i in imports:
            if i not in mods:
                continue  # Std, Lean, Mathlib or CSLib
            q = place(mods[i][0])
            if q != p and q not in below[p]:
                edges.append((name, p, i, q))
    return edges


def report_upward(mods):
    today = upward(mods, area)
    unfixed = [e for e in today if (e[0], e[2]) not in FIXES]
    print("Upward edges, with each directory of Lanes/ read as its layer:")
    for name, p, i, q in today:
        fix = FIXES.get((name, i), "no fix listed")
        print(f"  {name} ({p}) -> {i} ({q}): {fix}")
    after = upward(mods, lambda path: home(path)[0])
    print("Left after the moves, each fixed by a split or an edit of its imports:")
    for name, p, i, q in after:
        print(f"  {name} ({p}) -> {i} ({q}): {FIXES.get((name, i), 'no fix listed')}")
    foreign = [(n, i) for n, (_, _, imps) in mods.items() for i in imps
               if i.split(".")[0] in ("Mathlib", "Cslib")]
    print("Imports of Mathlib and CSLib, each replaced by a module of lanes-model:")
    for n, i in foreign:
        print(f"  {n} -> {i}")
    print(f"{len(today)} upward edges today, {len(unfixed)} without a fix; {len(after)} left "
          f"after the moves; {len(foreign)} imports of Mathlib or CSLib")
    return not unfixed and all((e[0], e[2]) in FIXES for e in after)


def report_packages(mods):
    files, lines = collections.Counter(), collections.Counter()
    edges = collections.Counter()
    for name, (path, n, imports) in mods.items():
        p = home(path)[0]
        files[p] += 1
        lines[p] += n
        for i in imports:
            if i in mods and (q := home(mods[i][0])[0]) != p:
                edges[(p, q)] += 1
    for p in REQUIRES:
        print(f"{p:9} {files[p]:4} files {lines[p]:7} lines  requires "
              f"{', '.join(REQUIRES[p]) or 'nothing'}")
    print()
    for (p, q), n in sorted(edges.items()):
        print(f"{p:9} -> {q:9} {n:4} imports")


def report_moves(mods):
    for name, (path, _, _) in mods.items():
        p, new = home(path)
        target = new if p == "umbrella" else f"packages/{p}/{new}"
        print(f"{path} -> {target}")
    for path, (what, p, new) in SPLITS.items():
        print(f"{path} (split: {what}) -> packages/{p}/{new}")


TEXT = (".lean", ".md", ".py", ".yml", ".yaml", ".toml", ".sh", ".tmpl", ".json")
SKIP = ("./.lake", "./.git", "./docs/decisions")
# Written by `lanes lint --fix`, or a record of the past, or this table.
GENERATED = {"docs/changes/before-fragments.md", "CHANGELOG.md", "scripts/layers.py"}


def report_cost(mods):
    renamed = {}
    moved = 0
    for name, (path, _, _) in mods.items():
        p, new = home(path)
        if p != "umbrella":
            moved += 1
        new_name = new[:-5].replace("/", ".")
        if new_name != name:
            renamed[name] = new_name
    old_paths = {path for _, (path, _, _) in mods.items() if home(path)[0] != "umbrella"}
    import_lines = path_refs = name_refs = 0
    files_touched = set()
    by_dir = collections.Counter()
    pattern_path = re.compile(r"Lanes/[A-Za-z0-9_/]+\.lean")
    pattern_name = re.compile(r"Lanes(?:\.[A-Z][A-Za-z0-9_]*)+")
    for root, dirs, fs in os.walk("."):
        if root.startswith(SKIP) or "/.lake" in root:
            dirs[:] = []
            continue
        for f in fs:
            full = os.path.join(root, f)
            if not f.endswith(TEXT) or f == "lake-manifest.json" or full[2:] in GENERATED:
                continue
            try:
                text = open(full, encoding="utf-8").read().splitlines()
            except UnicodeDecodeError:
                continue
            for line in text:
                hit = False
                m = IMPORT.match(line)
                if m and m.group(1) in renamed:
                    import_lines += 1
                    hit = True
                elif not m:
                    for ref in pattern_path.findall(line):
                        if ref in old_paths:
                            path_refs += 1
                            hit = True
                    for ref in pattern_name.findall(line):
                        if ref in renamed:
                            name_refs += 1
                            hit = True
                if hit:
                    files_touched.add(full[2:])
                    top = full[2:].split("/")[0]
                    by_dir[top if "/" in full[2:] else full[2:]] += 1
    print(f"{moved} files move into packages/, {len(renamed)} of them with a new module name")
    print(f"{len(SPLITS)} files split in two")
    print(f"{import_lines} import lines name a renamed module")
    print(f"{path_refs} references to an old path and {name_refs} to an old module name "
          f"outside import lines (docs/decisions and generated files keep theirs or are rewritten)")
    print(f"{len(files_touched)} files change, the moved ones included; lines changed by place:")
    for top, n in by_dir.most_common():
        print(f"  {top:24} {n:5}")


def main():
    mods = modules()
    if "--packages" in sys.argv:
        report_packages(mods)
    elif "--moves" in sys.argv:
        report_moves(mods)
    elif "--cost" in sys.argv:
        report_cost(mods)
    else:
        sys.exit(0 if report_upward(mods) else 1)


if __name__ == "__main__":
    main()
