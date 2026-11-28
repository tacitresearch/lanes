#!/usr/bin/env python3
"""The layered packages of `docs/decisions/D99-layered-packages.md`, and the moves that put each
file of `Lanes/` in its package's directory.

Which package each module belongs to, and which packages each requires, is `LanesCli/Layers.lean`,
which this script reads; `lake exe lanes lint` checks every import of `Lanes/` against it (rule
`layering`), so this script does not. `MOVES` below gives each file's path inside its package.

    python3 scripts/layers.py            # files, lines and imports between packages
    python3 scripts/layers.py --moves    # every file's old path and new path
    python3 scripts/layers.py --cost     # what the moves would change elsewhere

Run from the repository root. It reads the `import` lines only, so it needs no build.
"""
import collections
import os
import re
import sys

LAYERS = "LanesCli/Layers.lean"


def read_layers():
    """The packages each package requires, and the package of each path prefix, from `LAYERS`."""
    text = open(LAYERS, encoding="utf-8").read()
    requires_block = text.split("def Package.requires")[1].split("\n\n")[0]
    requires = {p: re.findall(r"\.(\w+)", deps)
                for p, deps in re.findall(r"\| \.(\w+) => \[([^\]]*)\]", requires_block)}
    homes_block = text.split("def homes")[1].split("\n]")[0]
    homes = re.findall(r'\("([^"]+)", \.(\w+)\)', homes_block)
    return requires, homes


REQUIRES, PACKAGES = read_layers()

# Each file's path inside its package: a path prefix today and the path it becomes. The longest
# prefix wins; a path that no prefix names keeps its path.
MOVES = [
    ("Lanes/Outside/IO/Clock.lean", "Lanes/Runtime/IO/Clock.lean"),
    ("Lanes/Behaviours/Jobs/IO/Pool.lean", "Lanes/Runtime/IO/Jobs.lean"),
    ("Lanes/Lib/Net/", "Lanes/Net/"),
    ("Lanes/Web/IO/Tls.lean", "Lanes/Net/IO/Tls.lean"),
    ("Lanes/Lib/Postgres/", "Lanes/Postgres/"),
    ("Lanes/Lib/Mime/", "Lanes/Http/"),
    ("Lanes/Web/Http/SigV4", "Lanes/S3/SigV4"),
    ("Lanes/Web/Http/", "Lanes/Http/"),
    ("Lanes/Web/Html/", "Lanes/Html/"),
    ("Lanes/Web/Auth/", "Lanes/Auth/"),
    ("Lanes/Web/S3/", "Lanes/S3/"),
    ("Lanes/Web/IO/S3.lean", "Lanes/S3/IO/Client.lean"),
    ("Lanes/Web/IO/SignIn.lean", "Lanes/Auth/IO/SignIn.lean"),
    ("Lanes/Web/IO/", "Lanes/Http/IO/"),
]

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


def longest(table, path):
    return max((p for p in table if path.startswith(p[0])), key=lambda p: len(p[0]),
               default=None)


def home(path):
    """The package of `path`, and its path inside the package."""
    package = longest(PACKAGES, path)
    if package is None:
        sys.exit(f"no package for {path}: add it to {LAYERS}")
    move = longest(MOVES, path)
    new = path if move is None else move[1] + path[len(move[0]):]
    return package[1], new


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
    print(f"{import_lines} import lines name a renamed module")
    print(f"{path_refs} references to an old path and {name_refs} to an old module name "
          f"outside import lines (docs/decisions and generated files keep theirs or are rewritten)")
    print(f"{len(files_touched)} files change, the moved ones included; lines changed by place:")
    for top, n in by_dir.most_common():
        print(f"  {top:24} {n:5}")


def main():
    mods = modules()
    if "--moves" in sys.argv:
        report_moves(mods)
    elif "--cost" in sys.argv:
        report_cost(mods)
    else:
        report_packages(mods)


if __name__ == "__main__":
    main()
