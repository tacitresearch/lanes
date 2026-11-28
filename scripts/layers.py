#!/usr/bin/env python3
"""The layered packages of `docs/decisions/D99-layered-packages.md`: the files, lines and imports
between them.

Which package each module belongs to, and which packages each requires, is `LanesCli/Layers.lean`,
which this script reads; `lake exe lanes lint` checks every import of `Lanes/` against it (rule
`layering`), so this script does not. A file stays in the directory of its concern (D62), so a
package is read from `homes`, not from a directory.

    python3 scripts/layers.py            # files, lines and imports between packages

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
    """The package of `path`."""
    package = longest(PACKAGES, path)
    if package is None:
        sys.exit(f"no package for {path}: add it to {LAYERS}")
    return package[1]


def report_packages(mods):
    files, lines = collections.Counter(), collections.Counter()
    edges = collections.Counter()
    for name, (path, n, imports) in mods.items():
        p = home(path)
        files[p] += 1
        lines[p] += n
        for i in imports:
            if i in mods and (q := home(mods[i][0])) != p:
                edges[(p, q)] += 1
    for p in REQUIRES:
        print(f"{p:9} {files[p]:4} files {lines[p]:7} lines  requires "
              f"{', '.join(REQUIRES[p]) or 'nothing'}")
    print()
    for (p, q), n in sorted(edges.items()):
        print(f"{p:9} -> {q:9} {n:4} imports")


def main():
    report_packages(modules())


if __name__ == "__main__":
    main()
