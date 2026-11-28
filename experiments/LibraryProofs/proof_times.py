#!/usr/bin/env python3
"""Time the proofs of some theorems of a Lean file, best of a few runs.

  python3 experiments/LibraryProofs/proof_times.py FILE NAME... [--runs 3]

Lean's `trace.profiler` prints `elaborating proof of <name>` with the seconds it took; each name
here matches the last component of a declaration's name (`Refines.trans` matches
`Lanes.Refines.trans`). Run it from a directory whose `lake env` can elaborate FILE.
"""
import re
import subprocess
import sys

args = sys.argv[1:]
runs = 3
if "--runs" in args:
    k = args.index("--runs")
    runs = int(args[k + 1])
    del args[k:k + 2]
path, names = args[0], args[1:]
best = {}
for _ in range(runs):
    out = subprocess.run(
        ["lake", "env", "lean", "-Dtrace.profiler=true", "-Dtrace.profiler.threshold=0", path],
        capture_output=True, text=True).stdout
    seen = {}
    for m in re.finditer(r"\[Elab\.async\] \[([0-9.]+)\] \S+ elaborating proof of (\S+)", out):
        t, full = float(m.group(1)), m.group(2)
        for n in names:
            if full == n or full.endswith("." + n):
                seen[n] = seen.get(n, 0.0) + t
    for n, t in seen.items():
        best[n] = min(best.get(n, t), t)
total = 0.0
for n in names:
    t = best.get(n)
    print(f"{n}\t{'?' if t is None else f'{t * 1000:.0f} ms'}")
    total += t or 0.0
print(f"total\t{total * 1000:.0f} ms")
