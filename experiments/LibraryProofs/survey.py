#!/usr/bin/env python3
"""Find which theorems of Lanes are already in Lean core, Batteries or Mathlib.

For every `theorem` in the given Lean files, the statement is copied into a file that imports
only the library under test (`--import Mathlib` or `--import Std`), with the `variable` lines of
its section, as `example <statement> := by exact?`. A statement that does not elaborate there
mentions a definition of Lanes, so no library can have it. One that `exact?` closes is in the
library, and `exact?` names the lemma.

  python3 experiments/LibraryProofs/survey.py --import Mathlib --out OUT.lean FILE...
  lake env lean OUT.lean > OUT.log 2>&1
  python3 experiments/LibraryProofs/survey.py --parse OUT.lean OUT.log
"""
import re
import sys

OPEN = "([{⟨⦃"
CLOSE = ")]}⟩⦄"
START = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?theorem\s+(\S+)(.*)$")


def statement(lines, i, rest):
    """The signature after the theorem's name, up to its `:=`, `|` or `where`."""
    text = ""
    part = rest
    depth = 0
    j = i
    while True:
        for k, ch in enumerate(part):
            if ch in OPEN:
                depth += 1
            elif ch in CLOSE:
                depth -= 1
            elif depth == 0 and part.startswith(":=", k):
                return text + part[:k], j
        text += part
        j += 1
        if j >= len(lines):
            return None, j
        part = lines[j]
        if depth == 0 and (re.match(r"^\s*\|", part) or re.match(r"^\s*where\b", part)):
            return text, j
        text += "\n"


def extract(path):
    lines = open(path, encoding="utf-8").read().split("\n")
    out = []
    variables = []
    stack = []
    i = 0
    while i < len(lines):
        line = lines[i]
        if line.startswith("open ") and not line.rstrip().endswith(" in"):
            variables.append(line)
        elif line.startswith("variable"):
            block = [line]
            while i + 1 < len(lines) and lines[i + 1].startswith("  ") and not START.match(lines[i + 1]):
                i += 1
                block.append(lines[i])
            variables.append("\n".join(block))
        elif re.match(r"^(section|namespace)\b", line):
            stack.append(len(variables))
        elif re.match(r"^end\b", line):
            variables = variables[:stack.pop()] if stack else []
        m = START.match(line)
        if m:
            sig, j = statement(lines, i, m.group(2))
            if sig is not None and sig.strip():
                out.append((m.group(1), list(variables), sig.strip()))
            i = max(i, j - 1)
        i += 1
    return out


def generate(imp, files, dest, tactic="exact?", only=None):
    with open(dest, "w", encoding="utf-8") as f:
        f.write(f"import {imp}\n\nset_option maxHeartbeats 400000\nset_option relaxedAutoImplicit false\nset_option maxErrors 1000000\n\n")
        n = 0
        for path in files:
            for name, variables, sig in extract(path):
                n += 1
                if only is not None and n not in only:
                    continue
                f.write(f"-- CASE {n} {path} {name}\nsection\n")
                for v in variables:
                    f.write(v + "\n")
                f.write(f"example {sig} := by\n  {tactic}\nend\n\n")
    print(f"{n} statements written to {dest}")


def parse(lean, log):
    """Each case gives one message: `exact?`'s error, with its position, or its `Try this`,
    which `lean` prints without one. So a `Try this` is the next case after the last one placed."""
    starts = []
    for no, line in enumerate(open(lean, encoding="utf-8").read().split("\n"), 1):
        m = re.match(r"^-- CASE (\d+) (\S+) (\S+)$", line)
        if m:
            starts.append((no, m.group(2), m.group(3)))
    import bisect
    nos = [s[0] for s in starts]
    status = {k: ("no-message", "") for k in range(len(starts))}
    last = -1
    lines = open(log, encoding="utf-8").read().split("\n")
    i = 0
    while i < len(lines):
        line = lines[i]
        m = re.match(r"^.*?\.lean:(\d+):(\d+): (error|warning)(?:\([^)]*\))?: ?(.*)$", line)
        if m:
            k = bisect.bisect_right(nos, int(m.group(1))) - 1
            if "could not close the goal" in m.group(4):
                status[k] = ("not-found", "")
            elif m.group(3) == "error":
                status[k] = ("elab-error", m.group(4)[:120])
            last = max(last, k)
        elif line.startswith("Try this:"):
            lemma = lines[i + 1].strip() if i + 1 < len(lines) else ""
            lemma = re.sub(r"^\[apply\]\s*", "", lemma)
            last += 1
            if last < len(starts):
                status[last] = ("found", lemma)
        i += 1
    counts = {}
    for k, (st, info) in status.items():
        counts[st] = counts.get(st, 0) + 1
        if st == "found":
            print(f"FOUND\t{starts[k][1]}\t{starts[k][2]}\t{info}")
    for k, (st, info) in status.items():
        if st != "found":
            print(f"{st.upper()}\t{starts[k][1]}\t{starts[k][2]}\t{info}")
    print("COUNTS", counts)


if __name__ == "__main__":
    args = sys.argv[1:]
    if args[0] == "--parse":
        parse(args[1], args[2])
    elif args[0] == "--elaborates":
        # Case numbers whose statement elaborated: from a log of a run with `sorry`.
        lean, log = args[1], args[2]
        bad = set()
        starts = []
        for no, line in enumerate(open(lean, encoding="utf-8").read().split("\n"), 1):
            m = re.match(r"^-- CASE (\d+) ", line)
            if m:
                starts.append((no, int(m.group(1))))
        import bisect
        nos = [s[0] for s in starts]
        for line in open(log, encoding="utf-8"):
            m = re.match(r"^.*?\.lean:(\d+):\d+: error", line)
            if m:
                k = bisect.bisect_right(nos, int(m.group(1))) - 1
                if k >= 0:
                    bad.add(starts[k][1])
        good = [c for _, c in starts if c not in bad]
        print(",".join(map(str, good)))
    else:
        imp = args[1]
        dest = args[3]
        tactic = "exact?"
        only = None
        rest = args[4:]
        if rest and rest[0] == "--sorry":
            tactic = "sorry"
            rest = rest[1:]
        if rest and rest[0].startswith("--only="):
            only = set(int(x) for x in open(rest[0][7:]).read().strip().split(",") if x)
            rest = rest[1:]
        generate(imp, rest, dest, tactic, only)
