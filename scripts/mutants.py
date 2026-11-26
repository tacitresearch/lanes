#!/usr/bin/env python3
"""Mutation gate for trusted code.

Each mutant below breaks one duty of a file listed in TRUSTED.md. The test suite must fail on
every one of them: a mutant that passes is a claim nothing checks. Run from the repository
root; it takes a minute or two per mutant, so it is run by hand and nightly, not on every push.

    python3 scripts/mutants.py            # all
    python3 scripts/mutants.py journal    # those whose name contains "journal"
"""
import pathlib
import subprocess
import sys

MUTANTS = [
    ("runtime: outputs handed over before the journal is written", "Lanes/Actors/Runtime.lean",
     """    if let some log := journal then unless entries.isEmpty do log.append entries
    rt.record events
    handOver outputs
""",
     """    rt.record events
    handOver outputs
    if let some log := journal then unless entries.isEmpty do log.append entries
"""),
    ("runtime: nothing handed over again after a restart", "Lanes/Actors/Runtime.lean",
     "  handOver outputs\n  let since := start.clock_ms", "  let since := start.clock_ms"),
    ("runtime: commands left in the inbox when the shard ends", "Lanes/Actors/Runtime.lean",
     """      | some (.idle _ done) => done.resolve false
      | some _ => pure ()
      | none => break""",
     "      | _ => break"),
    ("journal: no lock", "Lanes/Env/Journal.lean",
     "  unless ← lock.tryLock do", "  unless (← lock.tryLock) || true do"),
    ("journal: appended entries not flushed", "Lanes/Env/Journal.lean",
     "      append := write true", "      append := write false"),
    ("disk: a save replaces the journal before the snapshot is in place",
     "Lanes/Actors/Disk.lean",
     """[.putSnapshot (saved c system index image),
    .putJournal (file input system [.snapshot index])]""",
     """[.putJournal (file input system [.snapshot index]),
    .putSnapshot (saved c system index image)]"""),
    ("http: request ids start at zero after a restart", "Lanes/Env/Http.lean",
     "IO.mkRef ((log.map (·.index)).getD 0)", "IO.mkRef (0 : ReqId)"),
    ("http: a shard that ends on an error is not noticed", "Lanes/Env/Http.lean",
     "    if (← runtime.ended).isSome then", "    if false then"),
    ("http: the runtime is left running when the port is taken", "Lanes/Env/Http.lean",
     "      runtime.stop\n      throw e", "      throw e"),
    ("http client: no deadline", "Lanes/Env/HttpClient.lean",
     "try Async.race attempt patience", "try attempt"),
    ("http client: the socket of a call given up on is left open", "Lanes/Env/HttpClient.lean",
     "  finally socket.close", "  finally pure ()"),
    ("courier: stop leaves accepted connections open", "Lanes/Actors/Courier.lean",
     "(c.dialed.keys ++ c.inbound.keys).map .close", "c.dialed.keys.map .close"),
    ("courier: a second write is started while one is under way", "Lanes/Actors/Courier.lean",
     "(c.setWire to { w with line := .up conn true }, [.write conn bytes])",
     "(c, [.write conn bytes])"),
    ("courier: the queue has no limit", "Lanes/Actors/Courier.lean",
     "  if w.waiting.length < limits.queue then c.setWire",
     "  if w.waiting.length < limits.queue + 9 then c.setWire"),
]


def run(cmd):
    return subprocess.run(cmd, shell=True, capture_output=True, text=True, timeout=1800)


def main():
    wanted = sys.argv[1:]
    chosen = [m for m in MUTANTS if not wanted or any(w in m[0] for w in wanted)]
    survivors, stale = [], []
    for name, path, old, new in chosen:
        file = pathlib.Path(path)
        source = file.read_text()
        if source.count(old) != 1:
            stale.append(name)
            print(f"STALE    {name}: the text to change is not in {path} exactly once")
            continue
        try:
            file.write_text(source.replace(old, new))
            build = run("lake build lanesTest")
            if build.returncode != 0:
                print(f"killed   {name} (does not build)")
                continue
            try:
                test = run("timeout 300 ./.lake/build/bin/lanesTest")
                killed = test.returncode != 0
            except subprocess.TimeoutExpired:
                killed = True
            print(f"{'killed  ' if killed else 'SURVIVED'} {name}")
            if not killed:
                survivors.append(name)
        finally:
            file.write_text(source)
    run("lake build lanesTest")
    print(f"{len(chosen) - len(survivors) - len(stale)} killed, {len(survivors)} survived, "
          f"{len(stale)} stale")
    sys.exit(1 if survivors or stale else 0)


if __name__ == "__main__":
    main()
