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
     """      if let some log := journal then unless done.1.isEmpty do log.append done.1.toList
      rt.record done.2.1.toList
      handOver done.2.2.toList
""",
     """      rt.record done.2.1.toList
      handOver done.2.2.toList
      if let some log := journal then unless done.1.isEmpty do log.append done.1.toList
"""),
    ("runtime: nothing handed over again after a restart", "Lanes/Actors/Runtime.lean",
     "  handOver outputs\n  let since := start.clock_ms", "  let since := start.clock_ms"),
    ("runtime: commands left in the inbox when the shard ends", "Lanes/Actors/Runtime.lean",
     "  discard <| rt.inbox.modifyGet Mailbox.take\n", ""),
    ("runtime: a snapshot is not taken", "Lanes/Actors/Runtime.lean",
     "      (journal.bind (·.save)).filter fun _ => written ≥ max 1 rt.config.snapshotEvery",
     "      (journal.bind (·.save)).filter fun _ => false"),
    ("mailbox: no limit", "Lanes/Actors/Mailbox.lean",
     "  else if m.count < capacity then", "  else if m.count < capacity + 1000000 then"),
    ("mailbox: senders that wait for room are never woken", "Lanes/Actors/Mailbox.lean",
     "wake := m.waiting, closed := m.closed }", "wake := [], closed := m.closed }"),
    ("mailbox: the shard is not woken", "Lanes/Actors/Mailbox.lean",
     "    (.taken m.sleeper, { m with items := x :: m.items, count := m.count + 1, sleeper := none })",
     "    (.taken none, { m with items := x :: m.items, count := m.count + 1, sleeper := none })"),
    ("runtime: stop drops the commands already handed over", "Lanes/Actors/Runtime.lean",
     "    if batch.isEmpty && closed then break", "    if closed then break"),
    ("runtime: the clock starts from zero after a restart", "Lanes/Actors/Runtime.lean",
     "return since + ((← IO.monoMsNow) - epoch)", "return (← IO.monoMsNow) - epoch"),
    ("runtime: a handler that throws ends the shard", "Lanes/Actors/Runtime.lean",
     "    try onOutput out\n    catch e => IO.eprintln s!\"lanes: output handler failed: {e}\"",
     "    onOutput out"),
    ("runtime: the journal is closed before the inbox", "Lanes/Actors/Runtime.lean",
     """  for wake in ← rt.inbox.modifyGet Mailbox.close do wake.resolve ()
  discard <| rt.inbox.modifyGet Mailbox.take
  if let some log := journal then discard log.close.toBaseIO
""",
     """  if let some log := journal then discard log.close.toBaseIO
  for wake in ← rt.inbox.modifyGet Mailbox.close do wake.resolve ()
  discard <| rt.inbox.modifyGet Mailbox.take
"""),
    ("runtime: an inbox of no capacity takes nothing", "Lanes/Actors/Runtime.lean",
     "  max 1 rt.config.inboxCapacity", "  rt.config.inboxCapacity"),
    ("mailbox: parcels from other shards come out newest first", "Lanes/Actors/Mailbox.lean",
     "batch := m.urgent.reverse ++ m.items.reverse", "batch := m.urgent ++ m.items.reverse"),
    ("mailbox: the shard sleeps on what another shard sent", "Lanes/Actors/Mailbox.lean",
     "  if m.closed || !m.items.isEmpty || !m.urgent.isEmpty then (false, m)",
     "  if m.closed || !m.items.isEmpty then (false, m)"),
    ("mailbox: what another shard sends does not wake the shard", "Lanes/Actors/Mailbox.lean",
     "  else (some m.sleeper, { m with urgent := x :: m.urgent, sleeper := none })",
     "  else (some none, { m with urgent := x :: m.urgent, sleeper := none })"),
    ("courier: no rest after a process could not be reached", "Lanes/Actors/Courier.lean",
     "{ line := .resting (now_ms + limits.retry_ms) }", "{ line := .idle }"),
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
    ("courier: the parcel that makes it dial waits in a queue of no room",
     "Lanes/Actors/Courier.lean",
     "waiting := if limits.queue = 0 then {} else Fifo.push {} bytes }",
     "waiting := Fifo.push {} bytes }"),
    ("courier: bytes on a connection it dialed close it, and it goes on writing there",
     "Lanes/Actors/Courier.lean",
     "    | none => if c.dialed.contains conn then (c, []) else (c, [.close conn])",
     "    | none => (c, [.close conn])"),
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
