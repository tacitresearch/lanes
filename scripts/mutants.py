#!/usr/bin/env python3
"""Mutation gate for trusted code.

Each mutant below breaks one duty of a file listed in TRUSTED.md. The test suite must fail on
every one of them: a mutant that passes is a claim nothing checks. Run from the repository
root; it takes a minute or two per mutant, so it is run by hand and nightly, not on every push.

    python3 scripts/mutants.py            # all
    python3 scripts/mutants.py journal    # those whose name contains "journal"
"""
import os
import pathlib
import signal
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
    ("runtime: the entries of earlier runs do not count towards the next save",
     "Lanes/Actors/Runtime.lean",
     "  let mut written := (journal.map (·.past.length)).getD 0", "  let mut written := 0"),
    ("journal: what is cut off is not kept", "Lanes/Env/Journal.lean",
     """      IO.FS.writeBinFile (store.path.addExtension "cut")
        (disk.journal.extract found.size disk.journal.size)
""",
     "      pure ()\n"),
    ("journal: the mark of a save is not counted", "Lanes/Env/Journal.lean",
     "        (perform store.path handle true)\n      count.modify (· + 1)",
     "        (perform store.path handle true)"),
    ("http: an answered request stays among those in flight", "Lanes/Env/Http.lean",
     "        modify (·.erase id)\n        return waiter", "        return waiter"),
    ("http: a request refused for a full inbox stays among those in flight",
     "Lanes/Env/Http.lean",
     "      modify (·.erase id)\n      return false", "      return false"),
    ("node: peers are left listening when the server cannot start", "Lanes/Env/Node.lean",
     "      peers.stop\n      throw e", "      throw e"),
    ("node: an output that is neither a response nor a parcel is dropped",
     "Lanes/Env/Node.lean",
     "        | .inl out => onOutput out", "        | .inl _ => pure ()"),
    ("peers: the end of an accepted connection is not reported", "Lanes/Env/Peers.lean",
     """          background (listen events conn socket fun bytes =>
            discard <| post events (.received conn bytes))
""",
     """          background do
            try
              repeat
                let some bytes ← socket.recv? 65536 | break
                discard <| post events (.received conn bytes)
            catch _ => pure ()
"""),
    ("peers: a connection that cannot be made is not reported", "Lanes/Env/Peers.lean",
     """              listen events conn socket fun _ => pure ()
            catch _ => discard <| post events (.broken conn (← IO.monoMsNow))
""",
     """              listen events conn socket fun _ => pure ()
            catch _ => pure ()
"""),
    ("peers: a connection this side made is not read", "Lanes/Env/Peers.lean",
     """              discard <| post events (.connected conn)
              listen events conn socket fun _ => pure ()
""",
     "              discard <| post events (.connected conn)\n"),
    ("peers: a parcel over the limit is sent", "Lanes/Env/Peers.lean",
     "\n      && bytes.size ≤ peers.config.limits.maxParcelBytes then", " then"),
    ("peers: what the courier asks for at once is done last first", "Lanes/Env/Peers.lean",
     "    for action in actions do", "    for action in actions.reverse do"),
    ("peers: a shard with peers does not use its journal", "Lanes/Env/Peers.lean",
     "runtimeConfig (journal := journal) fun", "runtimeConfig (journal := none) fun"),
    ("node: the journal is not used", "Lanes/Env/Node.lean",
     "config runtimeConfig (log := log) fun", "config runtimeConfig (log := none) fun"),
    ("node: a parcel the shard puts out is not sent", "Lanes/Env/Node.lean",
     "        | .inr parcel => peers.send parcel", "        | .inr _ => pure ()"),
    ("node: a parcel that arrives is not handed to the shard", "Lanes/Env/Node.lean",
     "  ready.resolve fun parcel => discard <| server.tryInput (.inr parcel)",
     "  ready.resolve fun _ => pure ()"),
]


CHECKS = {
    "lanesTest": dict(cwd=".", build="lake build lanesTest",
                      run="./.lake/build/bin/lanesTest", limit_s=120),
    "raftProcs": dict(cwd="systems/raft-kv", build="lake build raftNode raftProcs",
                      run="./.lake/build/bin/raftProcs", limit_s=300),
}

WORDS = {
    "failed": "killed  ", "nobuild": "killed  ", "crashed": "CRASHED ", "hung": "HUNG    ",
    "passed": "SURVIVED",
}


def sh(cmd, cwd=".", limit_s=1800):
    """The exit code and output of `cmd`; the code is `None` if it did not end in time. The
    command has a process group of its own, so that what it started ends with it."""
    proc = subprocess.Popen(cmd, shell=True, cwd=cwd, text=True, start_new_session=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    try:
        out, _ = proc.communicate(timeout=limit_s)
        return proc.returncode, out
    except subprocess.TimeoutExpired:
        os.killpg(proc.pid, signal.SIGKILL)
        out, _ = proc.communicate()
        return None, out


def verdict(check):
    """How the check ends on the code as it now is, and a word about it."""
    code, out = sh(check["build"], check["cwd"])
    if code != 0:
        errors = [line.strip() for line in out.splitlines() if "error:" in line]
        return "nobuild", f"does not build ({errors[0] if errors else 'no error reported'})"
    code, out = sh(check["run"], check["cwd"], check["limit_s"])
    failed = [line[5:] for line in out.splitlines() if line.startswith("FAIL ")]
    if code is None:
        return "hung", f"no test failed and the run had not ended after {check['limit_s']} s"
    if failed:
        more = f", and {len(failed) - 1} more" if len(failed) > 1 else ""
        return "failed", f"FAIL {failed[0]}{more}"
    if code != 0:
        return "crashed", f"no test failed and the run ended with code {code}"
    return "passed", "every test passed"


def main():
    args = sys.argv[1:]
    wanted = [a for a in args if not a.startswith("--")]
    entries = [(m[0], m[1], m[2], m[3], m[4] if len(m) > 4 else "lanesTest") for m in MUTANTS]
    if "--list" in args:
        for name, path, _, _, check in entries:
            print(f"{name}\n    {path}, must fail {check}")
        print(f"{len(entries)} mutants")
        return
    if wanted:
        chosen = [m for m in entries if any(w in m[0] for w in wanted)]
    else:
        chosen = [m for m in entries if "--all" in args or m[4] == "lanesTest"]
    counts = {}
    for name, path, old, new, check in chosen:
        file = pathlib.Path(path)
        source = file.read_text()
        if source.count(old) != 1:
            counts["stale"] = counts.get("stale", 0) + 1
            print(f"STALE    {name}: the text to change is not in {path} exactly once")
            continue
        try:
            file.write_text(source.replace(old, new))
            how, word = verdict(CHECKS[check])
        finally:
            file.write_text(source)
        counts[how] = counts.get(how, 0) + 1
        by = "" if check == "lanesTest" else f" [{check}]"
        print(f"{WORDS[how]} {name}{by}: {word}", flush=True)
    sh("lake build lanesTest")

    def n(how):
        return counts.get(how, 0)

    print(f"{n('failed')} killed by a test that fails, {n('nobuild')} do not build, "
          f"{n('hung')} only hang, {n('crashed')} only crash, {n('passed')} survived, "
          f"{n('stale')} stale; {len(entries) - len(chosen)} not run")
    sys.exit(1 if n("passed") or n("stale") else 0)


if __name__ == "__main__":
    main()
