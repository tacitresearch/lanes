#!/usr/bin/env python3
"""Mutation gate for trusted code.

Each mutant below breaks one duty of a file listed in TRUSTED.md. A check must fail on every
one of them: a mutant that passes is a claim nothing checks. The check is `lanesTest` unless
the entry names another as its fifth part (see `CHECKS`). Run from the repository root; it
takes a minute or two per mutant, so it is run by hand and nightly, not on every push.

    python3 scripts/mutants.py            # those checked by lanesTest
    python3 scripts/mutants.py --all      # also those checked by something slower
    python3 scripts/mutants.py journal    # those whose name contains "journal"
    python3 scripts/mutants.py --list     # print every mutant and run nothing

CI runs the list in pieces on several machines and then puts the verdicts together:

    python3 scripts/mutants.py --all --shard 2/8 --baseline --json v2.json
    python3 scripts/mutants.py --collect v*.json

`--shard i/n` takes every n-th mutant from the i-th on, so the n shards hold each mutant
exactly once (`--list --shard i/n` shows a shard). `--baseline` first runs each check the
shard needs on the code as it is, and stops if one does not pass: a broken baseline would kill
every mutant. `--json` writes the verdicts to a file; `--collect` reads such files, checks that
together they hold every mutant once, prints them, and fails as the gate does.

A mutant is killed when a test fails on it, or when it no longer builds, which is how a
theorem kills one. A run that does not end, or ends without a test that failed, has noticed
the mutant and asserted nothing: it is reported as HUNG or CRASHED, apart from the kills, and
is a test to write. The gate fails on a mutant that survives, on one that only hangs, and on
one whose text is no longer in the file.

This is a list of known ways to break trusted code, each caught. It is not a measure of what
the tests cover: each row of TRUSTED.md says what its tests check and what they do not.
"""
import json
import os
import pathlib
import signal
import subprocess
import sys
import tempfile

MUTANTS = [
    ("runtime: nothing handed over again after a restart", "Lanes/Runtime/IO/Shell.lean",
     "  handOver outputs\n  let since := start.clock_ms", "  let since := start.clock_ms"),
    ("runtime: the outputs an older version had not handed over are dropped at a migration",
     "Lanes/Runtime/IO/Shell.lean", "    deliver log.pending\n", ""),
    ("journal: a migration is not written", "Lanes/Durable/IO/Journal.lean",
     "      migrate := upgraded.writes.forM (perform store.path handle true)\n", ""),
    ("runtime: commands left in the inbox when the shard ends", "Lanes/Runtime/IO/Shell.lean",
     "  discard <| rt.inbox.modifyGet Mailbox.take\n", ""),
    ("runtime: a snapshot is not taken", "Lanes/Runtime/IO/Shell.lean",
     "  let snapshotEvery := save.map fun _ => rt.config.snapshotEvery",
     "  let snapshotEvery : Option Nat := none"),
    ("runtime: a save the batch asks for is not performed", "Lanes/Runtime/IO/Shell.lean",
     "      | .save image => if let some save := save then save image",
     "      | .save _ => pure ()"),
    ("runtime release: an actor is never released", "Lanes/Runtime/Kernel.lean",
     "    { k with cells := k.cells.erase i }\n  else k", "    k\n  else k"),
    ("runtime release: an actor with a timer pending is released", "Lanes/Runtime/Kernel.lean",
     "if (sys.actor i).fresh c.state && c.up && c.timers.isEmpty then",
     "if (sys.actor i).fresh c.state && c.up then"),
    ("runtime release: an actor is released whatever its state", "Lanes/Runtime/Kernel.lean",
     "if (sys.actor i).fresh c.state && c.up && c.timers.isEmpty then",
     "if c.up && c.timers.isEmpty then"),
    ("mailbox: no limit", "Lanes/Runtime/Mailbox.lean",
     "  else if m.count < capacity then", "  else if m.count < capacity + 1000000 then"),
    ("mailbox: senders that wait for room are never woken", "Lanes/Runtime/Mailbox.lean",
     "wake := m.waiting, closed := m.closed }", "wake := [], closed := m.closed }"),
    ("mailbox: the shard is not woken", "Lanes/Runtime/Mailbox.lean",
     "    (.taken m.sleeper, { m with items := x :: m.items, count := m.count + 1, sleeper := none })",
     "    (.taken none, { m with items := x :: m.items, count := m.count + 1, sleeper := none })"),
    ("runtime: stop drops the commands already handed over", "Lanes/Runtime/IO/Shell.lean",
     "    if batch.isEmpty && closed then break", "    if closed then break"),
    ("runtime: the clock starts from zero after a restart", "Lanes/Runtime/IO/Shell.lean",
     "return since + ((← IO.monoMsNow) - epoch)", "return (← IO.monoMsNow) - epoch"),
    ("runtime: a handler that throws ends the shard", "Lanes/Runtime/IO/Shell.lean",
     "    try onOutput out\n    catch e => IO.eprintln s!\"lanes: output handler failed: {e}\"",
     "    onOutput out"),
    ("runtime: the journal is closed before the inbox", "Lanes/Runtime/IO/Shell.lean",
     """  for w in ← rt.inbox.modifyGet Mailbox.close do rt.wake w
  discard <| rt.inbox.modifyGet Mailbox.take
  if let some log := journal then discard log.close.toBaseIO
""",
     """  if let some log := journal then discard log.close.toBaseIO
  for w in ← rt.inbox.modifyGet Mailbox.close do rt.wake w
  discard <| rt.inbox.modifyGet Mailbox.take
"""),
    ("runtime: the shard sleeps past its next timer", "Lanes/Runtime/IO/Shell.lean",
     "    | .for_ms ms => rt.parker.parkAtMost ms", "    | .for_ms ms => rt.parker.parkAtMost (ms + 3000)"),
    ("runtime: an inbox of no capacity takes nothing", "Lanes/Runtime/IO/Shell.lean",
     "  max 1 rt.config.inboxCapacity", "  rt.config.inboxCapacity"),
    ("courier: no rest after a process could not be reached", "Lanes/Net/Courier.lean",
     "{ line := .resting (now_ms + limits.retry_ms) }", "{ line := .idle }"),
    ("journal: no lock", "Lanes/Durable/IO/Journal.lean",
     "  unless ← lock.tryLock do", "  unless (← lock.tryLock) || true do"),
    ("journal: appended entries not flushed", "Lanes/Durable/IO/Journal.lean",
     "      append := write true", "      append := write false"),
    ("disk: a save replaces the journal before the snapshot is in place",
     "Lanes/Durable/Disk.lean",
     """[.putSnapshot (saved c system index image),
    .putJournal (file input system [.snapshot index])]""",
     """[.putJournal (file input system [.snapshot index]),
    .putSnapshot (saved c system index image)]"""),
    ("http: request ids start at zero after a restart", "Lanes/Web/IO/Server.lean",
     "Mutex.new (Waiting.start ((log.map (·.index)).getD 0))", "Mutex.new (Waiting.start 0)"),
    ("http: a shard that ends on an error is not noticed", "Lanes/Web/IO/Server.lean",
     "    if (← runtime.ended).isSome then", "    if false then"),
    ("http: the runtime is left running when the port is taken", "Lanes/Web/IO/Server.lean",
     "      runtime.stop\n      throw e", "      throw e"),
    ("http: a request is journalled as it came, not as the bridge prepared it",
     "Lanes/Web/IO/Server.lean", "    let request := prepare request\n", ""),
    ("http: serve names its journal by the application alone, so an old gate's is read",
     "Lanes/Web/IO/Server.lean", "system := config.journalName", "system := config.system"),
    ("http: a connection's deadline is never acted on", "Lanes/Web/IO/Server.lean",
     "        if t ≤ now then c.tell .alarm", "        if t ≤ now && false then c.tell .alarm"),
    ("http: every answer goes to the first request of its connection", "Lanes/Web/IO/Server.lean",
     "tell ctx line false (.conn (.answered seq r))", "tell ctx line false (.conn (.answered 0 r))"),
    ("http: no bound on connections", "Lanes/Web/IO/Server.lean",
     "c.count.admit config.connections_max", "c.count.admit (config.connections_max + 1)"),
    ("http: a connection is closed at once, with what the client still sends unread",
     "Lanes/Web/IO/Server.lean",
     "    try socket.shutdown catch _ => pure ()\n    let drain",
     "    socket.close\n    let drain"),
    ("http: stop does not tell the open connections", "Lanes/Web/IO/Server.lean",
     "  for (_, c) in alive do c.tell (.conn .stop)", "  for (_, _) in alive do pure ()"),
    ("http: what the connection asks for is done last first", "Lanes/Web/IO/Server.lean",
     "  let mut todo := actions\n", "  let mut todo := actions.reverse\n"),
    ("http stream: the head of a request that streams is not kept, so its pieces are refused",
     "Lanes/Web/IO/Server.lean", "          | some id => (seq, id) :: heads", "          | some _ => heads"),
    ("http stream: a piece is not tagged with its head", "Lanes/Web/IO/Server.lean",
     """(.conn (.took seq index r))
        match loop.heads.lookup seq with
        | some id => discard <| ctx.submitStream (Stream.tag request id) reply""",
     """(.conn (.took seq index r))
        match loop.heads.lookup seq with
        | some _ => discard <| ctx.submitStream request reply"""),
    ("http stream: a piece's answer goes to the piece before", "Lanes/Web/IO/Server.lean",
     "(.conn (.took seq index r))", "(.conn (.took seq (index - 1) r))"),
    ("http stream: a pull's answer goes to the next pull", "Lanes/Web/IO/Server.lean",
     "(.conn (.pulled seq index r))", "(.conn (.pulled seq (index + 1) r))"),
    ("http stream: the connection is never told that what it wrote was sent",
     "Lanes/Web/IO/Server.lean", "  | .sent => react ctx line { loop with sentSet := false } .sent",
     "  | .sent => return { loop with sentSet := false }"),
    ("http stream: a time to look again that is no deadline is not acted on",
     "Lanes/Web/IO/Server.lean", "    (conn.wakeAt config.conn)", "    none"),
    ("http client: a stream of events is read past its deadline", "Lanes/Web/IO/Client.lean",
     "(Async.race (try read catch _ => pure ()) (Async.sleep (.ofNat timeout_ms)))",
     "(try read catch _ => pure ())"),
    ("http client: no deadline", "Lanes/Web/IO/Client.lean",
     "try Async.race attempt patience", "try attempt"),
    ("http client: the socket of a call given up on is left open", "Lanes/Web/IO/Client.lean",
     "  finally socket.close", "  finally pure ()"),
    ("jobs: a result is handed back as another attempt's", "Lanes/Behaviours/Jobs/IO/Pool.lean",
     "deliver (port.result key attempt r)", "deliver (port.result key (attempt + 1) r)"),
    ("jobs: no result is handed back", "Lanes/Behaviours/Jobs/IO/Pool.lean",
     "discard <| deliver (port.result key attempt r)",
     "discard <| pure (port.result key attempt r)"),
    ("jobs: a call goes without its key", "Lanes/Behaviours/Jobs/IO/Pool.lean",
     "Http.Client.exchange (withHeader header (keyText key) job) config",
     "Http.Client.exchange job config"),
    ("jobs: an attempt is performed on the shard's thread", "Lanes/Behaviours/Jobs/IO/Pool.lean",
     "    background (prio := prio) do\n", "    discard <| pure prio\n    id do\n"),
    ("courier: stop leaves accepted connections open", "Lanes/Net/Courier.lean",
     "(c.dialed.keys ++ c.inbound.keys).map .close", "c.dialed.keys.map .close"),
    ("courier: a second write is started while one is under way", "Lanes/Net/Courier.lean",
     "(c.setWire to { w with line := .up conn true }, [.write conn bytes])",
     "(c, [.write conn bytes])"),
    ("courier: the queue has no limit", "Lanes/Net/Courier.lean",
     "  if w.waiting.length < limits.queue then c.setWire",
     "  if w.waiting.length < limits.queue + 9 then c.setWire"),
    ("runtime: the entries of earlier runs do not count towards the next save",
     "Lanes/Runtime/IO/Shell.lean",
     "  let mut written := (journal.map (·.past.length)).getD 0", "  let mut written := 0"),
    ("journal: what is cut off is not kept", "Lanes/Durable/IO/Journal.lean",
     """        IO.FS.writeBinFile (store.path.addExtension "cut")
          (disk.journal.extract found.size disk.journal.size)
""",
     "        pure ()\n"),
    ("journal: the mark of a save is not counted", "Lanes/Durable/IO/Journal.lean",
     "        (perform store.path handle true)\n      count.modify (· + 1)",
     "        (perform store.path handle true)"),
    ("node: peers are left listening when the server cannot start", "Lanes/Net/IO/Node.lean",
     "      peers.stop\n      throw e", "      throw e"),
    ("node: an output that is neither a response nor a parcel is dropped",
     "Lanes/Net/IO/Node.lean",
     "        | .inl out => onOutput out", "        | .inl _ => pure ()"),
    ("peers: the end of an accepted connection is not reported", "Lanes/Net/IO/Peers.lean",
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
    ("peers: a connection that cannot be made is not reported", "Lanes/Net/IO/Peers.lean",
     """              listen events conn socket fun _ => pure ()
            catch _ => discard <| post events (.broken conn (← IO.monoMsNow))
""",
     """              listen events conn socket fun _ => pure ()
            catch _ => pure ()
"""),
    ("peers: a connection this side made is not read", "Lanes/Net/IO/Peers.lean",
     """              discard <| post events (.connected conn)
              listen events conn socket fun _ => pure ()
""",
     "              discard <| post events (.connected conn)\n"),
    ("peers: a parcel over the limit is sent", "Lanes/Net/IO/Peers.lean",
     "\n      && bytes.size ≤ peers.config.limits.maxParcelBytes then", " then"),
    ("peers: what the courier asks for at once is done last first", "Lanes/Net/IO/Peers.lean",
     "    for action in actions do", "    for action in actions.reverse do"),
    ("peers: a shard with peers does not use its journal", "Lanes/Net/IO/Peers.lean",
     "runtimeConfig (journal := journal) fun", "runtimeConfig (journal := none) fun"),
    ("node: the journal is not used", "Lanes/Net/IO/Node.lean",
     "config runtimeConfig (log := log) fun", "config runtimeConfig (log := none) fun"),
    ("node: a parcel the shard puts out is not sent", "Lanes/Net/IO/Node.lean",
     "        | .inr parcel => peers.send parcel", "        | .inr _ => pure ()"),
    ("node: a parcel that arrives is not handed to the shard", "Lanes/Net/IO/Node.lean",
     "  ready.resolve fun parcel => discard <| server.tryInput (.inr parcel)",
     "  ready.resolve fun _ => pure ()"),
    ("journal: after a save, entries are appended to the file the save replaced",
     "Lanes/Durable/IO/Journal.lean",
     "    replace path bytes\n    handle.set (← IO.FS.Handle.mk path .append)",
     "    replace path bytes"),
    ("node: a parcel that arrives is not handed to the shard, in three processes",
     "Lanes/Net/IO/Node.lean",
     "  ready.resolve fun parcel => discard <| server.tryInput (.inr parcel)",
     "  ready.resolve fun _ => pure ()", "raftProcs"),
    ("peers: a connection that cannot be made is not reported, between three raft nodes",
     "Lanes/Net/IO/Peers.lean",
     """              listen events conn socket fun _ => pure ()
            catch _ => discard <| post events (.broken conn (← IO.monoMsNow))
""",
     """              listen events conn socket fun _ => pure ()
            catch _ => pure ()
""", "raftLive"),
    ("courier: the parcel that makes it dial waits in a queue of no room",
     "Lanes/Net/Courier.lean",
     "waiting := if limits.queue = 0 then {} else Fifo.push {} bytes }",
     "waiting := Fifo.push {} bytes }"),
    ("courier: bytes on a connection it dialed close it, and it goes on writing there",
     "Lanes/Net/Courier.lean",
     "    | none => if c.dialed.contains conn then (c, []) else (c, [.close conn])",
     "    | none => (c, [.close conn])"),
    ("tls: the certificate is not verified", "native/tls.c",
     "SSL_set_verify(ssl, SSL_VERIFY_PEER, NULL);", "SSL_set_verify(ssl, 0, NULL);"),
    ("tls: the name the certificate is for is not checked", "native/tls.c",
     "                   : SSL_set1_host(ssl, name)\n                     && SSL_ctrl(",
     "                   : SSL_ctrl("),
    ("tls: the address the certificate is for is not checked", "native/tls.c",
     "int named = ip ? X509_VERIFY_PARAM_set1_ip_asc(param, name)", "int named = ip ? 1"),
    ("tls: the name is not sent (SNI)", "native/tls.c",
     """SSL_set1_host(ssl, name)
                     && SSL_ctrl(ssl, SSL_CTRL_SET_TLSEXT_HOSTNAME, TLSEXT_NAMETYPE_host_name,
                                 (void *)name);""",
     "SSL_set1_host(ssl, name);"),
    ("tls: the trust store given is not the one used", "Lanes/Web/IO/Tls.lean",
     "  | .file path => pure path", "  | .file _ => pure (systemFiles.headD \"\")"),
    ("https client: the call is made in the clear", "Lanes/Web/IO/Client.lean",
     "        converseTls socket address request (← Tls.Session.start config.trust call.host) config",
     "        converse socket address request config"),
    ("https client: the end of the connection is taken for the server's close_notify",
     "Lanes/Web/IO/Client.lean",
     "Response.read config.maxResponseBytes received (← session.closed) then",
     "Response.read config.maxResponseBytes received ((← session.closed) || arrived.isNone) then"),
    ("libsodium: the comparison reads only the first byte", "native/lanes.c",
     "sodium_memcmp(lean_sarray_cptr(a), lean_sarray_cptr(b), size) == 0",
     "sodium_memcmp(lean_sarray_cptr(a), lean_sarray_cptr(b), size != 0) == 0"),
    ("libsodium: sha-256 of half the message", "native/lanes.c",
     "crypto_hash_sha256(lean_sarray_cptr(out), lean_sarray_cptr(msg), lean_sarray_size(msg));",
     "crypto_hash_sha256(lean_sarray_cptr(out), lean_sarray_cptr(msg), lean_sarray_size(msg) / 2);"),
    ("libsodium: an hmac key cut to a block", "native/lanes.c",
     "crypto_auth_hmacsha256_init(&state, lean_sarray_cptr(key), lean_sarray_size(key));",
     "crypto_auth_hmacsha256_init(&state, lean_sarray_cptr(key),\n"
     "        lean_sarray_size(key) > 64 ? 64 : lean_sarray_size(key));"),
]


CHECKS = {
    "lanesTest": dict(cwd=".", build="lake build lanesTest",
                      run="./.lake/build/bin/lanesTest", limit_s=120),
    "raftProcs": dict(cwd="examples/raft-kv", build="lake build raftNode raftProcs",
                      run="./.lake/build/bin/raftProcs", limit_s=300),
    "raftLive": dict(cwd="examples/raft-kv", build="lake build raftLive",
                     run="./.lake/build/bin/raftLive", limit_s=300),
}

WORDS = {
    "failed": "killed  ", "nobuild": "killed  ", "crashed": "CRASHED ", "hung": "HUNG    ",
    "passed": "SURVIVED", "stale": "STALE   ", "missing": "MISSING ",
}
FAILING = ("passed", "hung", "stale", "missing")


def sh(cmd, cwd=".", limit_s=1800):
    """The exit code and output of `cmd`; the code is `None` if it did not end in time. The
    command has a process group of its own, and what it started and left running is killed
    with it: a test that fails early may leave the processes it spawned."""
    with tempfile.TemporaryFile(mode="w+") as out:
        proc = subprocess.Popen(cmd, shell=True, cwd=cwd, start_new_session=True,
                                stdout=out, stderr=subprocess.STDOUT)
        try:
            code = proc.wait(timeout=limit_s)
        except subprocess.TimeoutExpired:
            code = None
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        proc.wait()
        out.seek(0)
        return code, out.read()


def verdict(check):
    """How the check ends on the code as it now is, and a word about it."""
    code, out = sh(check["build"], check["cwd"])
    if code != 0:
        errors = [line.strip() for line in out.splitlines() if "error:" in line]
        return "nobuild", f"does not build ({errors[0] if errors else 'no error reported'})"
    code, out = sh(check["run"], check["cwd"], check["limit_s"])
    failed = [line[5:] for line in out.splitlines() if line.startswith("FAIL ")]
    asserted = [name for name in failed if ": threw " not in name]
    if asserted:
        more = f", and {len(failed) - 1} more" if len(failed) > 1 else ""
        hang = f"; the run then hung past {check['limit_s']} s" if code is None else ""
        return "failed", f"FAIL {asserted[0]}{more}{hang}"
    if code is None:
        return "hung", f"no test failed and the run had not ended after {check['limit_s']} s"
    if failed:
        return "crashed", f"no test failed and one threw ({failed[0]})"
    if code != 0:
        return "crashed", f"no test failed and the run ended with code {code}"
    return "passed", "every test passed"


def line(name, check, how, word):
    by = "" if check == "lanesTest" else f" [{check}]"
    return f"{WORDS[how]} {name}{by}: {word}"


def summary(counts, not_run):
    def n(how):
        return counts.get(how, 0)
    missing = f", {n('missing')} missing" if n("missing") else ""
    return (f"{n('failed')} killed by a test that fails, {n('nobuild')} do not build, "
            f"{n('hung')} only hang, {n('crashed')} only crash, {n('passed')} survived, "
            f"{n('stale')} stale{missing}; {not_run} not run")


def shard(arg):
    """`i/n` as the pair (i, n), with 1 ≤ i ≤ n."""
    i, _, n = arg.partition("/")
    try:
        i, n = int(i), int(n)
    except ValueError:
        sys.exit(f"--shard takes i/n, not {arg}")
    if not 1 <= i <= n:
        sys.exit(f"--shard {arg}: i must be from 1 to n")
    return i, n


def collect(files, entries):
    """Exits as the gate does on the verdicts in `files`, which must hold each mutant once."""
    verdicts, problems = {}, []
    for f in files:
        data = json.loads(pathlib.Path(f).read_text())
        problems += [f"BASELINE {b}" for b in data["baseline"]]
        for v in data["verdicts"]:
            if v["name"] in verdicts:
                problems.append(f"TWICE    {v['name']}: in more than one shard")
            verdicts[v["name"]] = v
    counts = {}
    for name, _, _, _, check in entries:
        v = verdicts.pop(name, None)
        how, word = (v["how"], v["word"]) if v else ("missing", "in the verdicts of no shard")
        counts[how] = counts.get(how, 0) + 1
        print(line(name, check, how, word))
    problems += [f"UNKNOWN  {name}: not a mutant of this list" for name in verdicts]
    for problem in problems:
        print(problem)
    print(summary(counts, 0))
    sys.exit(1 if problems or any(counts.get(how) for how in FAILING) else 0)


def main():
    args = sys.argv[1:]
    entries = [(m[0], m[1], m[2], m[3], m[4] if len(m) > 4 else "lanesTest") for m in MUTANTS]
    if "--collect" in args:
        collect(args[args.index("--collect") + 1:], entries)
    value = {}
    for flag in ("--shard", "--json"):
        if flag in args:
            k = args.index(flag)
            if k + 1 == len(args):
                sys.exit(f"{flag} needs a value")
            value[flag] = args.pop(k + 1)
    wanted = [a for a in args if not a.startswith("--")]
    if wanted:
        chosen = [m for m in entries if any(w in m[0] for w in wanted)]
    else:
        chosen = [m for m in entries if {"--all", "--list"} & set(args) or m[4] == "lanesTest"]
    if "--shard" in value:
        i, n = shard(value["--shard"])
        chosen = chosen[i - 1::n]
    if "--list" in args:
        for name, path, _, _, check in chosen:
            print(f"{name}\n    {path}, must fail {check}")
        print(f"{len(chosen)} mutants")
        return
    report = {"shard": value.get("--shard"), "baseline": [], "verdicts": []}

    def save():
        if "--json" in value:
            pathlib.Path(value["--json"]).write_text(json.dumps(report, indent=1) + "\n")

    if "--baseline" in args:
        for check in dict.fromkeys(m[4] for m in chosen):
            how, word = verdict(CHECKS[check])
            print(f"baseline {check}: {word}", flush=True)
            if how != "passed":
                report["baseline"].append(f"{check} on the code as it is: {word}")
                save()
                sys.exit(1)
    counts = {}
    for name, path, old, new, check in chosen:
        file = pathlib.Path(path)
        source = file.read_text()
        if source.count(old) != 1:
            how, word = "stale", f"the text to change is not in {path} exactly once"
        else:
            try:
                file.write_text(source.replace(old, new))
                how, word = verdict(CHECKS[check])
            finally:
                file.write_text(source)
        counts[how] = counts.get(how, 0) + 1
        report["verdicts"].append(dict(name=name, path=path, check=check, how=how, word=word))
        save()
        print(line(name, check, how, word), flush=True)
    save()
    sh("lake build lanesTest")
    print(summary(counts, len(entries) - len(chosen)))
    sys.exit(1 if any(counts.get(how) for how in FAILING) else 0)


if __name__ == "__main__":
    main()
