#!/usr/bin/env python3
"""Mutation gate for trusted code.

Each mutant below breaks one duty of a file listed in TRUSTED.md. A check must fail on every
one of them: a mutant that passes is a claim nothing checks. The check is `lanesTest` unless
the entry names another as its fifth part (see `CHECKS`). Run from the repository root; it
takes a minute or two per mutant, so it is run by hand and nightly, not on every push.

    python3 scripts/mutants.py            # those checked by lanesTest
    python3 scripts/mutants.py --all      # also those checked by something slower
    python3 scripts/mutants.py tls        # those whose name contains "tls"
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
import re
import signal
import subprocess
import sys
import tempfile

MUTANTS = [
    ("runtime: what booting puts out is not handed over", "Lanes/Runtime/IO/Shell.lean",
     "  handOver outputs\n  rt.recovered.set true", "  rt.recovered.set true"),
    ("runtime: commands left in the inbox when the shard ends", "Lanes/Runtime/IO/Shell.lean",
     "  discard <| rt.inbox.modifyGet Mailbox.take\n", ""),
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
    ("runtime: the shard sleeps past its next timer", "Lanes/Runtime/IO/Shell.lean",
     "    | .for_ms ms => rt.parker.parkAtMost ms", "    | .for_ms ms => rt.parker.parkAtMost (ms + 3000)"),
    ("runtime: an inbox of no capacity takes nothing", "Lanes/Runtime/IO/Shell.lean",
     "  max 1 rt.config.inboxCapacity", "  rt.config.inboxCapacity"),
    ("http: a shard that ends on an error is not noticed", "Lanes/Web/IO/Server.lean",
     "    if (← runtime.ended).isSome then", "    if false then"),
    ("http: the runtime is left running when the port is taken", "Lanes/Web/IO/Server.lean",
     "      runtime.stop\n      throw e", "      throw e"),
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
    ("http client: the Host header leaves out a port that is not the scheme's",
     "Lanes/Web/IO/Client.lean",
     "  else call.host ++ \":\" ++ toString call.port", "  else call.host"),
    ("http client: the answer to a HEAD is read as if it had a body", "Lanes/Web/IO/Client.lean",
     "if call.headOnly then Response.readHead", "if false then Response.readHead"),
    ("s3: the answer is taken from another operation", "Lanes/Web/IO/S3.lean",
     "(← Client.exchange call config).map (interpret op)",
     "(← Client.exchange call config).map (interpret .list)"),
    ("s3: a call is given no deadline of its own", "Lanes/Web/IO/S3.lean",
     "{ config with timeout_ms := call.deadline_ms }", "{ config with timeout_ms := 1 }"),
    ("tls: the certificate is not verified", "native/tls.c",
     "SSL_set_verify(ssl, SSL_VERIFY_PEER, NULL);", "SSL_set_verify(ssl, 0, NULL);"),
    ("tls: the name the certificate is for is not checked", "native/tls.c",
     "                   : (!check || SSL_set1_host(ssl, name))\n                     && SSL_ctrl(",
     "                   : SSL_ctrl("),
    ("tls: the address the certificate is for is not checked", "native/tls.c",
     "int named = ip ? !check || X509_VERIFY_PARAM_set1_ip_asc(param, name)", "int named = ip ? 1"),
    ("tls: the name is not sent (SNI)", "native/tls.c",
     """(!check || SSL_set1_host(ssl, name))
                     && SSL_ctrl(ssl, SSL_CTRL_SET_TLSEXT_HOSTNAME, TLSEXT_NAMETYPE_host_name,
                                 (void *)name);""",
     "(!check || SSL_set1_host(ssl, name));"),
    ("tls: no ALPN protocol is offered", "native/tls.c",
     "    if (named && protos != 0)\n", "    if (0)\n"),
    ("tls: the server's certificate is not given", "native/tls.c",
     "    if (size > 0 && i2d_X509(cert, &out) == size) lean_to_sarray(bytes)->m_size = (size_t)size;",
     "    if (size > 0 && i2d_X509(cert, &out) == size) lean_to_sarray(bytes)->m_size = 0;"),
    ("postgres client: verifyFull checks the chain only", "Lanes/Lib/Postgres/IO/Client.lean",
     "    | .verifyFull => Tls.Session.start cfg.trust name [\"postgresql\"]",
     "    | .verifyFull => Tls.Session.startChain cfg.trust name [\"postgresql\"]"),
    ("postgres client: after the handshake, bytes are sent in the clear",
     "Lanes/Lib/Postgres/IO/Client.lean",
     "  | some t => t.write bytes; s.flush t", "  | some _ => s.socket.send bytes"),
    ("tls: the trust store given is not the one used", "Lanes/Web/IO/Tls.lean",
     "  | .file path => pure path", "  | .file _ => pure (systemFiles.headD \"\")"),
    ("https client: the call is made in the clear", "Lanes/Web/IO/Client.lean",
     "        converseTls socket address request (← Tls.Session.start config.trust call.host) read",
     "        converse socket address request read"),
    ("https client: the end of the connection is taken for the server's close_notify",
     "Lanes/Web/IO/Client.lean",
     "read received (← session.closed) then",
     "read received ((← session.closed) || arrived.isNone) then"),
    ("signature: every signature checks", "native/verify.c",
     "        ok = ctx && EVP_DigestVerifyInit(", "        ok = 1 || EVP_DigestVerifyInit("),
    ("signature: an ECDSA signature is handed over as JWS writes it, not as DER",
     "Lanes/Lib/Crypto/PublicKey.lean",
     "    if sig.size == 64 then\n      some ⟨",
     "    if sig.size == 64 then some sig else if false then\n      some ⟨"),
    ("jose: a key checks a signature of the other algorithm", "Lanes/Web/Auth/Jose.lean",
     "    | .es256, .p256 .. => true\n    | _, _ => false", "    | .es256, .p256 .. => true\n    | _, _ => true"),
    ("jose: the kid a token names is ignored", "Lanes/Web/Auth/Jose.lean",
     "keys.filter fun k => k.fits c.alg && (c.kid.isNone || k.kid == c.kid)",
     "keys.filter fun k => k.fits c.alg"),
    ("id token: the audience is not checked", "Lanes/Web/Auth/IdToken.lean",
     "  else if x.clientId ∉ c.aud then .error .audience", "  else if false then .error .audience"),
    ("id token: the expiry is not checked", "Lanes/Web/Auth/IdToken.lean",
     "  else if c.exp + x.skew_s ≤ x.now_s then .error .expired",
     "  else if false then .error .expired"),
    ("id token: the nonce is not checked", "Lanes/Web/Auth/IdToken.lean",
     "  else if c.nonce != some x.nonce then .error .nonce", "  else if false then .error .nonce"),
    ("oauth: a state is accepted from another browser", "Lanes/Web/Auth/OAuth.lean",
     "    if !same t.state state then .error .otherBrowser",
     "    if false then .error .otherBrowser"),
    ("oauth: a ticket is read without its tag", "Lanes/Web/Auth/OAuth.lean",
     "  (Auth.verify key \"sign-in\" cookie).bind read",
     "  read (\".\".intercalate ((cookie.splitOn \".\").drop 1))"),
    ("oauth: a state accepted is not used up", "Lanes/Web/Auth/OAuth.lean",
     "    else (⟨raised, (t.state, t.expires_ms) :: kept⟩, .ok ())",
     "    else (⟨raised, kept⟩, .ok ())"),
    ("oauth: a full set drops states without raising the floor", "Lanes/Web/Auth/OAuth.lean",
     "    let raised := (live.drop (limit - 1)).foldr (fun e m => max e.2 m) floor",
     "    let raised := floor"),
    ("oauth: a sign-in that has expired is accepted", "Lanes/Web/Auth/OAuth.lean",
     "    else if t.expires_ms ≤ now_ms then .error .expired",
     "    else if false then .error .expired"),
    ("oauth: a JWK Set is fetched for every unknown kid", "Lanes/Web/Auth/OAuth.lean",
     "    else if t + settings.minRefresh_ms ≤ now_ms then .fetch", "    else if true then .fetch"),
    ("oauth: the code enters the system", "Lanes/Web/Auth/OAuth.lean",
     "  { r with query := [], headers := r.headers ++", "  { r with headers := r.headers ++"),
    ("sign-in: identity headers a client sends are let in", "Lanes/Web/IO/SignIn.lean",
     "  let r := strip r\n", "  let r := r\n"),
    ("sign-in: the state of a sign-in done is not claimed", "Lanes/Web/IO/SignIn.lean",
     "          let (u, claimed) := u.claim limit later t\n          (claimed, u)",
     "          let (_, claimed) := u.claim limit later t\n          (claimed, u)"),
    ("server: the work a request needs before it enters is not done", "Lanes/Web/IO/Server.lean",
     "        | .ok (.ok request) => discard <| hand request answer",
     "        | .ok (.ok _) => discard <| hand request answer"),
    ("crypto: the comparison reads only the first byte", "native/lanes.c",
     "CRYPTO_memcmp(lean_sarray_cptr(a), lean_sarray_cptr(b), size) == 0",
     "CRYPTO_memcmp(lean_sarray_cptr(a), lean_sarray_cptr(b), size != 0) == 0"),
    ("crypto: sha-256 of half the message", "native/lanes.c",
     "SHA256(lean_sarray_cptr(msg), lean_sarray_size(msg), lean_sarray_cptr(out))",
     "SHA256(lean_sarray_cptr(msg), lean_sarray_size(msg) / 2, lean_sarray_cptr(out))"),
    ("crypto: an hmac key cut to a block", "native/lanes.c",
     "lean_sarray_cptr(key), (int)size,",
     "lean_sarray_cptr(key), (int)(size > 64 ? 64 : size),"),
    ("crypto: argon2id in one lane whatever is asked", "native/lanes.c",
     'OSSL_PARAM_BLD_push_uint32(bld, "lanes", lanes)',
     'OSSL_PARAM_BLD_push_uint32(bld, "lanes", 1)'),
]


CHECKS = {
    "lanesTest": dict(cwd=".", build="lake build lanesTest",
                      run="./.lake/build/bin/lanesTest", limit_s=120),
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
    # `FAIL (test) name`, as `Testing.report` prints it, or `FAIL name`.
    failed = [re.sub(r"^\(\w+\) ", "", line[5:]) for line in out.splitlines()
              if line.startswith("FAIL ")]
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
