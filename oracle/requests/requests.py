#!/usr/bin/env python3
"""The request reader's differential test.

Reads the corpus Tests/ReadRequest.corpus, whose verdicts are those of Lanes' Request.read
(`lake test` checks them), and puts each case to other HTTP/1.1 servers: Go's net/http, Node's
http (llhttp) and Python's h11, each with the limits of Request.Limits. Every disagreement is
printed with its kind:

  stricter   Lanes refuses, or waits for more, where the other reads a request
  waits      Lanes waits for more where the other refuses
  status     both refuse, with different statuses
  LOOSER     Lanes reads a request the other refuses or waits on: a bug unless decided
  FRAMING    both read a request, but not the same one: a bug unless decided

Usage: oracle/requests/requests.py [--go PATH] [--node PATH] [--only NAME]
Exits 1 if a disagreement is LOOSER or FRAMING.
"""

import argparse
import os
import re
import socket
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
CORPUS = os.path.join(HERE, "..", "..", "Tests", "ReadRequest.corpus")


def unescape(text):
    text = re.sub(r"\\\*(\d+)\(([^)]*)\)", lambda m: m.group(2) * int(m.group(1)), text)
    out = bytearray()
    i = 0
    while i < len(text):
        c = text[i]
        if c != "\\":
            out += c.encode()
            i += 1
            continue
        e = text[i + 1]
        if e == "x":
            out.append(int(text[i + 2:i + 4], 16))
            i += 4
        else:
            out.append({"r": 13, "n": 10, "t": 9, "\\": 92}[e])
            i += 2
    return bytes(out)


def corpus():
    cases = []
    with open(CORPUS, encoding="utf-8") as f:
        for line in f.read().split("\n"):
            if not line or line.startswith("#"):
                continue
            parts = line.split("\t") + [""]
            cases.append((parts[0], parts[1].split(), unescape(parts[2])))
    return cases


def responses(data):
    """The verdicts in what a server sent back: X-Verdict of a 200, `more` for 599, or the
    status."""
    verdicts = []
    while data:
        end = data.find(b"\r\n\r\n")
        if end < 0:
            break
        lines = data[:end].decode("latin-1").split("\r\n")
        if not lines[0].startswith("HTTP/"):
            verdicts.append("garbage:" + repr(data[:40]))
            break
        status = int(lines[0].split(" ")[1])
        headers = {}
        for line in lines[1:]:
            name, _, value = line.partition(":")
            headers[name.strip().lower()] = value.strip()
        data = data[end + 4:]
        if "content-length" in headers:
            data = data[int(headers["content-length"]):]
        elif status >= 300:
            data = b""
        if 100 <= status < 200:
            continue
        if "x-read" in headers:
            verdicts = headers["x-read"].split() + [str(status)]
        elif status == 200:
            verdicts.append(headers.get("x-verdict", "ok"))
        elif status == 599:
            verdicts.append("more")
        else:
            verdicts.append(str(status))
    return verdicts


def over_socket(port, wire):
    s = socket.create_connection(("127.0.0.1", port))
    s.settimeout(3)
    s.sendall(wire)
    s.shutdown(socket.SHUT_WR)
    data = b""
    try:
        while True:
            chunk = s.recv(65536)
            if not chunk:
                break
            data += chunk
    except (socket.timeout, ConnectionResetError):
        pass
    s.close()
    return responses(data)


def h11_verdicts(wire):
    import h11

    conn = h11.Connection(h11.SERVER, max_incomplete_event_size=16384)
    conn.receive_data(wire)
    out = []
    method, size = "", 0
    while True:
        try:
            event = conn.next_event()
        except h11.RemoteProtocolError as e:
            out.append(str(e.error_status_hint))
            return out
        if event is h11.NEED_DATA:
            return out
        if isinstance(event, h11.Request):
            method, size = event.method.decode(), 0
        elif isinstance(event, h11.Data):
            size += len(event.data)
        elif isinstance(event, h11.EndOfMessage):
            out.append(f"ok:{method}:{size}")
            try:
                conn.send(h11.Response(status_code=200, headers=[("Content-Length", "0")]))
                conn.send(h11.EndOfMessage())
                conn.start_next_cycle()
            except h11.LocalProtocolError:
                return out
        else:
            return out


def start(command):
    process = subprocess.Popen(command, stdout=subprocess.PIPE, text=True)
    port = int(process.stdout.readline())
    return process, port


def strip_more(verdicts):
    return [v for v in verdicts if v != "more"]


# Disagreements that come from how a server is driven here, not from its parser, each checked by
# hand.
ARTIFACTS = {
    ("a field that only looks like transfer-encoding", "node"):
        "node drops the answer to the first request when its parser fails on the next one in the "
        "same packet; sent apart, node reads the first as Lanes does and refuses the rest",
}


def kind(lanes, other):
    for i in range(max(len(lanes), len(other))):
        a = lanes[i] if i < len(lanes) else None
        b = other[i] if i < len(other) else None
        if a == b:
            continue
        a_ok = a is not None and a.startswith("ok")
        b_ok = b is not None and b.startswith("ok")
        if a_ok and b_ok:
            return "FRAMING"
        if a_ok:
            return "LOOSER"
        if b_ok:
            return "stricter"
        if a is None:
            return "waits"
        if b is None:
            return "stricter"
        return "status"
    return None


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--go", default="/usr/local/go/bin/go")
    parser.add_argument("--node", default="node")
    parser.add_argument("--only")
    args = parser.parse_args()
    env = dict(os.environ, GOFLAGS="-mod=mod", GOCACHE=os.environ.get("GOCACHE", "/tmp/go-cache"))
    servers = {}
    others = []
    try:
        go = subprocess.Popen([args.go, "build", "-o", "/tmp/lanes-requests-go", "./requests"],
                              cwd=os.path.join(HERE, ".."), env=env)
        if go.wait() == 0:
            servers["go"] = start(["/tmp/lanes-requests-go"])
        servers["node"] = start([args.node, os.path.join(HERE, "server.js")])
        bad = 0
        counts = {}
        for name, lanes, wire in corpus():
            if args.only and args.only != name:
                continue
            verdicts = {name: over_socket(port, wire) for name, (_, port) in servers.items()}
            verdicts["h11"] = h11_verdicts(wire)
            for parser_name, verdict in verdicts.items():
                k = kind(strip_more(lanes), strip_more(verdict))
                if k is None:
                    continue
                if (name, parser_name) in ARTIFACTS:
                    k = "artifact"
                counts[k] = counts.get(k, 0) + 1
                if k in ("LOOSER", "FRAMING"):
                    bad += 1
                others.append((k, name, parser_name, " ".join(lanes), " ".join(verdict)))
        width = max((len(o[1]) for o in others), default=0)
        for k, name, parser_name, lanes, verdict in others:
            print(f"{k:9} {name:{width}}  {parser_name:5} lanes: {lanes:24} {parser_name}: {verdict}")
        print(f"{len(corpus())} cases; disagreements: "
              + ", ".join(f"{k} {n}" for k, n in sorted(counts.items())))
        return 1 if bad else 0
    finally:
        for process, _ in servers.values():
            process.kill()


if __name__ == "__main__":
    sys.exit(main())
