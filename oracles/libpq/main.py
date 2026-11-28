"""libpq's reading of connection strings and service files, for `Tests/Oracle/Libpq.lean`.

Reads the cases `lanesOracle` writes, one JSON object per line ({"id", "op", "in": hex}), and
answers one per line ({"id", "ok", "out"}). libpq is the system's `libpq.so.5`, loaded with
ctypes, so nothing is installed.

- conninfo: the input is a connection string, a URI or `keyword=value` pairs, read with
  `PQconninfoParse`. The answer is the object of every keyword it sets and its value; an error
  is a refusal, and a value that is not UTF-8 the answer "not UTF-8".
- service: the input is {"file": a service file, "service": a name}. The file is written to a
  directory of its own, named by `PGSERVICEFILE`, with `PGSYSCONFDIR` an empty directory and no
  other `PG` variable, and `PQconnectStartParams` is given `service` alone: libpq reads the file
  as it does to connect. A failure that names the service file is a refusal; otherwise the
  answer is the object of the keywords the cases use (`KEYS`) that the connection holds, but
  `options` when it is empty, its default. libpq takes an empty name as none, so the cases name
  a service. The
  cases name no host but `localhost` and `127.0.0.1`, so the connection libpq starts goes
  nowhere else, and it is ended at once.
"""

import ctypes
import json
import os
import sys
import tempfile


class Option(ctypes.Structure):  # pylint: disable=too-few-public-methods
    _fields_ = [("keyword", ctypes.c_char_p), ("envvar", ctypes.c_char_p),
                ("compiled", ctypes.c_char_p), ("val", ctypes.c_char_p),
                ("label", ctypes.c_char_p), ("dispchar", ctypes.c_char_p),
                ("dispsize", ctypes.c_int)]


LIB = ctypes.CDLL("libpq.so.5")
LIB.PQconninfoParse.restype = ctypes.POINTER(Option)
LIB.PQconninfoParse.argtypes = [ctypes.c_char_p, ctypes.POINTER(ctypes.c_char_p)]
LIB.PQconninfo.restype = ctypes.POINTER(Option)
LIB.PQconninfo.argtypes = [ctypes.c_void_p]
LIB.PQconninfoFree.argtypes = [ctypes.POINTER(Option)]
LIB.PQfreemem.argtypes = [ctypes.c_void_p]
LIB.PQconnectStartParams.restype = ctypes.c_void_p
LIB.PQconnectStartParams.argtypes = [ctypes.POINTER(ctypes.c_char_p),
                                     ctypes.POINTER(ctypes.c_char_p), ctypes.c_int]
LIB.PQerrorMessage.restype = ctypes.c_char_p
LIB.PQerrorMessage.argtypes = [ctypes.c_void_p]
LIB.PQfinish.argtypes = [ctypes.c_void_p]

KEYS = ["host", "application_name", "fallback_application_name", "options", "password"]


def options(opts, keys=None):
    out = {}
    i = 0
    while opts[i].keyword:
        k = opts[i].keyword.decode()
        if opts[i].val is not None and (keys is None or k in keys):
            out[k] = opts[i].val.decode("utf-8")
        i += 1
    return out


def conninfo(text):
    err = ctypes.c_char_p()
    opts = LIB.PQconninfoParse(text.encode("utf-8"), ctypes.byref(err))
    if not opts:
        if err:
            LIB.PQfreemem(err)
        return None
    try:
        return options(opts)
    finally:
        LIB.PQconninfoFree(opts)


def service(case, scratch):
    path = os.path.join(scratch, "pg_service.conf")
    with open(path, "w", encoding="utf-8") as f:
        f.write(case["file"])
    keywords = (ctypes.c_char_p * 2)(b"service", None)
    values = (ctypes.c_char_p * 2)(case["service"].encode("utf-8"), None)
    conn = LIB.PQconnectStartParams(keywords, values, 0)
    try:
        message = (LIB.PQerrorMessage(conn) or b"").decode("utf-8", "replace")
        if "service" in message:
            return None
        opts = LIB.PQconninfo(conn)
        try:
            out = options(opts, KEYS)
            if out.get("options") == "":
                del out["options"]
            return out
        finally:
            LIB.PQconninfoFree(opts)
    finally:
        LIB.PQfinish(conn)


def main():
    scratch = tempfile.mkdtemp()
    sysconf = tempfile.mkdtemp()
    for name in list(os.environ):
        if name.startswith("PG"):
            del os.environ[name]
    os.environ["PGSERVICEFILE"] = os.path.join(scratch, "pg_service.conf")
    os.environ["PGSYSCONFDIR"] = sysconf
    os.environ["PGPASSFILE"] = os.path.join(scratch, "none")
    os.environ["HOME"] = scratch
    out = sys.stdout
    with open(sys.argv[1], encoding="utf-8") as cases:
        for line in cases:
            if not line.strip():
                continue
            c = json.loads(line)
            text = bytes.fromhex(c["in"]).decode("utf-8")
            try:
                if c["op"] == "conninfo":
                    answer = conninfo(text)
                elif c["op"] == "service":
                    answer = service(json.loads(text), scratch)
                else:
                    raise SystemExit("unknown op " + c["op"])
            except UnicodeDecodeError:
                answer = "not UTF-8"
            if answer is None:
                out.write(json.dumps({"id": c["id"], "ok": False}) + "\n")
            else:
                out.write(json.dumps({"id": c["id"], "ok": True, "out": answer}) + "\n")


main()
