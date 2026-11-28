"""CBOR as cbor2 reads and writes it, for `Tests/Oracle/Cbor.lean`.

Reads the cases `lanesOracle` writes, one JSON object per line ({"id", "op", "in": hex}), and
answers one per line ({"id", "ok", "out"}). The input is read as one item by `CBORDecoder`, with
every tag kept as a `CBORTag` (cbor2 gives some tags a meaning, which the overrides below take
away), a map with a key twice refused, and bytes after the item refused. Ops:

- decode: the answer is the value, described as `describe` writes it;
- canonical: the answer is the value written by `dumps(canonical=True)`, in hex.

Anything cbor2 raises is a refusal.
"""

import io
import json
import struct
import sys

import cbor2

# The tags cbor2 6.3 gives a meaning to, found by decoding every tag up to 70000.
SEMANTIC = [0, 1, 2, 3, 4, 5, 25, 28, 29, 30, 35, 36, 37, 52, 54, 100, 256, 258, 260, 261, 1004,
            43000, 55799]


def keep(tag):
    return lambda value, immutable: cbor2.CBORTag(tag, value)


DECODERS = {tag: keep(tag) for tag in SEMANTIC}


def read(data):
    fp = io.BytesIO(data)
    value = cbor2.CBORDecoder(fp, semantic_decoders=DECODERS, allow_duplicate_keys=False,
                              max_depth=10000).decode()
    if fp.read():
        raise ValueError("bytes after the item")
    return value


def describe(v):
    """The value as JSON: ["u", n] and ["n", n] for n and -1 - n, ["f", bits in hex], ["t", text],
    ["h", hex], ["a", items], ["m", [key, value] pairs], ["tag", n, item], ["s", n], ["b", b],
    ["null"], ["undefined"]. Numbers are strings, which JSON keeps exactly."""
    if isinstance(v, bool):
        return ["b", v]
    if isinstance(v, int):
        return ["u", str(v)] if v >= 0 else ["n", str(-1 - v)]
    if isinstance(v, float):
        return ["f", struct.pack(">d", v).hex()]
    if isinstance(v, str):
        return ["t", v]
    if isinstance(v, (bytes, bytearray)):
        return ["h", bytes(v).hex()]
    if isinstance(v, (list, tuple)):
        return ["a", [describe(x) for x in v]]
    if isinstance(v, (dict, cbor2.frozendict)):
        return ["m", [[describe(k), describe(x)] for k, x in v.items()]]
    if isinstance(v, cbor2.CBORTag):
        return ["tag", str(v.tag), describe(v.value)]
    if isinstance(v, cbor2.CBORSimpleValue):
        return ["s", v.value]
    if v is None:
        return ["null"]
    if v is cbor2.undefined:
        return ["undefined"]
    raise ValueError("no description for " + repr(v))


def answer(op, data):
    value = read(data)
    if op == "decode":
        return describe(value)
    if op == "canonical":
        return cbor2.dumps(value, canonical=True).hex()
    raise SystemExit("unknown op " + op)


def main():
    out = sys.stdout
    with open(sys.argv[1], encoding="utf-8") as cases:
        for line in cases:
            if not line.strip():
                continue
            c = json.loads(line)
            try:
                result = {"id": c["id"], "ok": True, "out": answer(c["op"], bytes.fromhex(c["in"]))}
            except SystemExit:
                raise
            except Exception:  # pylint: disable=broad-except
                result = {"id": c["id"], "ok": False}
            out.write(json.dumps(result) + "\n")


main()
