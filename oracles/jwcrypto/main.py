"""JWS in compact form as jwcrypto verifies it, for `Tests/Oracle/Jose.lean`.

Reads the cases `lanesOracle` writes, one JSON object per line ({"id", "op", "in": hex}), and
answers one per line ({"id", "ok", "out"}). Op: verify. The input is {"keys": a JWK Set as text,
"token": a token}; the set is read with `JWKSet.from_json`, the token with `JWS.deserialize` and
checked with `JWS.verify` against the set, with the algorithms allowed RS256 and ES256 alone, as
Lanes allows. Accepted, the answer is the payload, in hex; anything jwcrypto raises is a refusal.
"""

import json
import sys

from jwcrypto.jwk import JWKSet
from jwcrypto.jws import JWS


def verify(case):
    keys = JWKSet.from_json(case["keys"])
    token = JWS()
    token.allowed_algs = ["RS256", "ES256"]
    token.deserialize(case["token"])
    token.verify(keys)
    return {"payload": token.payload.hex()}


def main():
    out = sys.stdout
    with open(sys.argv[1], encoding="utf-8") as cases:
        for line in cases:
            if not line.strip():
                continue
            c = json.loads(line)
            if c["op"] != "verify":
                raise SystemExit("unknown op " + c["op"])
            try:
                answer = {"id": c["id"], "ok": True,
                          "out": verify(json.loads(bytes.fromhex(c["in"]).decode("utf-8")))}
            except Exception:  # pylint: disable=broad-except
                answer = {"id": c["id"], "ok": False}
            out.write(json.dumps(answer) + "\n")


main()
