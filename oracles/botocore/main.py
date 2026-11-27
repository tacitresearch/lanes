"""Signature Version 4 as botocore signs, for `Tests/Oracle/SigV4.lean`.

Reads the cases `lanesOracle` writes, one JSON object per line ({"id", "op", "in": hex}), and
answers one per line ({"id", "ok", "out"}). Op: sign. The input is a request as JSON: the service,
region, time (in seconds since 1970), credentials, method, host, the path's segments and the query's pairs unescaped,
headers and the body in hex, and whether the payload is signed. The URL is written as botocore's
serializers write one (`botocore.utils.percent_encode`, each segment and each name and value),
signed by `S3SigV4Auth` for s3 and `SigV4Auth` otherwise at the given time, and the answer is the
`Authorization` and `X-Amz-Date` it adds.
"""

import datetime
import json
import sys

import botocore.auth
from botocore.awsrequest import AWSRequest
from botocore.config import Config
from botocore.credentials import Credentials
from botocore.utils import percent_encode


def sign(case):
    when = datetime.datetime.fromtimestamp(case["unix"], datetime.timezone.utc).replace(tzinfo=None)
    botocore.auth.get_current_datetime = lambda *args, **kwargs: when
    path = "/" + "/".join(percent_encode(s, safe="-._~") for s in case["path"])
    query = "&".join(
        percent_encode(k, safe="-._~") + "=" + percent_encode(v, safe="-._~")
        for k, v in case["query"]
    )
    url = "https://" + case["host"] + path + ("?" + query if query else "")
    request = AWSRequest(method=case["method"], url=url, data=bytes.fromhex(case["body"]))
    for name, value in case["headers"]:
        request.headers[name] = value
    if not case["signed"]:
        # As a client configured with `s3={"payload_signing_enabled": False}` signs.
        request.context["client_config"] = Config(s3={"payload_signing_enabled": False})
        request.context["payload_signing_enabled"] = False
    creds = Credentials(case["key"], case["secret"], case.get("token"))
    signer = botocore.auth.S3SigV4Auth if case["service"] == "s3" else botocore.auth.SigV4Auth
    signer(creds, case["service"], case["region"]).add_auth(request)
    return {"authorization": request.headers["Authorization"],
            "x-amz-date": request.headers["X-Amz-Date"]}


def main():
    out = sys.stdout
    with open(sys.argv[1], encoding="utf-8") as cases:
        for line in cases:
            if not line.strip():
                continue
            c = json.loads(line)
            if c["op"] != "sign":
                raise SystemExit("unknown op " + c["op"])
            try:
                case = json.loads(bytes.fromhex(c["in"]).decode("utf-8"))
            except ValueError:
                answer = {"id": c["id"], "ok": False}
            else:
                answer = {"id": c["id"], "ok": True, "out": sign(case)}
            out.write(json.dumps(answer, ensure_ascii=False) + "\n")


main()
