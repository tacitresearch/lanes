"""Signature Version 4 as botocore signs, for `Tests/Oracle/SigV4.lean`, and CloudFront's signed
URLs as `botocore.signers.CloudFrontSigner` writes them, for `integrations/aws/Checks/CloudFront.lean`.

Reads the cases `lanesOracle` writes, one JSON object per line ({"id", "op", "in": hex}), and
answers one per line ({"id", "ok", "out"}). Ops: sign, cloudfront.

For sign, the input is a request as JSON: the service, region, time (in seconds since 1970),
credentials, method, host, the path's segments and the query's pairs unescaped, headers and the
body in hex, and whether the payload is signed. The URL is written as botocore's
serializers write one (`botocore.utils.percent_encode`, each segment and each name and value),
signed by `S3SigV4Auth` for s3 and `SigV4Auth` otherwise at the given time, and the answer is the
`Authorization` and `X-Amz-Date` it adds.

For cloudfront, the input is JSON: a key's name (one of `keys/`), the hash, the key's ID, the URL,
whether the policy is canned, the expiry and for a custom policy its resource, start and range of
addresses (a number and a prefix length). The policy is `build_policy`'s and the URL
`generate_presigned_url`'s, signed by `cryptography`: RSA with PKCS #1 v1.5, ECDSA with RFC 6979's
nonce. botocore 1.44 knows no hash but SHA-1, so `Hash-Algorithm=SHA256` is appended here, last,
as AWS's Go and JavaScript SDKs append it.
"""

import datetime
import ipaddress
import json
import os
import sys

from botocore.signers import CloudFrontSigner
from cryptography.hazmat.primitives import hashes, serialization
from cryptography.hazmat.primitives.asymmetric import ec, padding, rsa

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


def load_key(name):
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "keys", name + ".pem")
    with open(path, encoding="ascii") as f:
        pem = f.read().replace("TESTING KEY", "PRIVATE KEY")
    return serialization.load_pem_private_key(pem.encode("ascii"), password=None)


KEYS = {name: load_key(name) for name in ["rsa2048", "p256"]}


def cloudfront(case):
    key = KEYS[case["key"]]
    digest = hashes.SHA256() if case["hash"] == "sha256" else hashes.SHA1()

    def signer(message):
        if isinstance(key, rsa.RSAPrivateKey):
            return key.sign(message, padding.PKCS1v15(), digest)
        return key.sign(message, ec.ECDSA(digest, deterministic_signing=True))

    def when(seconds):
        return datetime.datetime.fromtimestamp(seconds, datetime.timezone.utc)

    cf = CloudFrontSigner(case["keyId"], signer)
    if case["canned"]:
        policy = cf.build_policy(case["url"], when(case["expires"]))
        url = cf.generate_presigned_url(case["url"], date_less_than=when(case["expires"]))
    else:
        ip = None
        if "ip" in case:
            # A /32 is sometimes given bare, for botocore to add the prefix.
            addr, bits = case["ip"]
            ip = str(ipaddress.IPv4Address(addr)) + ("" if bits == 32 and addr % 2 else f"/{bits}")
        start = when(case["start"]) if "start" in case else None
        policy = cf.build_policy(case["resource"], when(case["expires"]), start, ip)
        url = cf.generate_presigned_url(case["url"], policy=policy)
    if case["hash"] == "sha256":
        url += "&Hash-Algorithm=SHA256"
    return {"policy": policy, "url": url}


def main():
    out = sys.stdout
    with open(sys.argv[1], encoding="utf-8") as cases:
        for line in cases:
            if not line.strip():
                continue
            c = json.loads(line)
            if c["op"] not in ("sign", "cloudfront"):
                raise SystemExit("unknown op " + c["op"])
            try:
                case = json.loads(bytes.fromhex(c["in"]).decode("utf-8"))
            except ValueError:
                answer = {"id": c["id"], "ok": False}
            else:
                try:
                    run = sign if c["op"] == "sign" else cloudfront
                    answer = {"id": c["id"], "ok": True, "out": run(case)}
                except ValueError:
                    # Python 3.14's `email` refuses a header name that is not a token, or a value
                    # with a line break, so botocore cannot be given such a request at all.
                    answer = {"id": c["id"], "ok": False}
            out.write(json.dumps(answer, ensure_ascii=False) + "\n")


main()
