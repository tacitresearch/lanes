# D?. S3 and Signature Version 4, in Lanes as the protocol of a class of object stores

The first application Lanes is for, a video site on AWS, keeps its videos and thumbnails in S3.
Browsers upload and download them directly, with presigned links, and the server makes ordinary
calls: put, get, head, delete and list. This adds what that needs: requests signed with AWS's
Signature Version 4 (`Lanes/Web/Http/SigV4.lean`, proved in `Lanes/Web/Http/SigV4Sound.lean`),
an S3 client on the HTTP client (`Lanes/Web/S3/Basic.lean`, `Lanes/Web/S3/Xml.lean`, its IO in
`Lanes/Web/IO/S3.lean`), and a model of an object store (`Lanes/Outside/ObjectStore.lean`). It
departs from D61 in one place, said below.

## In `Lanes/`, not in `integrations/`

D61 puts a vendor in a package under `integrations/` and keeps vendors' names out of `Lanes/`.
S3 and Signature Version 4 go in `Lanes/` all the same, for the owner to confirm:

- **They are a protocol, not one vendor's API.** The S3 API is what object stores speak: MinIO,
  Ceph's gateway, Cloudflare R2, Backblaze B2, Wasabi, LocalStack and Google Cloud Storage's
  interoperability mode answer it, each signed with Signature Version 4. AWS's own services sign
  with it too (SES, which the site will need for mail). A store is chosen by its `Endpoint`, so
  the code is the class's, as HTTP is. D61's class is "an object store"; S3 is how a system
  talks to one.
- **What D61 keeps out stays out.** An integration is where a vendor's releases, regions,
  quirks and test mode are. There is no table of regions or endpoints here, no IAM, no STS, no
  SDK and nothing that follows AWS's releases: the signing algorithm has not changed since 2012,
  and S3's operations used here are its oldest. The one name of AWS's is `Endpoint.aws`, the
  form of its endpoints, which a user could write. The parts that are AWS's alone are left for
  `integrations/`: credentials from an instance's metadata (below), and a test against AWS
  itself.
- **The pure parts are proved, as the rest of `Lanes/` is.** Signing is a function of the
  request with theorems; in a package outside it would be the one part of the site's stack
  without an axiom gate and the inventory.
- `integrations/` does not exist yet: no Lake package, no CI job. The first one should be a
  vendor that is only a vendor.

The names in the code say S3, because that is the protocol's name and what a reader will look
for; the model is named for its class, `ObjectStore`. If the owner prefers D61 as written, the
three S3 files move to a package with no change to them, and `SigV4` can stay.

## What is signed is what is sent

`SigV4.sign` signs the request the client sends, after putting its query in the canonical order,
and the target the client writes for it is the canonical path and query that were signed
(`SigV4.target_sign`): the path's segments escaped once, as S3 wants, and the parameters sorted
by escaped name and then value (`SigV4.sortQuery_sorted`, `SigV4.sortQuery_perm`). An escape is
letters, digits, `-._~` and `%XX` in capitals and nothing else (`SigV4.encode_chunks`), and an
S3 key, slashes and all, reads back from its escape (`SigV4.decodePath_canonicalPath`). The
headers signed are `host` and every header of the request the client writes, so a header the
writer drops (one that frames the message) is never signed; their names are in lowercase,
strictly in order and one for each name given (`SigV4.canonicalHeaders_sorted`,
`canonicalHeaders_lower`, `mem_canonicalHeaders`), and the list in `SignedHeaders` is those
names by definition. Services other than S3 escape the path twice; for a segment that needs no
escaping, which is every path the site uses, the two agree.

To make `Host` what is signed and what a browser sends, the client now writes the port in it
when it is not the scheme's (`Client.Call.authority`), as RFC 9110 says; a link presigned for
MinIO on port 9000 names `localhost:9000`, as the browser will. The client also sends `HEAD`
(`Call.headOnly`, `Request.wireHead`), whose answer it reads without a body
(`Response.readHead`), since a head's `Content-Length` is the object's.

A body is signed by its SHA-256 or sent as `UNSIGNED-PAYLOAD` (`S3.Payload`), which S3 accepts
over HTTPS. A session token is sent and signed as `X-Amz-Security-Token`. A presigned link is
good for at most seven days, as AWS allows, by its type (`SigV4.Expiry`), signs `host` and, for
a put, the content type the browser must send, and never the body.

A secret is a `SigV4.Secret`, which prints as `<secret>`, so credentials can derive `Repr`
safely and a key never reaches a log by `toString`. Reading it is `Secret.reveal`, which the
signer and the token header do and nothing else.

## Bodies are whole, at one seam

Another branch adds streamed bodies to the server and the client. Until then a body is whole and
in memory: `Op.put` carries one and `Answer.object` returns one, within the client's
`maxResponseBytes`. That is enough for the server's part, thumbnails and small objects; videos go
between the browser and S3 by presigned links and never through the server. When bodies stream,
`Op.put`, `Answer.object` and the exchange in `Lanes/Web/IO/S3.lean` change, and nothing else:
signing needs no body under `UNSIGNED-PAYLOAD`, and a signed stream
(`STREAMING-AWS4-HMAC-SHA256-PAYLOAD`) would be a new `Payload`.

## A reader of the XML S3 writes

ListObjectsV2 and S3's errors answer in XML, and Lanes has no XML library. `Lanes/Web/S3/Xml.lean`
reads the part of XML 1.0 those answers use into a tree: elements, whose attributes it skips,
text with the five named entities and character references, the declaration, comments and
processing instructions. It refuses a document type, so no entity is defined or expanded and
nothing is fetched; `CDATA`; any other entity; an element nested deeper than 16; an end tag that
does not match; and anything after the root. It is total, and what it reads is bounded by the
client's limit on a response. Keys are asked for escaped (`encoding-type=url`), so a key XML 1.0
cannot carry still lists.

It is tested, not proved, on S3's documented answers, on what it must refuse, and on every cut
of a page. D50 asks that a parser also be tested against Go's; this one is not yet (below).

## A model of an object store

`ObjectStore.server` is D61's object store, as an `Rpc.Server` (D65): puts, gets and deletes by
key, each answered at most once, with an answer the model allows, or `unknown`. A read sees the
last write answered, which is S3's promise since December 2020, unless a write may have taken
effect after it: one that timed out or was refused (an error may come after the write took
effect) may take effect at any moment, or never; and one answered while another write to the key
was open may have been the later. So a key may hold any of several objects, and what a get may
answer is one of them.

Proved: a get is answered only with an object a put sent under that key, in every run the model
allows (`ObjectStore.read_sent`). Tested: that a get after a write answered sees it, that a write
that timed out may show or not, that overlapping writes leave either, and that a delete leaves
nothing (`Tests/S3.lean`); and a system calling the fake S3 below through `S3.handler`, whose run
the model allows. Not modelled: listings, ranges, conditional writes, versions, and how long a
write takes. `S3.Op.modelled` and `S3.Answer.modelled` say which operations are the model's.

## Checked

`Tests/SigV4.lean` checks the canonical request and the `Authorization` header of 19 cases of
AWS's Signature Version 4 test suite, as botocore keeps it (`tests/unit/auth/aws4_testsuite`),
fetched for this work: `get-vanilla` and its queries (empty value, order by key, by case and by
value, unreserved characters, UTF-8), duplicate and ordered and trimmed header values,
`get-unreserved`, `get-utf8`, `post-vanilla` and its query, a header's name sorted and its
value's case kept, the two form bodies, and `post-sts-header-before` with a session token; and the string to
sign of `get-vanilla`. Left out: the cases that normalize a path (`get-slash`, `get-relative`,
`normalize-path`), which S3 does not do, and `get-header-value-multiline`, a folded header the
client cannot send. The suite's secret is `wJalrXUtnFEMI/K7MDENG+bPxRfiCYEXAMPLEKEY`, with a `+`
where the S3 examples have a `/`.

The S3 cases are the documentation's examples with its key `AKIAIOSFODNN7EXAMPLE` on 24 May
2013: GET object with a range, PUT object with a `$` in the key, a `Date` header and a storage
class, GET of a bucket's lifecycle and GET bucket with two parameters, and the presigned GET for
a day. The documentation could not be reached from here, so these were written from memory.
botocore 1.44, an independent implementation, computes the same signatures for the GET object,
lifecycle, list and presigned examples. It does not sign the PUT example as documented (it drops
`x-amz-date` when a `Date` header is given), so the PUT signature
(`98ad7217…`) and the GET example's string-to-sign hash (`7344ae5b…`) are confirmed only in that
the code computes exactly the values remembered, which a misremembered hash would not match.

`Tests/S3.lean` runs the client against a fake S3 written in the test, over plain HTTP. It reads
each request off the wire, rebuilds the canonical request from the bytes it received, checks the
signature with the same key, the payload's hash and the session token, and keeps the objects.
Every operation, a range and the last bytes, a head, a listing by pages and by a delimiter, a body
sent unsigned, a presigned put and get followed as a browser would, and the refusals of a wrong
secret, a missing token, a link changed and a put whose content type is not the one signed. No
call reaches AWS.

## Not done

- **Credentials from an instance's metadata** (IMDSv2, on EC2 and ECS). They expire within hours
  and must be fetched again before they do, which wants an actor with a deadline, not a
  function; and the endpoints are AWS's alone. They belong to an AWS integration. Credentials come
  from `AWS_ACCESS_KEY_ID`, `AWS_SECRET_ACCESS_KEY` and `AWS_SESSION_TOKEN`
  (`S3.credentialsFromEnv`), or are given.
- **The XML reader against Go's** `encoding/xml`, as D50 asks of a parser: Go accepts more (a
  document type, `CDATA`, namespaces), and each difference has to be decided.
- **S3 over TLS in a test.** `Tests/Tls.lean`'s `openssl s_server` serves files, not S3, so the
  fake runs over plain HTTP; HTTPS is the client's, tested on its own (D67). Nor is
  virtual-hosted addressing run against the fake, which would need a name for the bucket that
  resolves locally; the call it builds is tested.
- **Against a real store.** A run recorded against MinIO or LocalStack, and checked with
  `Outside.allows` against the model, is the test D61 asks of an integration.
- Multipart uploads, streamed and chunked signing, conditional writes, and retrying when the
  clock is more than fifteen minutes from S3's.
