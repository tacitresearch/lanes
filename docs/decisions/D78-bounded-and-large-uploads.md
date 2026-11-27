# D78. Uploads bounded by a signed policy, and large ones in parts

D71 gave the browser presigned links to put and get an object. A presigned `PUT` signs the
method, the key and the headers named, never the length, so whoever holds a link may put up to
5 GB with it: the video site (`examples/videos`) handed every member a link to store as much as
S3 takes, a cost no one bounded (its README's friction log, item 4; the security review, LOW).
A single `PUT` also fails whole: an upload of a few gigabytes that breaks at 90% starts again.
This adds S3's two answers, each pure with its theorems, and a model of the second.

## A form under a policy (`Lanes/Web/S3/Post.lean`)

S3 takes a browser's `POST` of a form whose `policy` field is a JSON document in base64, signed
with the same key Signature Version 4 derives: an `expiration` and `conditions`, each a field
equal to a value, a field that starts with a prefix, or `content-length-range`. S3 refuses a file
outside the range (`EntityTooLarge`, `EntityTooSmall`), a field no condition names, a condition
unmet and a policy past its expiration. That is the bound a presigned `PUT` cannot give.

`Post.form` writes, from a `Policy`, the conditions (the range, the content type, the bucket,
the key exactly or by prefix with `${filename}`, the algorithm, the credential, the date and the
session token when there is one), the document, its base64, its signature and the fields a page
puts in a `<form>` or a `FormData`. The policy's key and expiry are typed: a `Length` is at most
5 GiB, what S3 takes in one `POST`, and the expiry is SigV4's, at most seven days.

`Post.check` is what S3 does with a form, the signature apart: it is the specification the fake
S3 runs, so the tests check the fake against the same reading the theorems are about. Proved
(`Lanes/Web/S3/PostSound.lean`, gated):

- `form_policy`: the policy a form carries decodes, as `Post.decode?` reads it (base64, UTF-8,
  `Json.parse`, the conditions), to exactly the document `Post.document` gives: the conditions in
  order and the expiration. It rests on `Base64.decode_encode` and `Json.parse_compress`, so the
  base64 and the JSON are well formed and within the reader's limits by construction.
- `expiration_parse`: the expiration reads back, as RFC 3339, as the moment `expiry` seconds
  after signing.
- `admitted_bounded`: a file `Post.check` admits under a form's policy has a size within the
  range and is posted before the expiry.

The conditions are written in botocore's order and its expiration's form (`2013-05-24T00:15:00Z`),
so its policies and Lanes' read back as the same document; the base64 differs only because
Python's `json.dumps` puts a space after each separator, and S3 signs the base64 as sent.

## Parts (`Lanes/Web/S3/Multipart.lean`)

Multipart upload is five calls, now operations of `S3.Op`: `createUpload`, `uploadPart`,
`completeUpload` (with a `Manifest`: at least one part, ascending, each with the ETag its upload
was answered, sent as S3's XML), `abortUpload` and `listParts`. A Complete may be answered `200`
with an error in its body, which `S3.interpret` reads as a refusal. `S3.presignPart` makes a link
for one part a browser puts itself; given a length, it signs `Content-Length`, so the part must
be exactly that long. With a plan of the parts, that bounds an upload by parts as the policy
bounds a form.

`Plan` cuts a body: parts of `partSize` (5 MiB to 5 GiB), the last what is left, at most 10,000,
proved (`Plan.count_le`, `Plan.range_full`, `Plan.range_next`, `Plan.range_last`); `Plan.auto`
picks the smallest size in whole MiB that fits 5 TiB in 10,000 parts.

`Flow` is the server's upload, a pure machine like D74's refresh: `next` says the call to make,
`answer` what an answer or none does. It sends the parts in order, makes each call up to
`maxAttempts` times, aborts an upload it gives up on, and treats a Complete with care: its answer
may be lost after it took effect, and S3 answers a Complete made again with the first's result
for a while and then `NoSuchUpload`. So after a lost answer the flow sends it again, and if the
upload is then gone it asks the object's `HEAD` and is done only when the store holds an object of
the body's size. `S3.upload` (`Lanes/Web/IO/S3.lean`) performs it, a bounded number of calls,
and decides nothing. Bodies are still whole in memory (D71); the flow names byte ranges, so a
streamed body changes `Flow.op` alone.

## A model of multipart uploads (`Lanes/Outside/Multipart.lean`)

The object store's model (D65, D71) has no parts. `Multipart.server` is one more `Rpc.Server`:
uploads begun under issued ids, parts sent by number, Completes by listing, aborts and reads. As
in the object store's, what is not known is kept open rather than guessed: a part sent may be held
whatever its answer, and a Complete sent may take effect whatever its answer. A Complete is
answered `completed` only for an ordered listing whose every part was sent with its tag, under an
upload that was not aborted, and with one listing an upload; a read finds nothing only if no
Complete of the key was answered. A tag stands for S3's ETag, a digest of the part.

Proved, for every run the model allows (`Multipart.read_listed`, `Multipart.completed_sent`,
gated): an object a read is answered with consists exactly of the parts some Complete of its key
listed, in order, each sent as that part of that upload with the tag listed; and a Complete is
answered `completed` only for such a listing.

Checked (`Tests/Multipart.lean`, rule 5.1): the flow, as an actor, against the model with each
call answered, lost, refused for a moment, refused as gone or as a wrong part; every Complete it
sends lists the plan's parts in order with the tags answered, it is done only when the store may
hold that object, and failed only when no Complete was answered (20,610 states, a part sent
twice, a Complete twice, done by `HEAD` after a lost Complete, an abort, all reached). And a
browser that puts every part at once, puts again a part whose answer was lost and completes again
when that answer is lost: every object the store may hold is the parts in order (4,434 states).
Not modelled: ListParts, part sizes (the fake checks them), and the order between two uploads of
one key.

## Checked against AWS's example, botocore and a fake

`Tests/S3Upload.lean`: AWS's documented `POST` example (`sigv4examplebucket`, 29 December 2015)
remembered, not fetched; its signature, computed from the remembered policy with the documented
secret, is the remembered one (`8afdbf40…`), which a policy misremembered would not give, and it
reads back as its eleven conditions; `Post.check` admits its form before the expiration and not
after, and refuses another key, another type and an unnamed field. botocore 1.44's
`generate_presigned_post`, run at a fixed time in a scratch environment, for an exact key with a
type and a range of 1 byte to 2 GiB, a prefix with a session token, and a path-style bucket at a
port: its policies decode to the documents Lanes writes, its signatures are Lanes' signatures of
its policies, and its fields are Lanes' fields, in order. Its presigned `UploadPart` URL has the
signature `presignPart` computes.

The test kit's fake S3 (`Lanes/Testing/S3.lean`), which `Tests/S3Upload.lean` and
`examples/videos` run against, takes a form only with the policy's signature and token, runs `Post.check` and refuses as S3 does; and multipart uploads with
S3's rules: ETags as MD5s, a multipart object's ETag as the MD5 of the parts' MD5s and their
number, parts out of order and sent again, a listing in order and with the last ETags, 5 MiB
before the last part, a Complete made twice answered the same, an abort. Against it: the
refusals of a file too large, too small, another key, another type, an unnamed field, a policy
changed after signing, an expired one, a missing token; `S3.upload` of 5 MiB and 3 bytes in two
parts, its run checked with the model's `Outside.allows`; a browser's parts through presigned
links, one whose length is not the one signed refused.

## The video site

`examples/videos` hands out a form, not a link: the key and content type exact, from one byte to
`maxUpload_bytes` (2 GiB, `VIDEOS_MAX_UPLOAD_BYTES`), for fifteen minutes; `upload.js` posts its
`FormData` and does not send a file over the limit. Its spec and proofs do not change: the
upload is still a write the site hands out and never hears answered. It does not use multipart:
2 GiB fits one `POST`, and resuming would need the site to keep each upload's id and parts. The
stack's bucket allows `POST` from the site's origin and exposes `ETag`, which a browser putting
parts needs.

## Not done, and not verified

- Nothing here has run against AWS. Not verified: that S3 refuses a presigned part whose
  `Content-Length` is not the one signed, as SigV4 says it must; S3's error codes for a form, as
  remembered; that a Complete made again is answered as the first for long enough.
- `success_action_status`, `success_action_redirect` and `x-amz-meta-*` fields are not written by
  `Post.form` (a `Policy` has no field for them), though `Post.check` reads them.
- A `POST` body is not streamed by the client; the browser sends it. `S3.upload` holds the body
  in memory and sends one part at a time; parts in parallel, and resuming an upload from
  `listParts` after a restart, are not done.

## For the owner

- Whether the per-member limit should be per upload (as here, every member alike) or a quota
  of bytes a member holds, which the spec would have to count from the `HEAD`'s size.
- Whether `Post.check`, a specification of S3's, belongs in `Lanes/` as here or with the fake.
