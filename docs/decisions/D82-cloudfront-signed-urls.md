# D82. CloudFront signed URLs and cookies, and signatures made with a private key

Status: Accepted

A site such as `examples/videos` keeps its content private in S3 and hands browsers presigned
links (D71). Behind a CDN, the link is CloudFront's: a URL that carries a policy, a signature by
a private key the site holds and the ID of the public key CloudFront was given. Lanes could
check signatures under a public key (`native/verify.c`, D72) but not make one. This adds both:
signing with a private key, in `Lanes/`, and CloudFront's links and cookies, in the AWS
integration.

## What CloudFront expects

AWS's documentation pages could not be fetched from here; what follows is from three
implementations by AWS, read at the versions named, and from AWS's announcements as search
results quote them.

- botocore 1.44.12, `botocore.signers.CloudFrontSigner`, which the oracles already pin: a canned
  policy is `{"Statement":[{"Resource":…,"Condition":{"DateLessThan":{"AWS:EpochTime":…}}}]}`,
  compact, in that order, and a link to it carries `Expires`, `Signature` and `Key-Pair-Id`, in
  that order, after `?` or, when the URL has a query, `&`. A custom policy adds `IpAddress`
  (`AWS:SourceIp`, a CIDR, `/32` when bare) and `DateGreaterThan` to the condition, and the link
  carries `Policy` in place of `Expires`. Base64 with `+`, `=` and `/` written `-`, `_` and `~`.
  It signs over SHA-1 only.
- The AWS SDK for Go v2, `feature/cloudfront/sign` v1.12.13: it signs with any `crypto.Signer`,
  ECDSA among them since v1.10.0, which writes a DER signature; since v1.11.0 a hash, SHA-1 or
  SHA-256, and then `&Hash-Algorithm=SHA256` after `Key-Pair-Id`, and the cookie
  `CloudFront-Hash-Algorithm`. Its cookies are `CloudFront-Policy`, `CloudFront-Signature` and
  `CloudFront-Key-Pair-Id`, `HttpOnly`.
- The AWS SDK for JavaScript v3, `@aws-sdk/cloudfront-signer` 3.1177.0: the same, with
  `Hash-Algorithm` for SHA-256 and, for a canned policy, the cookie `CloudFront-Expires`.
- AWS's announcements: ECDSA keys for signed URLs and cookies (September 2025), and SHA-256 with
  `Hash-Algorithm=SHA256` (April 2026), SHA-1 when the parameter is absent. The developer
  guide's pages, as search results quote them, take "RSA 2048 and ECDSA 256" keys, and sign with
  `openssl sha1 -sign`, which writes a DER ECDSA signature under an EC key.

So the ECDSA option is P-256, its signature DER, over SHA-1 or SHA-256 like RSA's; that is what
both SDKs send. No example by AWS with a published private key was found: the tests use
published keys of RFCs instead (below), and none of AWS's is made up.

## Signing is in `Lanes/`, CloudFront in the integration

`Lanes.SigningKey` (`Lanes/Lib/Crypto/Sign.lean`, `native/sign.c`) is not CloudFront's: a JWT
signed with RS256 or ES256 needs it too. It sits beside the check, as D72 placed that.

CloudFront's links are one vendor's format, not a protocol a class of systems speaks, which is
what took S3 into `Lanes/` (D71). D61 puts a vendor in `integrations/`, and `integrations/aws`
exists now (D74), with an axiom gate (`integrations/aws/Aws/Axioms.lean`) and a pure oracle run by
`lake exe oracle`, which CI's oracle job already runs. So `Aws.CloudFront` is
`integrations/aws/Aws/CloudFront.lean`, proved in `integrations/aws/Aws/CloudFrontSound.lean`.

## The binding

The C is as small as the job allows, three functions.
`lanes_private_key_read` reads the first private key of a PEM with `PEM_read_bio_PrivateKey`
over a memory BIO and keeps it, OpenSSL's `EVP_PKEY`, in a Lean external object that frees it
when Lean drops it, so a key is parsed once. An encrypted key is refused, with a password
callback that fails, rather than asked a password for on the terminal. `lanes_private_key_spki`
gives the public half as DER (`i2d_PUBKEY`). `lanes_private_key_sign` signs with
`EVP_DigestSign` over SHA-1 or SHA-256. Nothing else of the key leaves the C, and every failure is
`none` with no reason, so no error says what a key held; `SigningKey` prints as `<signing key>`.

Lean decides which keys are taken, from the public half: `PublicKey.ofSpki?` reads the DER back
only when `PublicKey.spki` writes it again (`PublicKey.ofSpki?_spki`), and a `SigningKey` holds
a key of `PublicKey.valid`, RSA of 2048 to 8192 bits or P-256, with the proof that it is the
key's. The CloudFront signer takes RSA of 2048 bits and P-256 only.

Signing is pure, because it is a function: RSASSA-PKCS1-v1_5 is deterministic, and ECDSA is told
to take its nonce as RFC 6979 says (`nonce-type`, OpenSSL 3.2 and later; the toolchain ships
4.1.0), which Lean asks for under a P-256 key. A link can then be made where S3's presigned links
are, in a view or a step, with no IO, and a test can compare signatures byte for byte. Signing in
`IO` with a random nonce was the other choice; it would have put every link behind an effect.

## What is proved

- The canned policy is byte for byte the document AWS gives for the URL and the time
  (`Aws.CloudFront.cannedPolicy_eq`), since CloudFront builds it again from the link to check the
  signature. A resource is visible ASCII but `"` and `\` (`Resource`), so JSON writes it as it is;
  botocore would escape such characters, but a browser sends a URL with them escaped as `%XX`.
- CloudFront's base64 reads back (`Aws.CloudFront.decode_encode`); it swaps `+`, `=`, `/` with
  `-`, `_`, `~` both ways, an involution, which is the documented map on what base64 writes.
- Every parameter is named by a token and valued in letters, digits, `-`, `_` and `~`
  (`Aws.CloudFront.fields_safe`), so a link needs no escaping and every cookie is valid
  (`Aws.CloudFront.cookies_valid`): `Response.setCookie` drops none.

That a custom policy reads back as its document is not proved here: its times are numbers of any
size, and `Json.parse_compress` wants at most 1000 digits. The oracle compares it byte for byte.

## Checked

- `Tests/Sign.lean`: RFC 9500 §2.1's RSA key, as Go keeps it in `crypto/rsa/example_test.go`, and
  RFC 6979 A.2.5's P-256 key, written as PEM from its secret, are in `oracles/botocore/keys/`
  with the label `TESTING KEY`, as Go writes them, so no scanner takes them for secrets. RFC
  6979's signatures of "sample" and "test" with SHA-256 are made exactly; RSA signatures check
  under the public half, by the binding and `Rsa.verifyReference`; with `openssl`, RSA signatures
  are byte for byte those of `openssl dgst -sha1 -sign` and `-sha256 -sign`, ECDSA ones check
  under `openssl dgst -verify`, the public key's PEM is `openssl pkey -pubout`'s, and an
  encrypted key, RSA of 1024 bits, P-384, secp256k1 and Ed25519 are refused.
- `scripts/tls-declarations.py` checks `native/sign.c`'s declarations against the system's
  headers, as for `native/tls.c` and `native/verify.c`.
- `integrations/aws/Checks/CloudFront.lean`, against botocore's `CloudFrontSigner`, which signs
  with `cryptography` 50.0.2 (RSA with PKCS #1 v1.5, ECDSA with RFC 6979's nonce), on generated
  links, canned and custom, under both keys and both hashes: the policy and the whole link,
  signature included, are the same bytes. botocore 1.44 knows no `Hash-Algorithm`, so the
  reference appends it last, as the SDKs do. The one difference is a resource ours refuses
  (space, quote, backslash, non-ASCII), which botocore signs. 200 answers are recorded in
  `oracles/botocore/cloudfront.jsonl` for `lake test` in the integration.

## How the video site would use it

Not in this change. `examples/videos` would require `integrations/aws` and give its `Settings` a
`cdn : Option Cdn` of a `CloudFront.Signer` and the distribution's origin, read at start from a
key file and an ID the environment names (`Signer.ofPem id (← IO.FS.readBinFile path)`). Where it
makes a presigned GET today (`Videos/Web.lean`, `S3.presign … .get`), it would make
`signer.url ⟨origin ++ "/" ++ key, _⟩ (.canned (now_s + ttl_s))` when a CDN is set; uploads stay
presigned PUTs to S3. A video cut in segments (HLS) needs one grant for many files: cookies of a
custom policy on `origin/videos/<id>/*`, set with the watch page. The checks run unchanged, since
a link is a pure value of the time.

## Not done

- Cookies have no `Domain`: `Http.Cookie` has no such attribute, and adding one changes
  `Lanes/Web/Http/CookieSound.lean`. So signed cookies work only when one host serves both the
  site and CloudFront's content, the site behind CloudFront; a CDN on another subdomain needs a
  `Domain` cookie, for the owner to decide.
- A key in an encrypted PEM; a key group of several keys (one `Signer` per key; rotating is
  choosing which); IPv6 ranges in a policy (`Cidr` is IPv4, as AWS's examples are).
- A test against CloudFront itself, and mutants of `scripts/mutants.py` for the signer.
