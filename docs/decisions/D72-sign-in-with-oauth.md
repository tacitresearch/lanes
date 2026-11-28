# D72. Sign-in with OAuth 2.0 and OpenID Connect, done where a request arrives

Status: Partly superseded by new-volatile-actors.md (each provider a Lake package of its own: Google and GitHub are presets of `Services/Oidc`)

The first application Lanes is for is a video site whose users sign in with Google or GitHub.
This adds the authorization code flow with PKCE (RFC 6749 §4.1, RFC 7636), OpenID Connect's ID
token on it (OpenID Connect Core §3.1), the signatures it needs (RS256 and ES256), and presets for
the two providers. What decides is pure and in `Lanes/Web/Auth/` (`Jose.lean`, `IdToken.lean`,
`OAuth.lean`); what performs is `Lanes/Web/IO/SignIn.lean`; the signature check is bound from the
OpenSSL Lean's toolchain ships (`native/verify.c`); the vendors are packages under
`integrations/`; `examples/sign-in` signs members in and gives them sessions.

## The flow

- *Begin.* `GET /sign-in/<provider>`. Four values of 32 bytes each from libsodium's random source
  (`randomBytes`), written in base64url: the `state`, the `nonce`, the PKCE verifier (43
  characters, its challenge `S256`), and a value set in a cookie that binds the sign-in to the
  browser. The pending sign-in is kept under its state with an expiry (`Settings.ttl_ms`, ten
  minutes) and at most `Settings.maxPending` are kept, the oldest dropped first (rule 2.6). The
  browser is sent to the provider with a `302`. The cookie is `HttpOnly`, `SameSite=Lax`
  (the callback is a top-level navigation from the provider), `Secure` unless turned off for a
  test over plain HTTP, and sent only to `/sign-in`.
- *Callback.* `GET /sign-in/<provider>/callback?code&state`. The state is looked up, compared in
  time that does not depend on where it differs, and removed whatever the answer: it is used once.
  It is accepted only from the browser whose cookie it was issued with, on the route of the
  provider it was issued for, and before it expires. A provider's error (`error=access_denied`)
  uses the state up too.
- *Exchange.* The code is posted to the token endpoint with the verifier, the redirect URI and
  the client's secret in the body (`client_secret_post`, which Google and GitHub both take), over
  the HTTP client and so over TLS (D67). The answer must be a bearer token; an error code is a
  refusal.
- *Identity.* An OpenID Connect provider's ID token is verified (below). A provider of OAuth 2.0
  alone is asked who the user is with the access token, at the URLs its preset names, and the
  preset's `read` makes an identity of the JSON answers. Either way the system gets an `Identity`:
  issuer and subject, which name a user and do not change, and an email with whether the provider
  says it verified it.

Proved (gates in `Tests/Axioms/Web.lean`): a callback is accepted only for a sign-in kept under
its state, from its browser, for its provider and before its expiry
(`OAuth.Pending.callback_ok`); after a callback no sign-in waits under its state
(`Pending.callback_removes`); over any run of beginnings and callbacks from none, no state is
accepted more often than it was issued (`Pending.accepted_le_issued`), so a state issued once is
accepted at most once; at most `maxPending` wait (`Pending.length_begin`). Model-checked
(`Tests/OAuth.lean`): the store as an actor against two browsers, one an attacker's, that replay
callbacks, present each other's state (the attacker the victim's, and the victim's browser the
attacker's, which is login CSRF) in every order and through a restart that empties it: no state
is accepted twice, and none from a browser it was not issued to.

## Where it runs: before the system, not in it

The flow is not an actor of the application's system. Its inputs would be journalled (D24): the
callback's request carries the code, and a job that exchanged it would hand back the access token
and the ID token as inputs. D44 keeps secrets out of the journal by preparing a request before it
enters, but `Bridge.prepare` is pure and the exchange is IO, which a step may not do (rule 2.4).

So `serve` (and `serveWith`, `serveFronted`) take `arrive : Request → IO (Except Response
Request)`, run on a task of the request's own before `prepare`: what it returns enters as the
request, or is the answer and nothing enters. `SignIn.arrive` drops identity headers a client
sent, answers a beginning with the redirect, and lets a callback in only with the identity it
verified, in headers (`OAuth.identity?` reads them; `identity?_withIdentity`, `identity?_strip`),
without its query; a refused callback is answered `403` with the reason. Codes, tokens, the
verifier and the client's secret therefore never reach the system or its journal, and the
system's theorems are unchanged: they hold of every input.

This departs from D44 in one way: D44 refused to let IO answer a request, since answering is the
gate's. Here a beginning and a refusal are answered by `arrive`, as the server already answers
`503` and `501` itself. The gate's theorems are about the requests it receives and are not
touched; what the edge answers depends only on the edge's store, which the system does not have.
Requests of one connection may now enter the system in another order than they were read when
`arrive` is given; their answers are still written in that order (`Conn`). The pending sign-ins
live in memory, as the server's `Waiting` does: a pure structure in a reference, used through
`modifyGet`. A restart loses them, and their callbacks are refused (`unknownState`); the user
begins again. Keeping them in the system, journalled, would survive a restart and put the
verifier in the journal.

## Signatures

An ID token is a JWS (RFC 7515). `Jose.Compact.read` takes it apart and reads `alg` only through
`Alg.parse?`, the allow-list of `RS256` and `ES256`: `none`, `HS256` and every other name are
refused by name before a key is looked at, and a header with `crit` is refused. A key of the JWK
Set (RFC 7517) checks only the algorithm of its type (`Jwk.fits`): an RSA key RS256, a P-256 key
ES256, so an RSA public key is never an HMAC secret. Keys that are for encryption, of another
algorithm, an RSA modulus under 2048 or over 8192 bits, an even exponent, or EC coordinates not
of 32 bytes are not read. A token naming a `kid` is checked only by the key of that `kid`.
`Jose.verify_ok` and `IdToken.verify_accepted` state what an accepted token is: a header naming
RS256 or ES256, a key of the set of that algorithm and `kid` under which the signature checks,
and every claim check of `IdToken.Accepted` passing (`IdToken.check_ok_iff`): the issuer one of
the provider's, this client among the audiences, this client the authorized party when there are
several or when `azp` is given, not expired and not before `nbf` within a skew of 60 s either
way, and the nonce the sign-in's. `iat`, `auth_time`, `acr` and `at_hash` are not checked.

The check itself is libcrypto's, from the copy of OpenSSL the toolchain ships (D67): Lean writes
the key as a DER `SubjectPublicKeyInfo` and an ES256 signature, which JWS writes `r ‖ s`, as DER,
and `native/verify.c` reads the key with `d2i_PUBKEY`, refuses it unless every byte was read, and
calls `EVP_DigestVerify` with SHA-256, PKCS #1 v1.5 padding being OpenSSL's default for RSA. It
declares eight functions; `scripts/tls-declarations.py` now checks this file's declarations too.
Which key may check which signature, and the size a signature must have, are decided in Lean
(`PublicKey.derSignature`), so the C chooses nothing.

Verification uses only public values, so D46's reason to bind, a time that leaks a secret, does
not apply, and RS256 could be Lean alone: `Rsa.verifyReference` is RSASSA-PKCS1-v1_5 with SHA-256
(RFC 8017 §8.2.2) in Lean, by building the encoding and comparing, not by parsing it, which is
the way around signature forgeries of lax parsers. It is the binding's reference, compared with it
on every vector and on every signature changed in one byte. The binding is used because the task
named OpenSSL, because ES256 needs P-256 arithmetic Lanes does not have, and because OpenSSL's
is the code every client uses. Using the reference for RS256 instead would take one line and
remove RSA from the trusted code; that is for the owner.

Keys are fetched from the provider's JWK Set URL and kept per provider (`OAuth.Keys`). A token is
checked with the keys held when they are younger than `maxAge_ms` (an hour) and hold its `kid`;
otherwise the set is fetched, but never sooner than `minRefresh_ms` (a minute) after the last
fetch (`Keys.lookup_fetch`, `Keys.no_fetch_within`), so tokens naming keys the set lacks cannot
make a server call the provider more often. The edge claims a fetch before it makes it, so
concurrent callbacks do not fetch twice. A fetch that gives no set keeps the keys held.

## Providers: classes in Lanes, vendors in `integrations/`

D61 keeps vendors' names out of `Lanes/`. The two classes are in `Lanes/Web/Auth/OAuth.lean`:
`Source.idToken issuers jwks`, OpenID Connect, and `Source.userApi urls read`, OAuth 2.0 whose
user is known from an API. A `Provider` gives its endpoints explicitly, as a discovery document
does; `Discovery.read` reads such a document kept with the deployment, and nothing is fetched
from `.well-known` at run time. Each vendor is a Lake package of its own, as D61 says, so that it
can change with the vendor's releases, or be dropped, without a release of Lanes:

- `integrations/google`: the endpoints and the two issuers Google's ID tokens name
  (`https://accounts.google.com` and `accounts.google.com`). Its check reads Google's discovery
  document and JWK Set as fetched on 2026-11-27 (`integrations/google/recorded/`): the endpoints
  are the document's, its issuer is accepted, it signs with RS256 and takes S256, and its keys are
  read.
- `integrations/github`: GitHub's OAuth app, with no ID token: `GET /user` for the user's `id`,
  never the `login`, which a user may change, and `GET /user/emails` (scope `user:email`) for the
  primary address and whether it is verified. `GitHub.read` is total and refuses answers of any
  other shape. The answers its check reads are written by hand in the shapes GitHub's REST
  documentation gives; none was recorded, since this machine could not reach GitHub's API.
  GitHub's token endpoint answers JSON when asked (`Accept: application/json`) and reports an
  error with status 200, both handled; whether GitHub checks the PKCE verifier was not confirmed:
  a provider that ignores it is no weaker than OAuth 2.0 without PKCE.

Each is a few dozen lines, which would fit in `Lanes/` as data. They are packages anyway because
D61 says where a vendor goes, and because what they hold (URLs, issuers, the shape of an API's
answers) is what changes with the vendor and is checked against recordings of it, as D61 asks of
an integration. CI builds and checks both, and `examples/sign-in`, which uses them.

## Secrets

`OAuth.Secret` holds a client secret, a code, a token or a verifier; its `Repr` and `ToString`
print `<secret>`, so a `Client`, a `Grant` or `Tokens` printed shows none (tested). Nothing in the
sign-in prints or logs. A refusal names its reason, and the provider's error code when there is
one, never a value.

## Checked

`Tests/Signature.lean`: RFC 7515 Appendix A.2 (RS256) and A.3 (ES256) and RFC 7520 §4.1 (RS256 with
a `kid`) verify; A.1 (HS256), A.5 (`none`) and RFC 8037 A.4 (EdDSA) are refused by name; keys of
another type or `kid` and another key refuse; the binding and the Lean reference agree on the
vectors and on signatures changed in one byte; keys made by `openssl` at test time (RSA of 2048
and 3072 bits, P-256) have the DER Lean writes and verify what `openssl dgst -sign` signs. The
vectors are taken from the test suite of jwcrypto 1.6.2, which carries the RFCs' appendices; the
RFCs' own text could not be fetched here. The signature of A.2 and the PKCE vector of RFC 7636
Appendix B match those remembered from the RFCs, and every vector verifies under OpenSSL and the
Lean reference, which a corrupted copy would not.

`Tests/OAuth.lean`: each decision alone; the model check above; and the flow end to end over HTTP
against a provider run in the test (a token endpoint that checks the client, the redirect URI
and the PKCE verifier, and signs ID tokens with an RSA key made by `openssl`; a JWK Set; a user
API). A sign-in gives the system the identity and no query. Refused: the same callback again, a
state never issued, a callback from another browser, an ID token expired, for another audience,
from another issuer, for another nonce, with `alg: none`, with HS256 keyed by the RSA public key
as PEM, of a `kid` the set lacks, or whose payload was changed after it was signed; identity
headers a client sends; the provider's error. The JWK Set is fetched once across them all. The
mutants of `scripts/mutants.py` named `signature`, `jose`, `id token`, `oauth`, `sign-in` and the
server's `arrive` each fail a test or no longer build.

## What is trusted

- `native/verify.c` and OpenSSL's signature code; that the C declares OpenSSL's functions as
  OpenSSL does (checked in CI).
- `Lanes/Web/IO/SignIn.lean`: that it performs what the pure functions decide, in order, keeps
  the store and the keys in references used atomically, and prints nothing; and the server's
  `arrive` (`Lanes/Web/IO/Server.lean`).
- That a provider is honest: its JWK Set, fetched over TLS from the URL its preset names, holds
  only its keys, and it signs only tokens it means. The TLS client is D67's.
- The wall clock, for expiries and `exp`; a clock far off refuses every token or accepts expired
  ones within the error.

## Not done

Refresh tokens and calling a provider's APIs later; the UserInfo endpoint of OpenID Connect;
fetching `.well-known` at run time; RFC 9207's `iss` parameter on the callback (a state is bound
to its provider, which refuses a mix-up between the providers of one deployment); signing out at
the provider; PS256, ES384, EdDSA; `private_key_jwt` and other client authentication; pushed or
signed authorization requests.

## For the owner

- Whether IO may answer a request before the system, as `arrive` does (above, against D44).
- Whether RS256 should be checked by `Rsa.verifyReference` alone, removing RSA from the trusted C.
- Whether one package per vendor under `integrations/` is the shape, or one package of presets.
- Whether pending sign-ins should survive a restart, journalled, at the price of the verifier in
  the journal.

*Amendment: the browser keeps the sign-in.* A review found that anyone could evict every pending
sign-in: `GET /sign-in/<provider>` needs nothing, and the table of 1024 dropped its oldest, so
about a hundred requests a second refused every user's callback. The server now keeps nothing for
a sign-in begun. The binding cookie holds a `Ticket`, the provider, the state and the expiry,
under an HMAC-SHA-256 tag (`Auth.sign`, purpose `sign-in`) by a key `SignIn.start` draws; the
nonce and the PKCE verifier are tags of the state under the same key (`Ticket.grant`), so neither
is in the cookie, which a callback carries into the system. The cookie is `__Host-lanes-sign-in`,
with `Path=/`, unless `secure` is off for a test over plain HTTP. A callback is accepted only with
the ticket of its own cookie, which only the key can make, for its state, on its provider's route
and before its expiry (`OAuth.check_ok`): bound to its browser and its provider, and expiring, as
before. After the code is exchanged and the identity verified, the state is claimed in `Used`,
the one structure the server keeps: the states of accepted callbacks with their expiries, and a
floor below which tickets are refused. A state claimed is refused again (`Refusal.used`), so over
any run a state is accepted again only with a ticket that expires later (`Used.accepted_later`),
and since the key tags one ticket for each random state, no state is accepted twice
(`Used.accepted_once`). `Used` holds at most `Settings.maxUsed` states (16384;
`Used.length_claim`), each dropped when its ticket expires. When it is full it drops the oldest and
raises the floor to their expiries: their replays stay refused, and so do the tickets that expire
no later, sign-ins begun before them; a newer ticket is accepted. No live state is forgotten, and
since a state is claimed only after the provider gave a code for it, filling the set takes a
sign-in at the provider for each state, not one anonymous request. The key is drawn at each
start and the states used are in memory, so a restart refuses the callbacks of sign-ins begun
before it, as it did. A provider's error no longer uses up a state, which is now only in the
browser. An identity from a provider with several issuers names the first
(`OAuth.Identity.under`), so Google's two issuers give a user one key. `Tests/OAuth.lean`
model-checks the edge with its tickets in two browsers' cookies, the states used and a restart
that draws another key; the properties are those above.
