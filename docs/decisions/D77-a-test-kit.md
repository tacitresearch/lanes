# D77. A test kit, `Lanes.Testing`, beside `Lanes` and not in it

Status: Accepted

The fakes that the S3 client and the sign-in are tested against were test files of Lanes
(`Tests/S3.lean`, `Tests/OAuth.lean`), and each application that serves pages wrote its own
scripted browser: rookery, the ledger and the video site three times. An application outside
this repository cannot import `Tests`, whose name is any project's own. This adds a library of
what an application's tests run against, `Lanes.Testing` (`Lanes/Testing/`):

- `Testing.S3.Fake`, a fake S3 on a local port that checks every signature as S3 would, from the
  bytes it received, the presigned links' included (D71);
- `Testing.OAuth.Fake`, an identity provider of both kinds D72 signs in with, whose token
  endpoint checks the code, the client, the redirect URI and PKCE, and can issue faulty ID tokens
  a sign-in must refuse; `Testing.OAuth.signIn` plays the user who agrees;
- `Testing.Browser`, which keeps cookies by name and path and sends forms from its origin;
- `Testing.listen`, a server of a handler on a local port, and readers of a response.

## A third import root, not part of `import Lanes`

`Lanes.Testing` is a root of the `Lanes` library, as `Lanes.Proofs` and `Lanes.Semantics` are,
and `Lanes.lean` does not import it. A test imports `Lanes.Testing`; a binary that serves does
not, and does not link it. A separate Lake library was the other way. It would say the same
thing to Lake, but the modules are named `Lanes.Testing.*`, which Lake also finds through the
`Lanes` library's root, so two libraries would claim each module; and a library of its own in
this package is not one an application can require without the rest. A Lake package of its
own, under `integrations/`, would be cleaner to depend on and is not needed: an application
already requires `lanes`, and the kit imports nothing beyond it.

## Not trusted, not production, but listed

The kit performs IO, as the files that `TRUSTED.md` names do, and sits in no `IO/` directory:
the rule that IO is in `IO/` and named in `TRUSTED.md` is about what a deployed system's
properties rest on, and no deployed system runs the kit. What rests on it is the tests: a fake
that accepts what S3 refuses makes a test pass that should fail. So `TRUSTED.md` names it in a
section of its own, without line counts, outside the trusted total, and the kit is tested for
what it refuses (`Tests/Testing.lean`: a link signed with another secret, changed, for another
verb or bucket, or not signed at all; cookies kept and cleared as a browser keeps them).

The inventory lists the kit's definitions as it lists every public definition of `Lanes/`
(D47), under their own area, `Lanes/Testing`. Their status is what the tests give them,
"tested", since a test of `Tests/` uses each; that status says they ran, as it does for every
other definition, and the decision above is what says what the kit is for.

## What stays in `Tests/`

What is a test and not a fake stays: the vectors, the model checks, and the cases each file
asserts. The kit is what more than one test, or an application, runs against.
