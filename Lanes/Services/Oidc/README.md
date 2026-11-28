# Sign-in providers

Presets of the generic sign-in, which is core because it is a protocol: OAuth 2.0 and OpenID
Connect (`Lanes/Web/Auth/OAuth.lean`, `Lanes/Web/Auth/Jose.lean`, `Lanes/Web/IO/SignIn.lean`,
`docs/decisions/D72-sign-in-with-oauth.md`). A preset is a `Provider`: its endpoints, its
issuers and where the identity comes from: configuration, tested against responses recorded
from the vendor or written from its documentation. Status: **client only**
(`docs/decisions/D113-service-models.md`); the protocol's proofs stay in `Lanes/Web/Auth/`. Its
tests are in `Tests/Oidc/`.

| Preset | Client | The protocol's model, in the core | Tested against | Status |
| --- | --- | --- | --- | --- |
| Google | `Google.lean`, an OpenID Connect provider | The core's flow, model-checked against an attacker's browser (`Tests/OAuth.lean`), and its fake provider (`Lanes/Testing/OAuth.lean`) | Google's discovery document and JWK Set, recorded in `oracles/google/` (`Tests/Oidc/Google.lean`) | client only |
| GitHub | `GitHub.lean`, an OAuth app and an identity read from GitHub's user API | The same | Answers in the shapes GitHub's documentation gives, written by hand (`Tests/Oidc/GitHub.lean`) | client only |
