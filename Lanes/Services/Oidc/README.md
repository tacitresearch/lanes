# Sign-in providers

Presets of the generic sign-in, which is core because it is a protocol: OAuth 2.0 and OpenID
Connect (`Lanes/Web/Auth/OAuth.lean`, `Lanes/Web/Auth/Jose.lean`, `Lanes/Web/IO/SignIn.lean`,
`docs/decisions/D72-sign-in-with-oauth.md`). A preset is a `Provider`: its endpoints, its
issuers and where the identity comes from. Its tests are in `Tests/Oidc/`.

| Preset | Client | Model | Oracle | Status |
| --- | --- | --- | --- | --- |
| Google | `Google.lean`, an OpenID Connect provider | The core's flow, model-checked against an attacker's browser (`Tests/OAuth.lean`), and its fake provider (`Lanes/Testing/OAuth.lean`) | Google's discovery document and JWK Set, recorded in `oracles/google/` (`Tests/Oidc/Google.lean`) | checked |
| GitHub | `GitHub.lean`, an OAuth app and an identity read from GitHub's user API | The same | None: answers in the shapes GitHub's documentation gives, written by hand (`Tests/Oidc/GitHub.lean`) | experimental |
