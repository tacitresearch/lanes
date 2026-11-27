| Test kit | `import Lanes.Testing`, for an application's tests and not in `import Lanes` (`docs/decisions/new-a-test-kit.md`): a fake S3 on a local port that checks every signature as S3 would, presigned links' included, and keeps the objects; a fake identity provider of OpenID Connect (ID tokens signed with an RSA key `openssl` makes, a JWK Set, and faulty tokens a sign-in must refuse) and of OAuth 2.0 with a user API shaped as GitHub's, whose token endpoint checks the code, the client, the redirect URI and PKCE; a scripted browser that keeps cookies by name and path and sends forms from its origin; a server of a handler; readers of a response. `Tests/S3.lean`, `Tests/OAuth.lean` and `examples/videos` run against it | `Lanes/Testing/` |

- The fake S3 checks signatures with the functions the client signs with, so it agrees with the
  client by construction; that they are S3's is tested against AWS's vectors (`Tests/SigV4.lean`).
- The browser runs no script and follows no redirect, and ignores a cookie's domain, expiry and
  `Secure`.
- Without the `openssl` command the fake provider issues no ID token.
