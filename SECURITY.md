# Security

## Reporting

Report a vulnerability privately through GitHub: the repository's **Security** tab, then
**Report a vulnerability**. Do not open a public issue for one. Say what is affected, the
version or commit, and the smallest input or program that shows it. You get an answer in the
advisory's thread; a fix is coordinated there and published with the advisory.

## In scope

- The trusted code: everything `TRUSTED.md` lists, the runtime shell, the transport between
  processes, the journal's files and the adapters' IO among it.
- The HTTP server and the parsers: the request reader, the response reader, the wire format,
  forms, cookies, routes, JSON, Base64, IP addresses, dates.
- The cryptography bindings and what is built on them: libsodium through `native/lanes.c`,
  signed tokens, form tokens, sessions and password digests.
- A theorem whose statement does not mean what its docs say: a headline theorem that is
  vacuous, has a premise its docs leave out, or states less than `README.md`,
  `docs/ARCHITECTURE.md` or `docs/INVENTORY.md` claims. Lanes' claims rest on its theorems, so
  this is a vulnerability, not a documentation bug.
- The CI workflows and the runner machine (`docs/RUNNERS.md`).

Out of scope: the Lean kernel, compiler and runtime, `Std`, libuv, libsodium itself and the
operating system; report those to their projects. Applications built on Lanes are in scope only
where the fault is in Lanes.

## Supported versions

The latest 0.x release. A fix goes into a patch release of it (`docs/RELEASING.md`); older
releases get no fixes.
