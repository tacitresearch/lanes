# D67. A TLS client, from the OpenSSL Lean's toolchain ships

Status: Accepted

Applications have to call HTTPS APIs: S3, SES, Stripe, OAuth providers. The HTTP client spoke
plain HTTP/1.1 only. This adds a TLS 1.2 and 1.3 client under it, bound from C as D46 says
(rule 2.7): what decides stays in Lean, and the C is counted in `TRUSTED.md`. The choice of
library is the owner's to confirm; the binding is written so that changing it touches
`native/tls.c` and the Lake file and nothing else.

## No server

There is no TLS server. On AWS the load balancer terminates TLS (an ALB or NLB with a TLS
listener and an ACM certificate) and talks HTTP to the instances inside the VPC; elsewhere a
proxy does (Caddy, nginx). A server would add certificate and key handling to the trusted code
for nothing in those deployments. Encryption to the instance, or mutual TLS between shards, is a
later decision if it is wanted.

## The shape of the binding

The binding does no IO. A session is OpenSSL's `SSL` over two memory BIOs: what arrives from the
server is handed to `feed`, what `take` returns is sent, and `handshake`, `write`, `read`,
`closed` and `shutdown` move the state on; errors are thrown with OpenSSL's reason and, when a
certificate was refused, why (`hostname mismatch`, `unable to get local issuer certificate`).
So it sits under the client's existing socket (`Std.Net`, whose descriptor Lean does not
expose), reads and writes in any pieces, and never blocks. Closing is the socket's; the `SSL` is
freed when Lean drops the session. A context is made per session, which loads the trust store
each time: about 3 ms for Ubuntu's 146 certificates, measured as 5.6 ms a local call against
2.6 ms with a file of one. Keeping one is an optimisation for later.

What is sent and what the bytes mean stay in the pure client: `Request.wire` writes the request,
`Response.read` reads the response, unchanged. One decision is new and stated in the client: a
response is ended only by the server's `close_notify`. A connection that ends without one may
have been cut by an attacker, so a response framed by the end of the connection and cut short
is no answer, while one framed by its length is read as soon as it is whole, as before.

Verification cannot be turned off. The certificate must chain to the trust store, be for the
name called (`SSL_set1_host`, no partial wildcards) or, for an IPv4 address, for that address,
and the name is sent as SNI. TLS 1.0 and 1.1 are refused. Revocation is not checked, as Go and
most clients do not. Tests use a trust store of their own, `Tls.Trust.file`, which is a choice
of roots, not a switch; production may use it for a private CA.

The trust store `.system` is the file `SSL_CERT_FILE` names, as for OpenSSL and Go, or else the
first of a list of files that systems keep: the list Go's `crypto/x509` uses on Linux, then
Homebrew's bundle, then `/etc/ssl/cert.pem`, which macOS and the BSDs have. On macOS that last
file is not kept up to date with the keychain (on GitHub's runners it lacks the root example.com
chains to), so a Mac without Homebrew should set `SSL_CERT_FILE`. It is not the macOS keychain:
roots an administrator added there are not seen. A binary built on
one distribution therefore finds the store on another, which the paths compiled into an OpenSSL
do not give.

Names are resolved now (`getaddrinfo`, the first IPv4 address), for `http` as for `https`, since
a certificate is for a name. `Call.at "https://host[:port]"` builds a call from an origin. There
is no proxy (`CONNECT`) and no IPv6.

## The options

| | OpenSSL 3, the system's | OpenSSL, as Lean ships it | AWS-LC (and s2n-tls) | BoringSSL | rustls via rustls-ffi | mbedTLS |
| --- | --- | --- | --- | --- | --- | --- |
| What becomes trusted | OpenSSL's TLS and X.509 code, several hundred thousand lines of C; a second copy beside the toolchain's | The same code, of which every Lean executable already links a copy (only its version is called today) | A BoringSSL fork of similar size; s2n-tls adds its own state machine, small, over a libcrypto | Similar to AWS-LC, vendored into this repository | rustls (Rust), and a crypto provider: aws-lc-rs by default (C and assembly) or ring | Smaller, tens of thousands of lines of C |
| Memory safety and verification | C; no verification | C; no verification | C; parts verified: AES-GCM, SHA-2, HMAC, the DRBG and some elliptic curves with SAW and Cryptol, big-number code with HOL Light (s2n-bignum); FIPS 140-3 validated. s2n-tls's handshake state machine and HMAC are verified with SAW | C; some field arithmetic generated from Coq proofs (fiat-crypto) | Protocol code memory-safe Rust, audited (Cure53, 2020); crypto as its provider | C; no verification |
| Ubuntu 24.04 | `libssl-dev` 3.0.13 | Nothing to install | Not packaged | Not packaged | Not packaged | `libmbedtls-dev` 2.28.8, a branch out of support since the end of 2024 |
| Homebrew | `openssl@3` 3.5.9, keg-only, so `pkg-config` needs a path | Nothing to install | `aws-lc` 5.15.0, keg-only (it conflicts with OpenSSL); `s2n` 1.7.14 | No formula | `rustls-ffi` 0.15.7 | `mbedtls` 4.3.0, `mbedtls@3` 3.6.8 |
| Static linking | Fails on Ubuntu 24.04: its `libcrypto.a` needs `__isoc23_strtol` from glibc 2.38, which the C library Lean's toolchain links against lacks (measured). Would put two OpenSSLs in one binary | Static by construction: `libssl.a` and `libcrypto.a` are in the toolchain's `lib/` on Linux and macOS (checked in the `darwin_aarch64` release), and `leanc` links them into every executable | Possible, but it exports OpenSSL's symbols, which clash with the toolchain's copy unless built with a symbol prefix | Vendored and built with CMake, Go and Perl; same clash | A static library from `cargo` | Static libraries packaged |
| The system's trust store | OpenSSL's compiled-in paths (Debian's, on Debian) | Its compiled-in paths are in the Nix store of its build, so the list of files above | `s2n_config` takes a file; AWS-LC as OpenSSL | As OpenSSL | rustls-platform-verifier, which also reads the macOS keychain | A file to parse |
| Maintenance and CVEs | Most-used library, an LTS (3.0 to September 2026, 3.5 to 2030); a long CVE record (Heartbleed, 2014; two high in 3.0 in 2022, the punycode overflows) | The same code; fixes reach Lanes when Lean releases a toolchain and Lanes moves to it, which follows CSLib | AWS maintains both, with regular releases | Google maintains it for its own products, without a stable API | Active, a small team; few CVEs, none of memory corruption | Arm and then TrustedFirmware; API changed at 3.0 and again at 4.0 |
| What users install | `libssl-dev`, and the static library works on some distributions only | Nothing | Build AWS-LC, or Homebrew's on a Mac only | Nothing (vendored), but the build needs CMake and Go | A Rust toolchain, or Homebrew's on a Mac only | `libmbedtls-dev`, out of support on Ubuntu 24.04 |
| macOS | Homebrew, with a `pkg-config` path | Works as on Linux | Homebrew | Builds | Homebrew | Homebrew |

## The choice: OpenSSL, the toolchain's copy

Recommended, for the owner to confirm. Lean's runtime requires OpenSSL 3 or later on every
platform but WebAssembly (`find_package(OpenSSL 3 REQUIRED)` in its CMake), and the release
toolchains ship it static (4.1.0 in `v4.37.0-rc1`) and link it into every executable; today the
runtime calls only `OpenSSL_version_num`, which suggests a TLS in `Std` later. So:

- users install nothing new, on Linux or macOS, and binaries stay static;
- OpenSSL's code is already in every Lean binary; what this adds to the trusted base is OpenSSL's
  TLS and certificate code being *used*, and `native/tls.c`;
- the system's OpenSSL cannot be linked statically on Ubuntu 24.04 at all, and would be a second
  copy beside the toolchain's.

The toolchain ships no headers, so `native/tls.c` declares the 34 functions and 10 constants it
uses as OpenSSL 3 and 4 declare them. `scripts/tls-declarations.py` compiles those
declarations against the system's OpenSSL headers, and CI runs it on Linux, so a declaration
that disagrees with OpenSSL's fails there. They are chosen from OpenSSL's API as LibreSSL and AWS-LC
also provide it (the `int` forms of read and write, not OpenSSL's `_ex` ones), so linking one of
those instead should change the Lake file only; that is not tried here.

The cost is that an OpenSSL fix reaches Lanes only through a Lean release and Lanes' next
toolchain, and that OpenSSL's record is that of a large C library. AWS-LC is the better library
on verification; it is not packaged on Ubuntu, and linked beside the toolchain's OpenSSL its
symbols clash, so it needs a build of its own with a symbol prefix. It is the first candidate if
a verified or FIPS-validated library becomes a requirement, and the binding would link it
unchanged. rustls is the better choice on memory safety and would replace `native/tls.c` (its
API is also sans-IO), at the price of a Rust toolchain for everyone who builds Lanes. When Lean's
`Std` has TLS, this binding should give way to it.

## Checked

`Tests/Tls.lean` runs the client against `openssl s_server`, with an authority, certificates and
a trust store made for the test by `openssl`: a certificate for the name and one for the address
are answered; a server that picks its certificate by SNI is answered; a certificate for another
name, one not for the address called, one from an authority not trusted, the test's authority
under the system's store, and a trust store that is not there are each refused; an answer framed
by the end of the connection is taken through a relay that passes everything, and refused
through one that drops the server's `close_notify`. Against a public server it runs when the
network reaches one, and is skipped otherwise. The mutants of `scripts/mutants.py` named `tls`
and `https client` (verification off, the name or the address not checked, no SNI, the trust
store given ignored, the call made in the clear, the end of the connection taken for
`close_notify`) each fail one of these.
