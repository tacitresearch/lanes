# D95. One crypto library: the OpenSSL Lean ships

Status: Accepted

`native/lanes.c`, `Lanes/Lib/Crypto/Native.lean`, `lakefile.lean`. The owner approved dropping
libsodium, so that building and running a Lanes application needs no C library beyond what
Lean's toolchain ships. This supersedes the part of D46 that chose libsodium as a system
library, found with pkg-config and linked statically.

## Why

Lanes had two crypto libraries. libsodium gave SHA-256, HMAC-SHA-256, the comparison of two byte
strings, random bytes and Argon2id. OpenSSL gave TLS, signature checks and signing (D67, D72,
D82). OpenSSL is not installed: Lean's toolchain ships a static libcrypto and links it into every
executable. libsodium was installed: every user, CI job, runner and deploy needed
`libsodium-dev` and `pkg-config`, Fedora a static package too, and Homebrew's headers outside
the compiler's path. Every function Lanes took from libsodium is also in that libcrypto
(OpenSSL 4.1.0 today), so the second library cost an install step and bought nothing.

## What replaces what

| libsodium | Now |
| --- | --- |
| `crypto_hash_sha256` | `SHA256` |
| `crypto_auth_hmacsha256_*`, `sodium_memzero` of its state | `HMAC`, which clears its own state |
| `sodium_memcmp` | `CRYPTO_memcmp` |
| `crypto_pwhash` (Argon2id 1.3) | the `ARGON2ID` KDF (`EVP_KDF_derive`), OpenSSL 3.2 or later |
| `randombytes_buf`, `sodium_init` | Lean's `IO.getRandomBytes` |

`native/lanes.c` declares the OpenSSL functions itself, as `native/tls.c` does, because the
toolchain's OpenSSL has no headers; `scripts/tls-declarations.py` compiles it against the
system's headers. The Argon2id parameters go through `OSSL_PARAM_BLD`, so the C never lays out an
`OSSL_PARAM` by hand, and are freed with `OSSL_PARAM_clear_free`, which wipes the copy of the
password. The C went from 147 lines to 188: fifteen functions and six type names, declared by
hand, replace one `#include`.

**Random bytes.** Lean's runtime reads `/dev/urandom` (`BCryptGenRandom` on Windows), the
operating system's secure source, so `randomBytes` is `IO.getRandomBytes` and the C has no random
function. Two differences from libsodium's `getrandom(2)`: it needs `/dev` mounted, and on Linux
`/dev/urandom` does not wait for the pool to be seeded, which matters only early in boot. Lean's
docstring says the bytes are "not guaranteed to be cryptographically secure": Lanes relies on the
implementation, not that promise, and `TRUSTED.md` says so.

## Password digests are unchanged

Lanes never stored libsodium's `crypto_pwhash_str` text: a digest is the raw 32-byte Argon2id
output of `crypto_pwhash`, with version 19, one lane, no secret, `ops` passes and `mem_kib` KiB.
OpenSSL's Argon2id with the same inputs gives the same bytes, so every digest in a journal still
verifies and there is nothing to migrate. Before libsodium was removed, its `crypto_pwhash` made
seven hashes and one `Password.digest`; they passed on the libsodium build and are fixtures in
`Tests/Crypto.lean` now: an empty password, one of 200 bytes, memory of 9, 13 and 1,023 KiB (not
multiples of four, which Argon2 rounds down) and the ledger's 19 MiB. Four strings that
libsodium's `crypto_pwhash_str` made are fixtures too: the hash in each is `Argon2id.hash` of its
salt at its cost, so a digest kept in that format by another program could be checked, though
Lanes reads and writes only raw digests. RFC 9106's own example
needs four lanes, a secret and associated data, which the `hash` of a password does not take, so
the binding takes all of them and `Argon2id.derive` exposes them; `Argon2id.hash` is `derive` with
one lane and neither.

## The module

`Lanes/Lib/Crypto/Sodium.lean` became `Lanes/Lib/Crypto/Native.lean`, the bound cryptography,
named for what it is rather than for whose it is. Every declaration keeps its name and type.
`Lanes.Lib.Crypto.Sodium` stayed for a while as a module that imported `Native`, for code that
imported it; it was removed before 0.1.0 (#107).
