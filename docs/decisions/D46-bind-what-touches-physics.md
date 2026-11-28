# D46. Bind what touches physics

Status: Partly superseded by D95-one-crypto-library.md (libsodium)

Write in Lean what decides: protocols, parsers, state machines, formats, each proved. Bind what
depends on what Lean cannot express or check, as every other language does: how long code takes
(a timing side channel), hand-tuned assembly, the operating system. A binding keeps a pure Lean
version beside it as the reference it is tested against, and a pure binding has that reference as
its body, so the theorems are about the reference and what is trusted is one sentence: the C
computes the same. The C is `native/lanes.c`, declared in `Lanes/Lib/Crypto/Sodium.lean` and
`Lanes/Durable/IO/Journal.lean`, all of it counted in `TRUSTED.md`.

**fsync.** Lean's `IO` has `flush` and no `fsync`, so a journal survived the death of the process
and not a loss of power, while the disk model (`Lanes/Durable/Disk.lean`) assumes each write done
before the next begins. Now it is, on the disk as well: an append is flushed and synced; a file
that replaces another is written beside it, synced, renamed, and its directory synced; the
directory is synced when a journal is opened, which may have made it. A loss of power then leaves
what a death at the same moment would, which the theorems already cover. Measured on ext4 on a
virtual disk, a shard given one input per batch took 190 µs a batch without the sync and 375 µs
with it; 20,000 inputs sent at once took 26 µs an input either way, because a batch is one append
and one sync. Durability is the default and there is no switch: rule 2.6 asks for a bound, and a
cost that amortises over a batch does not force one. That the journal calls `fsync` no test can
see, so its removal is not a mutant.

**libsodium.** Lean's compiler promises nothing about time, so the Lean comparison of two tags
could branch on where they differ, and so could SHA-256 on a key. SHA-256, HMAC-SHA-256, the
comparison (`sodium_memcmp`), secure random bytes and Argon2id (`crypto_pwhash`, with its passes
and memory in the type `Argon2id`) come from libsodium. The Lean SHA-256, HMAC and comparison
stay as references; `Tests/Crypto.lean` runs the published vectors on both and compares them on
thousands of random inputs of every length around a block. Passwords are hashed with Argon2id,
not PBKDF2, which nothing needs any more and is gone. Argon2id has no Lean reference. It is a
pure function, because the digest of a log-in has to be computed where a request arrives, off the
shard, by a bridge's `prepare : Request → Request`; it ends the process when its memory cannot be
had, as Lean does on any allocation.

**A system library, not vendored.** libsodium is packaged by every distribution, which audits and
updates it; vendoring it would put some 30,000 lines of C in this repository's trusted count and
its upkeep. Python's `hashlib` links the system's OpenSSL the same way. It is linked statically,
as `libsodium.a` found through `pkg-config`: Lean's toolchain links against a C library of its
own, against which the system's `libsodium.so` does not link, and a static binary also runs where
libsodium is not installed. The shim is compiled by the system's C compiler with the system's
headers, because the toolchain's compiler has none. `lakefile.toml` became `lakefile.lean`, since
TOML cannot declare a target that compiles C; the object and the library are `moreLinkObjs` of the
`Lanes` library, so every executable that imports a Lanes module links them, in packages that
require Lanes too, with no change to their Lake files (their manifests name the new file).
