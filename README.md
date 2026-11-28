# Lean on Lanes

Lanes is a runtime and library for building software in Lean 4. Programs are actors whose
logic is a pure step function. The runtime runs them, and the same step functions are
model-checked and proved against a spec. The library has what applications need: encodings,
cryptography, time, HTTP, PostgreSQL, storage, and models of outside services.

> Status: early beta. What is missing is under [Status](#status).

## A system in three parts

From `examples/bank` (`Bank.lean`, and the check from `Check.lean`):

```lean
-- 1. Logic is a pure step function: state and message in, state and effects out.
def account (opening : Nat) (self : A) : (sig A).Actor self Account where
  init := { balance := opening }
  step s
    | .transfer req dst amount =>
      if (amount : Int) ≤ s.balance then
        ({ balance := s.balance - amount },
          [.send dst (.credit amount), .emit ⟨req, .accepted⟩])
      else (s, [.emit ⟨req, .insufficient⟩])
    | .credit amount => ({ balance := s.balance + amount }, [])
    | .query req => (s, [.emit ⟨req, .balance s.balance⟩])
  recover s := (s, [])

-- 2. Prove what one actor guarantees; it lifts to every system, under every fault model.
theorem balance_nonneg (opening : Nat) (env : EnvModel (sig A)) (a : A) :
    (bank A opening).Invariant env fun c => 0 ≤ (c.state a).balance :=
  System.invariant_of_actor (bank A opening) a (Account.balance_nonneg opening a) env

-- 3. Check a property of the whole system on a small instance, here with lossy links.
#eval (Check.system (bank (Fin 2) 2) { env := lossy, driver := .anyOrder transfers }
  [.always "money is conserved" fun w => conserved w.state]).renderSystem
```

The checker finds the credit a lossy link drops:

```
FAIL: "money is conserved" is violated after 4 steps
  1. input transfer { req := 1, src := 0, dst := 1, amount := 1 }
  2. start 0
  3. deliver outside → 0: transfer 1 1 1
  4. drop 0 → 1: credit 1
```

## What is proved, checked, tested and trusted

Every claim, with its theorem, check or test, its premises and its status, is in
`docs/ARCHITECTURE.md`, area by area, with the limits of each. In short:

- **Proved** (Lean theorems, each with an axiom gate in `Tests/Axioms/`): every run of the
  runtime's scheduler, its actors free on worker threads, is a run of the semantics (the threads
  are trusted to perform its transitions), and so is every run of the one-threaded kernel that
  the tests and `Http.Loopback` run; a complete PASS of the model checker means the property
  holds in every reachable state of the instance; the HTTP gate
  answers no request more often than it arrived and, in a fair run in which it does not crash,
  answers every request it admits; a sign-in accepts no state more often than it was issued, and
  an ID token only when signed for an allowed algorithm with every claim passing; and the
  parsers, routes, HTML rendering and tokens of
  `docs/ARCHITECTURE.md`. Each has premises, which it gives.
- **Checked**: model checks of the examples on small instances, and of what the proofs do not
  yet cover, such as that a request reaches the gate.
- **Tested**: servers stopped with requests in flight, the parsers and encoders against
  reference implementations (Go's standard library, `expfmt`, botocore, jwcrypto), the models of
  S3, its multipart uploads, SES, SQS and PostgreSQL against runs recorded from moto and
  PostgreSQL (`oracles/README.md`), the bound C against its Lean references.
- **Trusted**: the trusted code, listed with each file's size in `TRUSTED.md`: the
  IO shells, the HTTP wire format where its proof does not reach, the C that binds OpenSSL's
  hashes, comparison and Argon2id, `fsync`, a timed wait, OpenSSL's TLS client, its signature check and its signing, the sign-in's IO, the AWS service's IO, and the template macro, with the assumptions the runtime makes. `lake exe lanes stats` prints the total. `lanes lint` fails if a trusted file changes without the
  list, and `scripts/mutants.py` holds known ways of breaking that code, each of which must
  fail a test.

## Examples

`examples/README.md` says what each example shows and in what order to read them. The
flagship is `examples/rookery`, a small social network for people and bots, kept in PostgreSQL:
each request is one pure transaction, and its claims are proved per transaction, so they hold in
every database the store's model allows. To run it, from the clone:

```bash
cd examples/rookery
lake build && lake test
../../scripts/with-postgres lake test                          # and over HTTP on PostgreSQL
PGHOST=... PGUSER=... lake exe rookery 8080 rookery.secrets    # serves http://127.0.0.1:8080
```

An application is a stateless process: actor state lives as long as the process, and what must
outlive it, or that several instances must agree on, lives in PostgreSQL
(`docs/ARCHITECTURE.md`, "The model"; `docs/DEPLOY.md`).

## Performance

Hello world over HTTP/1.1 with keep-alive, requests a second, on a c7a.16xlarge, at commit
70d61f52d0aa, 2026-11-27:

| Server | 1 connection | 16 | 64 | CPU |
| --- | ---: | ---: | ---: | --- |
| Go `net/http` | 29,870 | 125,809 | 137,938 | up to 12.8 cores |
| Lanes | 11,395 | 34,516 | 37,098 | 3.2 cores, 85–101 µs a request |

Lanes is about 4× behind Go at 64 connections at that commit. The benchmark's application is one
actor, and the runtime then ran its steps on one thread, so its logic used one core; actors have
since run free on worker threads (`docs/decisions/D116-free-running.md`), and this table was
measured before that. The method and settings are in `bench/README.md`.

## Quick start

You need [elan](https://github.com/leanprover/elan), which installs Lean and Lake, and a C
compiler; to run an app, PostgreSQL. The cryptography and TLS come from the OpenSSL in Lean's
toolchain, so there is no library to install:

```bash
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh
sudo apt-get install build-essential   # Debian, Ubuntu
xcode-select --install                 # macOS
```

```bash
git clone https://github.com/tacitresearch/lanes
cd lanes
lake exe lanes new my-app --dir ../my-app   # builds the `lanes` command, under a minute
cd ../my-app
lake test            # builds Lanes and the app (minutes, once), runs the model check and the proofs
PGHOST=localhost PGUSER=postgres lake exe my-app   # serves http://127.0.0.1:8080
```

`docs/TUTORIAL.md` then takes the app through a change, a model check and a proof, in fifteen
minutes.
`docs/TUTORIAL-WEB.md` then builds a web app on it: sign-in with an OpenID Connect provider,
uploads to S3 under a size limit, a test of the whole site against the test kit's fakes, a
property checked and proved, and what running it needs.

The app gets Lanes from GitHub, not from the clone, which it does not need once the app is
made. Its `lakefile.toml` requires the release tag the clone is at, or else the clone's commit
(Lanes has no release yet), so a later `lake update` does not move it; `--rev` names another.
Any Lake project can depend on Lanes the same way:

```toml
[[require]]
name = "lanes"
git = "https://github.com/tacitresearch/lanes"
rev = "<a release tag or a commit>"
```

The generated app is a counter kept in PostgreSQL: a typed table and its migration, one pure
transaction per request behind an actor that keeps nothing, its invariant proved per
transaction, a model check beside the store's model with vacuity witnesses, and a
server-rendered page. It runs its migrations at the start and refuses to start on tables other
than the declared ones.

## Status

Early beta: the API will change. What is missing and can be fixed is in the issues labelled
`known-limit`; the limits the design accepts are in `docs/ARCHITECTURE.md`, with each area.

`CONTRIBUTING.md` says how a change is made, `AGENTS.md` has the rules, `SECURITY.md` how to
report a vulnerability (a theorem that states less than the docs claim is one), and
`CHANGELOG.md` what each release changed. `docs/ARCHITECTURE.md` says how the pieces fit, what
is claimed of each and on what evidence, `docs/ROADMAP.md` where the direction and the work
are, and `docs/decisions/` why each piece is the way it is. The API reference, every module and declaration of `import Lanes` and
`import Lanes.Proofs` with its docstring, is built with doc-gen4 by `docs/api/`
(`docs/api/README.md`).

To build Lanes itself:

```bash
lake build
lake test            # the tests
lake exe lanesCheck  # the larger model checks
lake exe lanes lint
```

`AGENTS.md` ("Build and checks") says what each runs and how long it takes.

## License

Apache 2.0. See `LICENSE`.
