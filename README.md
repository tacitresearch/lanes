# Lean on Lanes

Lanes is a framework for writing distributed and web software in Lean 4 and proving it
against a spec: each actor is a pure step function, actors share no state, and IO happens only
at the edges. The step function that runs in production is the one the model checker explores
and the proofs are about.

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

Every claim the documents make, with its theorem, check or test, its premises and its status,
is in `docs/CLAIMS.md`. In short:

- **Proved** (Lean theorems, each with an axiom gate in `Tests/Axioms/`): the runtime kernel
  follows the semantics whatever the shell asks of it; a journal cut at any byte recovers the
  state it describes; a complete PASS of the model checker means the property holds in every
  reachable state of the instance; any number of shards behave as one system; the HTTP gate
  answers no request more often than it arrived and, in a fair run in which it does not crash,
  answers every request it admits; and the parsers, routes, HTML rendering and tokens of
  `docs/ARCHITECTURE.md`. Each has premises, which `docs/CLAIMS.md` gives.
- **Checked**: model checks of the examples on small instances, and of what the proofs do not
  yet cover, such as that a request reaches the gate.
- **Tested**: processes killed with SIGKILL and started again, JSON, Base64, URLs, IP
  addresses, media types and dates against Go's standard library, the bound C against its Lean
  references.
- **Trusted**: About 2,450 lines of trusted code, listed with their sizes in `TRUSTED.md`: the
  IO shells, the HTTP wire format where its proof does not reach, the C that binds libsodium,
  `fsync` and a timed wait, and the template macro, with the assumptions the runtime makes. `lanes lint` fails if a trusted file changes without the
  list, and `scripts/mutants.py` holds known ways of breaking that code, each of which must
  fail a test.

`docs/INVENTORY.md`, generated from the built library, gives every public definition its
status, and `docs/inventory-none.md` lists those with no evidence yet.

## Examples

`examples/README.md` says what each example shows and in what order to read them. The
flagship is `examples/rookery`, a small social network for people and bots, whose claims are
proved of its spec and which is proved to implement that spec. To run it, from the clone:

```bash
lake exe cache get   # prebuilt Mathlib, once
cd examples/rookery && mkdir -p .lake && ln -s ../../../.lake/packages .lake/packages
lake build && lake test
lake exe rookery 8080 rookery.journal rookery.secrets   # serves http://127.0.0.1:8080
```

`examples/raft-kv` is a replicated key-value store proved to be one map to its clients where
the link from a client does not repeat a request, and `examples/ledger` a multi-user web ledger
with its safety proved.

## Performance

Hello world over HTTP/1.1 with keep-alive, requests a second, on a c7a.16xlarge, at commit
70d61f52d0aa, 2026-11-27:

| Server | 1 connection | 16 | 64 | CPU |
| --- | ---: | ---: | ---: | --- |
| Go `net/http` | 29,870 | 125,809 | 137,938 | up to 12.8 cores |
| Lanes | 11,395 | 34,516 | 37,098 | 3.2 cores, 85–101 µs a request |
| Lanes, journal synced before every answer | 344 | 2,393 | 8,632 | |

Lanes is about 4× behind Go at 64 connections today. The benchmark's application is one actor
on one shard, and a shard runs on one thread, so its logic uses one core. The IO path and running
actors in parallel are the next steps. The method and settings are in `bench/README.md`.

## Quick start

You need [elan](https://github.com/leanprover/elan), which installs Lean and Lake, a C
compiler, and libsodium, which Lanes links, with pkg-config to find it:

```bash
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh
sudo apt-get install build-essential libsodium-dev pkg-config   # Debian, Ubuntu
brew install libsodium pkg-config                               # macOS, with xcode-select --install
```

```bash
git clone https://github.com/tacitresearch/lanes
cd lanes
lake exe lanes new my-app --dir ../my-app   # builds the `lanes` command, under a minute
cd ../my-app
lake exe cache get   # prebuilt Mathlib, once per project: 500 MB to fetch, 7.5 GB on disk
lake test            # builds Lanes and the app (minutes, once), runs the model checks
lake exe my-app      # serves http://127.0.0.1:8080
```

`docs/TUTORIAL.md` then takes the app through a change, a model check and a proof, in fifteen
minutes.

The app gets Lanes from GitHub (`rev = "main"` in its `lakefile.toml`), not from the clone,
which it does not need once the app is made. Any Lake project can depend on Lanes the same way:

```toml
[[require]]
name = "lanes"
git = "https://github.com/tacitresearch/lanes"
rev = "main"
```

The generated app is a counter service: a spec-sized actor, its invariant proved in one line, a
model check with vacuity witnesses, and a server-rendered page.

## Status

Early beta: the API will change. What works, area by area, and its known limits are in
`docs/STATUS.md`. Not there yet:

- TLS, a database, server push, and observability beyond the server's metrics, health checks
  and access log;
- migrations of a journal across changed step functions;
- models of external systems other than an API with idempotency keys and webhooks (payments
  and email are modelled, `Lanes/Outside/Effects/`), such as a database, which
  `docs/decisions/D61-models-of-external-systems.md` describes, and adapters to real services;
- liveness of the applications, and, for rookery, the theorem that joins its claims with its
  refinement into statements about the running system; the HTTP gate is proved for answers,
  not as a refinement.

`CONTRIBUTING.md` says how a change is made, `AGENTS.md` has the rules and the layout,
`SECURITY.md` how to report a vulnerability (a theorem that states less than the docs claim is
one), and `CHANGELOG.md` what each release changed. `docs/ARCHITECTURE.md` says how the pieces fit
and where each is proved, `docs/ROADMAP.md` the direction, and `docs/decisions/` why each piece is
the way it is.

To build Lanes itself:

```bash
lake exe cache get   # prebuilt Mathlib, once
lake build
lake test            # a few seconds
lake exe lanesCheck  # the larger model checks, about 20 s
lake exe lanes lint
```

## License

Apache 2.0. See `LICENSE`.
