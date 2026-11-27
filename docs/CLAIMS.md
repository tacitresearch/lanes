# Claims

Every claim the front-door documents make, with its evidence, its premises and its status. It is
for review: a claim that is not here, or whose evidence does not say what its sentence says, is a
defect (`SECURITY.md` treats a theorem that states less than its docs claim as one).

Status:

- **proved**: a theorem, checked by Lean, with an axiom gate (`Tests/Axioms/`, or the example's
  `Proofs/Axioms.lean`) that stops compiling if a `sorry` or a new axiom reaches it;
- **checked**: a model check on a small instance, or a check of `lanes lint`;
- **tested**: a test run by `lake test`, a CI job or by hand, as the row says;
- **trusted**: listed in `TRUSTED.md`, with how it is checked;
- **not proved**: stated here so that nobody reads it into another row.

The documents are `README.md` (README), `docs/ARCHITECTURE.md` (ARCH), `docs/STATUS.md` and its
fragments (STATUS), `TRUSTED.md` (TRUSTED), `examples/README.md` (EX) and the READMEs of
`examples/rookery`, `examples/ledger` and `examples/raft-kv`.

## The framework

| Claim | Where | Evidence | Premises | Status |
| --- | --- | --- | --- | --- |
| The step function that runs is the one the checker explores and the proofs are about | README, ARCH | One semantics, `SysState.step` (`Lanes/Core/World.lean`); `Check.system` runs actors through it (`Lanes/Check/System.lean`); the kernel is proved against it (`Kernel.exec_reachable`) | The shell is trusted to run the kernel as written | proved for the kernel; the rest by construction |
| A per-actor invariant holds in every reachable state of every system, under every fault model | README, ARCH | `System.invariant_of_actor`, `Lanes/Proof/Lift.lean`; gate `Tests/Axioms/Proof.lean` | None | proved |
| The kernel stays in a state the semantics reaches, and its events are a run reaching it, for any sequence of operations, inputs and clock readings | README, ARCH, TRUSTED | `Kernel.exec_reachable`, `Kernel.exec_outputs`, `Lanes/Runtime/KernelSound.lean`; gate `Tests/Axioms/Runtime.lean` | The shell hands inputs and outputs on unchanged (TRUSTED, "Assumptions the runtime makes") | proved |
| The journal describes the kernel; an output is handed over only after its entries are appended | ARCH, TRUSTED | `Batch.run_kernel`, `Batch.run_sound`, `Lanes/Runtime/Batch.lean`; gate `Tests/Axioms/Runtime.lean` | The shell performs the acts in order (`Lanes/Runtime/IO/Shell.lean`) | proved; the shell trusted |
| A journal cut at any byte opens and gives the entries written before the cut; other damage is refused | README, ARCH | `Journal.open?_cut`, `Lanes/Durable/Journal.lean`; gate `Tests/Axioms/Durable.lean` | A checksum makes a damaged entry unlikely, not impossible, to pass (TRUSTED) | proved |
| Recovery rebuilds the kernel the journal describes; a snapshot gives what a full replay gives | README, ARCH | `Journal.recover_kernel`, `Journal.resume_eq_recover`; gate `Tests/Axioms/Durable.lean` | None | proved |
| A process that dies anywhere in an append or a save leaves files that load as the kernel it had | ARCH, STATUS | `Journal.Disk.Holds.append_crash`, `Journal.Disk.Holds.save_crash`, `Journal.Disk.Torn.mend`, `Lanes/Durable/Disk.lean`; gate `Tests/Axioms/Durable.lean`; a child killed with SIGKILL while it works, `Tests/Durable.lean` | The file system behaves as the model: flushed bytes stay, a torn append leaves a prefix, a rename is atomic | proved over a model; the model trusted; tested |
| Every journal append is synced before the next, so a loss of power leaves what a death would | README, ARCH | `Lanes/Durable/IO/Journal.lean` (`append` flushes and calls `fsync`, `native/lanes.c`) | `fsync` and the disk do what they promise | trusted |
| The bank, killed with `kill -9` and started again, has the balance it had | README, EX | Run by hand on 2026-11-27: account 2 answers `142` after a transfer of 42 and a restart (`examples/bank-web`) | One process, one shard | tested by hand |
| A complete PASS of the checker means each `always` property holds in every reachable state of the instance | README, ARCH | `Check.search_sound`, `Check.system_sound_of_respects`; gate `Tests/Axioms/Check.lean` | `==` on actor states is equality and on the driver an equivalence, with a matching hash; only the instance checked, within its bounds | proved |
| A reported violation is a real run | ARCH | `Check.system_violated`; gate `Tests/Axioms/Check.lean` | None | proved |
| A complete PASS of a refinement check means every run's inputs and outputs are a trace of the spec | ARCH | `Check.refines_sound`, `Check.refines_traces`, `Lanes/Semantics/MonitorSound.lean`; gate `Tests/Axioms/Semantics.lean` | `==` on the spec's state is equality; the instance only | proved |
| Under lossy links the checker finds the credit the bank loses | README | `examples/bank/Check.lean` ("lossy links"), run by `lake test`; the trace in `README.md` reproduced on 2026-11-27 | None | checked |
| History variables (ghosts) erase: an invariant proved with them holds without them | README, ARCH | `System.Invariant.of_ghost`, `Lanes/Proof/Ghost.lean`; gate `Tests/Axioms/Proof.lean` | None | proved |
| Invariants about states and messages take five cases, not eight, and hold under loss, duplication, reordering and crashes | README, ARCH | `System.Inductive.of_monotone`, `System.Monotone.and_net`, `Lanes/Proof/Monotone.lean`; gate `Tests/Axioms/Proof.lean` | None | proved |
| Any number of shards joined behave as the one system | README, ARCH, STATUS | `System.SplitReachable.merged`, `System.ShardsReachable.unsharded`; gate `Tests/Axioms/Runtime.lean` | Well-routed runs, booting under `System.SteadyBoot`, states up to `SysState.Equiv` | proved |
| Processes joined by TCP implement `System.shards` | ARCH | None | | trusted |
| The transport's decisions: one write at a time, only what it was sent, in order, at most once, a bounded queue | ARCH, STATUS, TRUSTED | `Peers.Courier.written_sublist_sent` and the others of `Lanes/Net/CourierSound.lean`; gate `Tests/Axioms/Net.lean` | The IO of `Lanes/Net/IO/Peers.lean` performs what the courier says | proved; the IO trusted |
| No request is answered more often than it arrived | README, ARCH, STATUS, TRUSTED | `Http.served_answered_le_arrived`, `Http.kernel_served_answered_le_arrived`, `Lanes/Web/Http/FrontSound.lean`; gate `Tests/Axioms/Web.lean` | The link from outside to the gate does not duplicate (the kernel's does not); "no id answered twice" also needs distinct ids (`Http.served_answered_nodup`), which the server takes from `Http.Waiting` (trusted) | proved |
| A waiting request keeps its deadline armed | README, ARCH | `Http.served_deadlines_armed`; gate `Tests/Axioms/Web.lean` | None | proved |
| Every request the gate admits is answered, by the system or with `504` | README, ARCH, TRUSTED | `Http.served_pending_answered`, `Lanes/Semantics/Front.lean`; gate `Tests/Axioms/Semantics.lean` | A fair run (that the runtime's runs are fair is assumed, TRUSTED "Progress"), and the gate does not crash | proved |
| An arrival reaches the gate, so each request is answered exactly once | STATUS, TRUSTED | `Tests/Gate.lean`, two requests | | checked, not proved |
| The HTTP client reads a response written as a server writes it, stays within its limit and ends | README, ARCH | `Response.read_wire`, `Response.read_more`, `Lanes/Web/Http/WireSound.lean`; gate `Tests/Axioms/Web.lean` | Responses of the forms `Response.wire` writes; other forms are tested only | proved |
| Each server connection writes responses in the order requests were read, each once, within its bounds | ARCH, STATUS, TRUSTED | `Http.Conn.run_writes` and the others of `Lanes/Web/Http/ConnSound.lean`; gate `Tests/Axioms/Web.lean` | The IO of `Lanes/Web/IO/Server.lean` performs what `Conn.step` says | proved; the IO trusted |
| A link printed from a route is matched by that route's handler | README, ARCH | `Http.dispatch_link`, `Lanes/Web/Http/RouteSound.lean`; gate `Tests/Axioms/Web.lean` | Links printed from routes; a link written by hand is not covered | proved |
| Rendered HTML is read by a browser as the tree it was rendered from, so text stays text | README, ARCH | `Html.lex_render`, `Lanes/Web/Html/BasicSound.lean`; gate `Tests/Axioms/Web.lean` | Against a model of the tokenizer's data and double-quoted-attribute states (STATUS, Web limits) | proved |
| The template macro produces the element the template shows | README | `Tests/Html.lean` | | trusted, tested |
| A codec reads back what it writes | README | The law is a field of `Codec` (`Lanes/Data/Codec.lean`), so every codec, those `lanes_data` derives among them, carries its proof | None | proved (by its type) |
| `Server.system spec` implements its spec | README, ARCH | `Server.implements`, `Lanes/Semantics/Service.lean`; gate `Tests/Axioms/Semantics.lean` | An environment that loses, duplicates and crashes nothing (`EnvModel.Faultless`) | proved |
| A request named by its client takes effect at most once, under every fault | ARCH | `KV.implements_once` (`examples/kv-cache`), `RaftKV.implementsMachine_once`; gates in their examples | The memo (`Once.actor`, `Machine.once`) is in the system | proved |
| `System.Implements` is linearizability | ARCH | Its definition: weak simulation to `Service.spec` (`Lanes/Semantics/Service.lean`, D42) | | a definition; not proved equal to Herlihy and Wing's |
| Jobs: no key answered more often than submitted; every job answered in a fair run without crashes | ARCH | `Jobs.answered_le_handled`, `Jobs.submitted_answered`; gates `Tests/Axioms/Behaviours.lean`, `Tests/Axioms/Semantics.lean` | For the second: a fair run and no crashes | proved; the pool trusted |
| A request always sent under one idempotency key has its effect at most once, in every run a model of a service behind keys allows; each call is answered at most once; each event delivered at most `maxDeliveries` times | ARCH, STATUS | `Idempotent.at_most_once`, `Idempotent.keys_nodup`, `Effects.at_most_once`, `Rpc.answered_le_called`, `Events.deliveries_le`, `Lanes/Outside/`; gate `Tests/Axioms/Outside.lean` | Of the model: an effect counts from the moment its request is sent, whether or not it happened | proved |
| A real payment or email service does only what its model allows | ARCH, TRUSTED | The assumptions listed in `docs/decisions/D65-models-of-external-services.md`; recorded runs written by hand, `Tests/Outside.lean` | Keys that do not expire; webhooks within `maxDeliveries` | trusted; not tested against a real service |
| Every output of every run is one some actor's step or start emits | ARCH | `System.Emits.outputs`, `Lanes/Proof/Outputs.lean`; gate `Tests/Axioms/Proof.lean` | None | proved |
| Bound C computes what its Lean reference computes | ARCH, TRUSTED | `Tests/Crypto.lean` against the references and published vectors | That HMAC-SHA-256 is a pseudorandom function makes tokens unforgeable | trusted, tested |
| `Bytes.same a b` holds exactly when `a = b` | ARCH, TRUSTED | `Bytes.same_iff`, `Lanes/Lib/Crypto/Sodium.lean`; gate `examples/ledger/Ledger/Proofs/Axioms.lean` | Of the Lean reference; that the C computes the same is tested | proved of the reference; the C trusted |
| The number of trusted lines, and each trusted file's size | README, TRUSTED | Written by `lake exe lanes lint --fix`; lint `trusted-size` fails when a file differs | | checked |
| Each known way of breaking trusted code fails a test | README, TRUSTED | `scripts/mutants.py`, nightly (`.github/workflows/mutants.yml`) | A list of known mutants, not a measure of coverage | tested |
| Every public definition has a status and its evidence | README, ARCH | `docs/INVENTORY.md`, generated from the built modules; lint `inventory`, `inventory-none` | Those with none are on `docs/inventory-none.md` | checked |
| One shard takes about 1.8 million inputs a second from one sender; a message costs the same at 1,000 and 100,000 actors | STATUS | The scale benchmark in `lake exe lanesCheck` (`Tests/Scale.lean`) | A four-core machine; no journal | tested |
| HTTP: requests a second at 1, 16 and 64 connections against Go `net/http` | README, `bench/README.md` | `bench/run.sh` through the Bench workflow on a c7a.16xlarge, commit 70d61f52d0aa, 2026-11-27 | One set of runs; the report is the workflow's artifact, not in the repository | tested (measured) |

## The applications

| Claim | Where | Evidence | Premises | Status |
| --- | --- | --- | --- | --- |
| Bank: no balance is ever negative | README, STATUS | `Bank.balance_nonneg`, `examples/bank/Bank.lean`; gate `examples/bank/Bank/Proofs/Axioms.lean` | None | proved |
| Bank: money is conserved, for any number of accounts | STATUS | `Bank.money_conserved`, `examples/bank/Bank/Proofs.lean`; same gate | A faultless environment | proved |
| Key-value store: implements the map spec; with a read cache it does not | ARCH, STATUS | `KV.implements`, `KV.caching_not_implements`, `examples/kv-cache/KV/Proofs.lean`; gate `examples/kv-cache/KV/Proofs/Axioms.lean` | `KV.implements`: links that do not duplicate | proved |
| Election: at most one leader per term | STATUS | `Election.election_safety`, `examples/election/Election/Proofs.lean`; gate `examples/election/Election/Proofs/Axioms.lean` | `votesOncePerTerm` | proved |
| Watchdog: a fair run in which the dog never barks; an impatient run barks | STATUS | `Watchdog.exists_fair_run_never_barks`, `Watchdog.impatient_barks`; gate `examples/watchdog/Watchdog/Proofs/Axioms.lean` | None | proved |
| Payments: the shop charges each order at most once, in every run, under every fault the payment model allows | EX, STATUS | `Shop.charged_at_most_once`, `Shop.emits_keyed`, `examples/payments/Shop/Proofs.lean`; gate `examples/payments/Shop/Proofs/Axioms.lean` | Retries under the key (`keyedRetries`); the payment service behaves as `Payments.outside` (trusted, above); a charge counts from the moment it is sent | proved |
| Payments: a retry without the key charges an order twice | EX | `examples/payments/Check.lean`, run by its `lake test` | One order, one retry | checked |
| Payments: an order the shop calls paid has a payment that succeeded | EX | `examples/payments/Check.lean` | One order, one retry, one crash | checked, not proved |
| Counter (what `lanes new` writes): implements its spec | README | `Counter.implements`, `examples/counter/Counter/Proofs.lean` | A faultless environment | proved, no axiom gate |
| Raft: election safety, log matching, leader completeness, state machine safety, for every number of nodes and every fault | README, STATUS, EX, raft-kv | `RaftKV.election_safety`, `RaftKV.log_matching`, `RaftKV.leader_completeness`, `RaftKV.applied_agree_over_time` and the rest of `examples/raft-kv/RaftKV/Proofs/`; gate `examples/raft-kv/RaftKV/Proofs/Axioms.lean` | A finite set of nodes; a crash keeps what a node had; both protocol switches on for the second table | proved |
| Raft: the cluster is the one map to its clients (refinement, so linearizable as `System.Implements` defines it) | README, ARCH, STATUS, EX, raft-kv | `RaftKV.implementsMachine`, `examples/raft-kv/RaftKVProofs.lean` (gated there) | A request is not handed to a node twice by the link from its client | proved |
| Raft with the memo: each command takes effect at most once, with no premise on links | README, ARCH, STATUS, raft-kv | `RaftKV.implementsMachine_once`, same file | The machine behind `Machine.once`; `raftNode` runs the plain map, not this | proved |
| Raft: three processes killed with SIGKILL, two at a time, keep every acknowledged write | README, STATUS, raft-kv | `lake exe raftProcs`, a CI job | One machine | tested |
| Raft: a minute of random kills and pauses loses no acknowledged write | STATUS, raft-kv | `lake exe raftChaos`, by hand, one run with seed 7 | Not in CI | tested by hand |
| Raft: a request is eventually answered | | | | not proved: a cluster that answers nothing refines its spec too |
| Ledger: money conserved in each currency, no overdraft, paired entries, cached balances | STATUS, EX, ledger | `Ledger.book_invariant`, `examples/ledger/Ledger/Proofs/`; gate `examples/ledger/Ledger/Proofs/Axioms.lean` | None: every run and environment model | proved |
| Ledger: a user is shown only its own records; the ledger serves `n` only when `user n` asks; sessions and failed log-ins within bounds | STATUS, ledger | `Ledger.serve_onlyOf`, `Ledger.serve_from_owner`, `Ledger.user_bounded`; same gate | None | proved |
| Ledger, without timers: implements its spec | STATUS, ledger | `Ledger.implements`, `examples/ledger/Ledger/Proofs/Refines.lean`; same gate | Each user's link to the ledger is ordered and does not duplicate; no request is handed to a user twice | proved |
| Ledger, with timers: implements its spec with its deadlines | STATUS, ledger | `Ledger.implements_timed`, `examples/ledger/Ledger/Proofs/Timed.lean`; same gate | Each user's link to the ledger is ordered and neither loses nor duplicates; no request is handed to a user twice; the ledger does not crash (on one shard it restarts whole from its journal) | proved |
| Ledger: served over HTTP through SIGKILL and a restart | STATUS, EX, ledger | `lake exe ledgerLive`, a CI job | | tested |
| Ledger and rookery: the system behind the HTTP gate (`Http.served`) implements the spec | | Only the gate's own theorems (at most once, deadlines, answers) | | not proved |
| Rookery: posts never lost and deleted only by their author, a deleted post in no read, timelines exactly the newest posts followed, the rate limit, API changes acted on once per `seq`, no other account's secrets, every bound | EX, STATUS, rookery | `examples/rookery/Rookery/Proofs/` (`Board.run_keeps`, `Board.Gone.run`, `Board.timeline_complete`, `Board.rate_limit`, `Board.handle_api_again`, `Board.handle_secret`, `Board.Bounded.handle` and the rest); gate `examples/rookery/Rookery/Proofs/Axioms.lean` | Statements about the spec's functions (`Board.handle`, `Board.fire`) and every sequence of them, for every configuration | proved, of the spec |
| Rookery: the system implements its spec with deadlines | ARCH, STATUS, EX, rookery | `Rookery.implements`, `examples/rookery/Rookery/Proofs/Refines.lean`; same gate | The link from outside to the board does not duplicate; requests may be lost and reordered and the board may crash | proved |
| Rookery: the claims above hold of the running system's traces | | The theorem that composes them with `Rookery.implements` is not written | | not proved |
| Rookery: a request is made as the account its cookie or token verifies; no secret reaches the journal | rookery | `examples/rookery/Check.lean` (`bridge`), `lake exe rookeryLive` (CI) | HMAC is a pseudorandom function | tested |
| Every request to an application is answered | | Only the gate's: an admitted request is answered, at the latest with `504` | | not proved for the applications' own logic |
