# D112. Mathlib and CSLib in the proof layer, measured

Status: Accepted

The owner accepted (a) as part of the redesign (issue #239, D110), and the removal is done
(issue #111). The library uses no Mathlib or CSLib: `lakefile.lean` requires no package, and no
manifest of the repository lists either. An application may use them for its own proofs (#130),
from its proof files only (rule 1.6). `Lanes.Semantics.Lts`, `Lanes.Semantics.Seq`,
`Lanes.Semantics.Bag` and the sums of `Lanes.Semantics.Sums` replace what Lanes used, as the
branch `claude/no-mathlib` wrote them; the theorems keep their statements, but for those that
named a library type, now stated over the replacement: `Bag` for `Multiset` (`Service.Abs`,
`Account`, `Service.takes`), predicates for sets (`System.Run.WeakFair`, `Service.Once`,
`Once.Memo.Agrees`, `Check.Monitor.abs`), and `Enum.sum` over `[Enum α]` with values in `Int`
for `∑` over a `Fintype` in a commutative group (`Enum.sum_update`, `sum_map_erase`, the bank's
`money_conserved`). The toolchain stays a release candidate until a stable release of the same
or a newer version is installed and moved to in a change of its own (D99, section 3). The
sections below are the study as it was made, before the removal; `experiments/LibraryProofs/`
stays on the branch `claude/cslib-mathlib-study`.

This answers the owner's question on issue #111: Lanes' proofs are about state machines,
refinement, linearizability, liveness, lists and bytes; would they be shorter or simpler with
CSLib and Mathlib? It is research only. Nothing here changes what `lake build` builds. The
evidence is in `experiments/LibraryProofs/`, and each number below says which file measured it.

**The answer.** A little shorter, not simpler. The two libraries save Lanes about 1,100 lines
today, nearly all of them a library Lanes would otherwise own (multisets, transition systems,
infinite sequences, sums), and not proofs: the removal branch ported every proof off them at
the same length (section 4). Using them more widely saves little more: 82 lines in what was
measured (sections 2 and 3), against 163 that Lean core alone saves in the same places
(`grind`, core's `List` lemmas), which Lanes has either way. CSLib has the right vocabulary but almost none of
what Lanes proves: its theory is strong bisimulation and simulation with one label type, automata
and process calculi, while Lanes needs weak simulation along a label map, weak fairness of
events and refinement to a service (section 1). The recommendation is (a), remove them, as the
branch `claude/no-mathlib` does (section 6).

## How it was measured

| File | What it measures |
| --- | --- |
| `experiments/LibraryProofs/Usage.lean` | Every Mathlib, CSLib and Batteries constant that a declaration of `Lanes` uses in its type or proof, read from the built modules, by kind |
| `experiments/LibraryProofs/UsageRaft.lean`, `experiments/LibraryProofs/UsageLedger.lean` | The same for `examples/raft-kv` and `examples/ledger` |
| `experiments/LibraryProofs/Closure.lean` | The modules and `.olean` bytes that `import Lanes.Semantics` loads, by package |
| `experiments/LibraryProofs/survey.py` | Every theorem of `Lanes/` and `examples/`, stated again in a file that imports only Mathlib (or only `Std`), and given to `exact?` |
| `experiments/LibraryProofs/Quorum.lean`, `Ledger.lean`, `ListProofs.lean`, `RaftLog.lean`, `Refinement.lean`, `Blocks.lean` | Proofs of Lanes again, with Mathlib, CSLib or core; each states the same as the Lanes theorem it names |
| `experiments/LibraryProofs/proof_times.py` | The elaboration time of named proofs, from Lean's `trace.profiler`, best of three runs |

Line counts are of a declaration from its `theorem` line to the next blank line, without
comment lines, so a signature counts. The toolchain is the pinned `v4.37.0-rc1`, with CSLib at
`910210f` and Mathlib as CSLib pins it.

## 1. CSLib, area by area

CSLib (`.lake/packages/cslib`) is 53,187 lines in 323 files; the parts read for this are
13,784 of them (the semantics, distributed computing, sequences, logics, CCS, relations,
processes), and the rest was surveyed by its file names and headers. What Lanes uses of it
is the base of its semantics folder: `Usage.lean` finds 48 CSLib constants in Lanes, of which
16 theorems and 13 definitions, all from `LTS/Basic`, `LTS/HasTau`, `LTS/OmegaExecution`,
`OmegaSequence/Defs`, `OmegaSequence/Temporal`, `Nat/Segment` and the `Option` instance of
`HasTau` in `Automata/EpsilonNA/Basic`.

The import lines are in 5 files, which is where the earlier claim "Mathlib is used in only 5
files" came from (D99). That undercounts: `Usage.lean` finds library constants in 388
declarations of 17 of the 19 modules of `Lanes/Semantics/` (all but `Link` and `Sent`), since
the others import those 5. It also overcounts what Lanes needs, as the rest of this shows.

| CSLib | What it has | Lanes' counterpart | Verdict |
| --- | --- | --- | --- |
| `Foundations/Semantics/LTS/Basic`, `HasTau` | `LTS`, `MTr`, `CanReach`, traces; internal steps `τSTr`, saturated steps `STr`, `SMTr`, `saturate` and its idempotence (`saturate_tr_saturate_sTr`) | `Spec`, `Spec.Reachable`, `Refines`, `Refines.traces` (`Lanes/Semantics/Refinement.lean`) | Used today. The removal branch rewrote them in `Lanes/Semantics/Lts.lean`, 248 lines |
| `LTS/Simulation`, `TraceEq`, `MapHom` | `IsSimulation` with one label type on both sides, its composition (`IsSimulation.comp`), lifting along saturation (`IsSimulation.isSimulation_saturate_left`), `mono`, `sim_trace`; label maps that pull back (`LTS.mapLabel`) | `Refines impl spec f`: a weak forward simulation along a label map, with `Refines.trans` (41 lines, with its two private helpers `follow_τ`, `follow_sTr`) | `Refines` is exactly `IsSimulation impl.lts (spec.lts.saturate.mapLabel f)` (`refines_iff` in `Refinement.lean`, proved by `Iff.rfl`). `Refines.trans` from CSLib is 27 lines (section 3). CSLib's lemmas keep one label type, so the step that the pulled-back saturation is saturated already when `g` keeps `τ` (`collapse`, 9 lines) is still Lanes' |
| `LTS/Bisimulation` | Strong and weak bisimulation (`IsWeakBisimulation`, `IsSWBisimulation`), bisimilarity as a greatest fixed point, approximants, up-to techniques | None. Lanes proves one-way refinement only; no Lanes theorem is a bisimulation | Nothing to replace |
| `LTS/OmegaExecution`, `OmegaSequence/*` | `ωSequence`, `OmegaExecution`, `take`, `drop`, `flatten` with `cumLen`, `OmegaExecution.flatten_mTr` (an infinite run from finite runs one after another) | `System.Run` (`Lanes/Semantics/Liveness.lean`); `System.Run.ofBlocks`, `blockStart`, `blockOf` (`Lanes/Semantics/Projection.lean`, 75 lines) | `ofBlocks` and its four facts from `flatten_mTr` and `flatten_get_add` are 57 lines (`Blocks.lean`, section 3). `Run` is used as it is |
| `OmegaSequence/Temporal` | `Step`, `LeadsTo`, `leadsTo_trans`, `leadsTo_cases_or`, `until_frequently_leadsTo_and`, `until_frequently_not_leadsTo` | `System.LeadsTo`, `LeadsTo.trans` (uses `leadsTo_trans`), `LeadsTo.ensures_of_invariant` (WF1, 26 lines), `LeadsTo.induction` | The `until_frequently` rules need "infinitely often" (`Filter.Frequently`); Lanes' fairness gives "eventually taken" for each obligation (`System.Run.Fair`), so WF1 is not shorter through them. Only `leadsTo_trans` is reused, a one-line proof |
| `Data/Nat/Segment` | `Nat.segment` of a strictly increasing sequence, and its bounds | `blockOf` | Used today; it goes with `ofBlocks` above |
| `Computability/Distributed/Consistency` | Burckhardt's histories and abstract executions (`History`, `AbstractExecution` with `vis` and `ar`), `Linearizability`, `SequentialConsistency`, `CausalConsistency`, and that each implies the next (`linearizability_imp_sequentialConsistency` and the rest) | `Service.spec` and `System.Implements` (`Lanes/Semantics/Service.lean`): linearizability stated as refinement to an atomic service; `History.Explains` (`Lanes/Semantics/History.lean`); `cluster_implements` in `examples/raft-kv/RaftKVProofs/Refines.lean` | Definitions and the hierarchy only: no theorem takes a transition system to a linearizable history. Using it would add a proof (each history of a system that `Implements` its service satisfies `Linearizability`), not shorten one. It would give Raft's theorem a statement others recognise, which is worth noting for later |
| `Computability/Distributed/FLP` | The FLP impossibility, with its own processes, messages, stuttering LTS and a fair scheduler of processes (`FLP/FairScheduler`) | `System.Run.Fair`, `Lanes/Semantics/FairRuns.lean` (every finite run extends to a fair run) | The fairness there is of processes in that algorithm, not of events. Nothing to reuse |
| `LTS/Total`, `Divergence`, `Termination`, `Union`, `Reverse`, `FLTS` | Total LTSs and their ω-executions (`Total.omegaExecution_exists`), divergence, termination, products | `Spec.stutter` makes every Lanes run total, by stuttering | No Lanes theorem matches |
| `Languages/CCS`, `StatefulProcesses`, `Mech/Choreography`, `Logics/HML`, `Logics/Modal`, `Automata/*`, `Languages/OmegaRegularLanguage`, `SafetyLiveness` | CCS and its bisimulation theory, networks of stateful processes, choreographies, Hennessy–Milner logic, finite and Büchi automata, ω-regular languages, the safety-liveness decomposition | Actors, joins, the model checker (`Lanes/Check/`) | Different formalisms; nothing Lanes proves is stated in them |
| `Foundations/Relation`, `Data/List/IsChainFromTo` | Confluence, termination, chains | None | Nothing to replace |

So CSLib could shorten two Lanes proofs, `Refines.trans` and `System.Run.ofBlocks`, by about
32 lines together, and could give a recognised statement of linearizability with new work.
The gate's liveness (`Lanes/Semantics/Front.lean`), the fairness of joins
(`Lanes/Semantics/FairJoin.lean`), `System.Implements` and Raft's refinement and once-only
proofs use no CSLib result beyond the base definitions above.

**Is CSLib mature enough?** It is young and moves fast. Its `lakefile.toml` says version
`0.1.0`, and it states no API stability. It tags one release per Lean toolchain, release
candidates included (`v4.34.1`, `v4.35.0-rc1` to `rc4`, `v4.35.0`, `v4.36.0-rc1`, `rc2`,
`v4.36.0`, `v4.37.0-rc1` between mid-September and late November 2026, by its releases page),
and it requires Mathlib at the same toolchain's tag. Its repository had 823 commits and 185 open
pull requests when read. The file Lanes leans on most, `LTS/HasTau.lean`, changed 10 times in
eight months, among them the split of `LTS/Basic` into several files, the arrival of `SMTr` and
`mapLabel`, and a rewrite of the saturation proofs. It is well governed: a steering committee
(Stanford, Amazon, Google DeepMind, the Lean FRO), a lead maintainer and area maintainers, one
of them for LTS, automata and distributed computing (`GOVERNANCE.md`). That makes it a good
dependency for a research project and a costly one for a framework that pins a toolchain for its
users.

## 2. Mathlib, core and Batteries against Lanes' lemma libraries

`survey.py` copied the statement of every theorem in `Lanes/` and `examples/` (3,797 of 3,840;
the rest have shapes it does not parse) into a file with the `variable` and `open` lines of its
section, and the import of one library only.

- **146 statements (4 %) elaborate with Mathlib alone**, and 145 with `Std` alone. Every other
  theorem names a definition of Lanes (a system, a codec, an actor's state), so no library can
  hold it. The 146 are the lemma libraries and their like: `Lanes/Proof/HashMap.lean` (25),
  `Lanes/Proof/List/` (47), `Lanes/Proof/ByteArray.lean` (9), `Lanes/Proof/Utf8.lean` (5), and
  60 more spread over the runtime, the standard library and the web layer. Raft's log lemmas
  name `Entry` and `termAt`, so they are not among them; section 3 tries them by hand.
- **`exact?` with core and `Std` closes 16** of them with one lemma, 53 lines in all. These are
  in Lean today, whatever Lanes decides: `List.takeWhile_append_of_pos`,
  `List.dropWhile_append_of_pos`, `List.erase_filter`, `String.toByteArray_inj`,
  `ByteArray.size_eq_zero_iff`, `List.intercalate_cons_cons_left`, and ten that are one core
  lemma applied (`ge_iff_le`, `Nat.add_zero`, `ByteArray.ext`, `List.mem_of_mem_erase`,
  `Option.mem_bind_iff`). Some are kept on purpose: `Lanes.mem_of_mem_erase` says in its
  docstring that it pins the `BEq` instance.
- **`exact?` with Mathlib closes 4 more**, 39 lines: `Lanes.find?_congr` (Mathlib's
  `List.find?_congr`), `Lanes.forall_mem_takeWhile` (`List.mem_takeWhile_imp`),
  `Lanes.eq_of_mem_of_nodup_map` (`List.inj_on_of_nodup_map`) and `isAlpha_toLower` in
  `Lanes/Web/Html/BasicSound.lean` (`Char.isAlpha_toLower_eq_isAlpha`). Five `HashMap` and
  kernel-timer statements ran out of heartbeats there and are counted as not found.
- **`grind` alone, with no hints, closes 17** of the 145 core statements, 92 lines, among them
  `mem_arm` in `Lanes/Runtime/KernelTimers.lean` (27 lines),
  `Lanes.getElem?_append_singleton` and `set_set_comm` in `Lanes/Proof/HashMap.lean`.

Together 32 declarations, 174 lines, could go; 39 of those lines need Mathlib. `exact?` finds
only a proof by one lemma, so this is a lower bound on what the libraries offer to these
statements, but not on the whole: a statement that names a Lanes definition can still have a
shorter proof through library lemmas, which is what section 3 samples.

## 3. Proofs again, with the libraries

Each row is a theorem of Lanes and the same statement proved again; lines as above, times from
`proof_times.py` (the proofs only; the time to load the imports is in section 5).

| Theorem | Lanes today | Again | Library used | Lines | Time |
| --- | --- | --- | --- | ---: | ---: |
| `Lanes.Quorum.majority_inter` | `Lanes/Data/Quorum.lean`, with the private induction `countP_add_countP_le` | `Quorum.lean` | Core: `List.length_eq_countP_add_countP`, `List.countP_mono_left`. Mathlib's `Finset.inter_nonempty_of_card_lt_card_add_card` needs a `Finset` of nodes, and Lanes counts a list | 18 → 10 | 542 → 43 ms |
| `Lanes.sum_map_set`, which is the ledger's conservation step (`Ledger.Book.transfer_sound` uses it twice) | `Lanes/Proof/List/Basic.lean` | `Ledger.lean` | Mathlib: `List.sum_set'` | 16 → 5 | 123 → 69 ms |
| The rest of `Ledger.Book.transfer_sound` | `examples/ledger/Ledger/Proofs/Book.lean` | (not redone) | None: it is about which accounts a transfer changes, by how much | — | — |
| `Lanes.countP_erase_add` | `Lanes/Proof/List/Erase.lean` | `ListProofs.lean` | Mathlib: `List.countP_erase` (7 lines); or core `grind` with one hint (3 lines) | 11 → 3 | 146 → 205 ms |
| `Lanes.exists_filterMap_erase` | `Lanes/Proof/List/Erase.lean` | `ListProofs.lean` | Core: the same induction, cases closed by `simp_all` and `grind` | 22 → 16 | 231 → 512 ms |
| Raft's log lemmas: `termAt_cons_succ`, `termAt_drop`, `termAt_append_left`, `termAt_of_prefix`, `Matching.drop`, `merge_of_prefix` | `examples/raft-kv/RaftKV/Proofs/Log.lean` | `RaftLog.lean` | Core `grind` for the three `termAt` lemmas; nothing in either library for `Matching` or `merge` | 34 → 28 | 275 → 823 ms |
| `Lanes.Refines.trans`, with `follow_τ` and `follow_sTr` | `Lanes/Semantics/Refinement.lean` | `Refinement.lean` | CSLib: `IsSimulation.comp`, `isSimulation_saturate_left`, `IsSimulation.mono`, `saturate_tr_saturate_sTr`, and `LTS.mapLabel` (copied as `pull`, 4 lines, because its module is not built here) | 41 → 27 | 43 → 147 ms |
| `System.Run.ofBlocks` and its four facts, with `blockStart` and `blockOf` | `Lanes/Semantics/Projection.lean` | `Blocks.lean` | CSLib: `LTS.OmegaExecution.flatten_mTr`, `ωSequence.flatten_get_add`, `flatten_take`, `cumLen` | 75 → 57 | 1,155 → 1,239 ms (without the step proof inside the definition `ofBlocks`, which the profiler does not name) |

In all, 217 lines become 146, a third less. Of the 71 lines saved, 43 need a library: 11 from
Mathlib (`sum_map_set`) and 32 from CSLib (`Refines.trans`, `ofBlocks`). The other 28 come
from Lean core. Elaboration time moves both ways: a proof by a library lemma is faster
(`majority_inter`, `sum_map_set`), one by `grind` or by CSLib's general lemmas slower, by tenths
of a second at most, which is small beside the 1.7 s that loading the libraries costs each file
(section 5). The times were taken on a busy machine, best of three, so only their order of size
means anything.

None of these proofs is *simpler* to read with the library. The CSLib versions trade a
direct induction for an argument through saturation and pulled-back label maps, which a reader
must know CSLib to follow.

## 4. What the removal cost

`origin/claude/no-mathlib` (four commits on `1620026`) ports everything off both libraries. In
its `.lean` files it adds 1,692 lines and removes 615, 1,077 more in all
(`git diff --numstat 1620026 origin/claude/no-mathlib -- '*.lean'`):

| Where | Lines | What |
| --- | ---: | --- |
| `Lanes/Semantics/Bag.lean` | +421 | Multisets as lists up to `List.Perm`, with Mathlib's names: 83 theorems |
| `Lanes/Semantics/Lts.lean` | +248 | CSLib's transition systems, internal and saturated steps, `ReflTransGen`, infinite runs: 17 theorems |
| `Lanes/Semantics/Seq.lean` | +198 | Infinite sequences, leads-to, `StrictMono`, `segment`, `le_induction`: 18 theorems |
| `Lanes/Semantics/Sums.lean` | +179, −34 | Sums over `Enum` in place of `Finset.univ`: a list without repeats (`nub`), `Enum.sum`, `sum_update` by an induction where Mathlib's was 9 lines |
| `examples/rookery/Rookery/Proofs/Runs.lean` | +83, −29 | `Nat.findGreatest` and its four lemmas, written again |
| `Lanes/Proof/List/Basic.lean` | +20 | `filter_singleton`, `filterMap_const_none`, `reverse_induction` |
| The other 43 `.lean` files | +543, −552 | Renames (`Multiset` to `Bag`, `ℕ` to `Nat`, sets to predicates) and `abel` (18 uses) to `ac_rfl` and `omega` |

So the proofs themselves did not grow: outside the new library files, the port is 9 lines
shorter. What the libraries save is the 1,086 lines of library and `findGreatest`, about one
sixth of `Lanes/Semantics/` (6,721 lines) and 1.5 % of `Lanes/` (72,553).

One thing got harder: sums over all actors are over `Enum`, which may list a value twice,
instead of `Fintype`, so `Enum.values` and a list without repeats (`nub`) appear in
`Lanes/Semantics/Sums.lean`, and the bank's conservation (`Tests/Fixtures/BankProofs.lean`,
`examples/bank/Bank/Proofs.lean`) is stated over `Enum.sum`. One thing got better: four axiom
gates in `Tests/Axioms/Semantics.lean` now see fewer axioms than they list
(`LeadsTo.trans`, `LeadsTo.induction` and `LeadsTo.exists_left` no longer depend on
`Quot.sound`, nor `Refines.traces` on `Classical.choice`); the branch left the gates as they
were, for the owner.

The branch builds: `lake build Lanes.Semantics Lanes.Proofs` in a clean copy of it (no
packages at all) took 2 min 52 s, 436 jobs. Of the files it changed, three have changed on main
since (`Lanes.lean`, `examples/ledger/Ledger/Proofs/Refines.lean`,
`examples/rookery/Rookery/Proofs/Runs.lean`), so bringing it up to date is small.

## 5. The costs on the other side

What keeping them costs, measured in this container:

- **What a proof file loads.** `import Lanes.Semantics` loads 4,497 modules (`Closure.lean`):
  1,476 of Mathlib (348 MB of `.olean`), 26 of CSLib (2 MB), and 288 of the packages that come
  with them (Aesop 132, Batteries 74, ImportGraph 38, Qq 14, ProofWidgets 13, Plausible 13,
  LeanSearchClient 4; about 49 MB). That is for 89 theorems and 52 definitions, types,
  constructors and recursors that Lanes' own declarations use, besides 105 instances and the
  `abel` and `norm_num` machinery (`Usage.lean`: 290 constants in all). The examples add little: `examples/raft-kv` uses 126 library constants,
  46 of them theorems, and `examples/ledger` 74, 22 of them theorems. Loading the imports of a
  proof file is slower too: `lake env lean` on a file that only imports `Lanes.Semantics`
  took 2.4 to 3.1 s at `1620026` and 0.7 to 1.1 s on the removal branch (five runs each), so
  about 1.7 s more for each proof file, each time it is checked or built. Even a file that
  imports only `Std` took 1.7 s against 0.6 s, because Lake reads the ten packages first.
- **Build time.** `lake build Lanes.Semantics Lanes.Proofs` from nothing, with Mathlib's
  prebuilt `.olean` files in place, took 3 min 1 s at `1620026`, against 2 min 52 s on the
  removal branch, which builds the replacement library besides (3 min 36 s on a first try).
  The machine was shared (load about 17 on 4 cores), so the two are the same within noise:
  most of the time is Lanes itself. Mathlib itself is never built
  (`lake exe cache get`); a fresh clone first downloads it.
- **Disk.** `.lake/packages` is 7.7 GB per checkout, 7.2 GB of it Mathlib. In this container
  every worktree links one copy; each CI runner, each contributor's clone and each application
  that requires Lanes has its own.
- **The toolchain lock.** `lean-toolchain` is `v4.37.0-rc1`, a release candidate, because the
  pinned CSLib commit is built with it, and CSLib requires Mathlib at that toolchain's tag
  (D10, `AGENTS.md`: "follows CSLib's"; upgrades go "CSLib first"). Lake builds a workspace with
  one Lean and one copy of each package, so every application of Lanes takes Lanes' Lean and
  Lanes' Mathlib, whether or not it proves anything (D11 left this open). CSLib moves to each
  new toolchain within days, release candidates included, so Lanes is pulled along.
- **Renames upstream.** Both libraries rename freely. Lanes already uses one renamed name,
  `Multiset.notMem_zero` (formerly `not_mem_zero`, renamed across Mathlib in 2025), and the CSLib
  file it leans on most, `LTS/HasTau.lean`, changed 10 times in eight months (section 1). An
  upgrade of either is work on Lanes' schedule that brings Lanes nothing.
- **Layering.** Rule 1.6 exists because an executable that imports the proof layer is 157 MB
  instead of 8 MB (D11), and because Mathlib's `<i` token breaks `<input>` in templates. Lint
  `layering` enforces it. Without the libraries, half of the rule goes (D99, section 3).

## 6. Recommendation

**(a): remove them**, by merging `claude/no-mathlib` once it is brought up to date with main.

The numbers, side by side:

| | Lines |
| --- | ---: |
| Saved today by the two libraries: the library the removal had to write (`Bag`, `Lts`, `Seq`, sums, `findGreatest`) | 1,086 |
| Proofs that grew when ported off them | −9 (they shrank) |
| Saved more by using them more widely, measured: the lemmas only Mathlib closes (section 2) and the re-proofs that need Mathlib or CSLib (section 3) | 82 (39 + 43) |
| Saved by Lean core alone, measured, in the same sample: `grind` and core lemmas | 163 (135 + 28) |

Against that: 4,497 modules and 400 MB of `.olean` loaded by every proof file, 7.7 GB per
checkout, a release-candidate toolchain chosen by a dependency, and upgrades on its schedule.
About a thousand lines of owned, small, stable library is the cheaper side. The proofs Lanes
writes are about its own definitions (3,651 of 3,797 statements name one), so a general library
can only ever supply their lemmas, and those are mostly in core already.

Why not the others:

- **(b) for the proof layer only, as a package of its own.** It keeps Mathlib out of an
  application that never proves anything. But proving is what Lanes is for (rule 5.8): every
  example and every application made by `lanes new` has proofs, so nearly every user would
  still pay. And the toolchain lock stays for everyone, because the packages of one repository
  share one Lean. D99 chose no separate proof package on the ground that Mathlib goes; keeping
  Mathlib would bring that split back for little.
- **(c) more widely.** The measured gain of wider use is 82 lines, less than core alone gives
  (163), and CSLib's theory is mostly not Lanes' (section 1).

What to keep from this study, whatever is decided:

- The lemmas core already has (16, section 2) and those `grind` closes (17) can go now; that
  needs neither library. `Lanes.Quorum.majority_inter` is 10 lines from core's
  `List.length_eq_countP_add_countP` and `List.countP_mono_left` instead of 18.
- In the replacement `Lanes.Semantics.Lts`, state `Refines` as a simulation into the pulled-back
  saturation, as `experiments/LibraryProofs/Refinement.lean` does, and give it `comp`,
  `mono` and lifting along saturation: `Refines.trans` then follows as there.
- The ω-sequence `flatten` with `cumLen` is worth porting with `Lanes.Semantics.Seq` if
  `System.Run.ofBlocks` is touched again (`experiments/LibraryProofs/Blocks.lean`).

When to look again: a proof that needs real mathematics (probability for a randomised protocol,
counting over finite sets beyond majorities, real numbers for clocks), or a CSLib theorem that
takes a transition system to a linearizable history or proves weak fairness of events. Then an
application, or a bridge package beside Lanes (D99, section 3), can require Mathlib at the
version paired with Lanes' toolchain.
