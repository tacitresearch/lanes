# D104. Honest results: a bounded pass exits 2, each failure has a kind, a binding is proved of its reference

Status: Accepted

Issue #102. Four things a result said less plainly than it should.

**A bounded pass is not a pass.** `Check.Report.ok` was true for any search that found no
failure, so a check that hit `maxStates` or `maxDepth` exited 0 like one that explored its whole
instance, and the template's `lake test` passed. Now `Report.verdict` is `complete`, `bounded` or
`failed`; `Report.ok` is a complete pass (`Report.ok_iff`: no failure, complete, not
fingerprinted), which is what `Check.search_sound` and `Check.system_sound_of_respects` cover;
`Report.passed` is the old meaning, for a check that is bounded on purpose and says so in its
name ("to depth 12"). A fingerprinted pass is bounded: states whose hash collides are not
explored. The checker prints `PASS (complete)` or `PASS (bounded)`, and `Verdict.exitCode` is 0,
1 for a failure and 2 for a bounded pass. *Why 2 and not 0 with a warning:* CI and agents read
exit codes, not text, and a pass that covered part of the instance is exactly what they must not
take for a full one.

**Each failure has a kind.** `Lanes.Testing.report` (`Lanes/Testing/Run.lean`) is the runner of
the template's `lake test`, of Lanes' own `lanesTest` and `lanesCheck`, and of the examples'
check programs: named results, each of kind `build`, `proof`, `check` or `test`, printed as text
or, with `--json`, as one JSON object. `lanes check --json` passes `--json` to the test driver,
and gives a failure of kind `build` when the driver did not build; `lanes lint --json` gives
each finding with its kind, `proof` for a `sorry`. *Why a kind:* an agent that reads "failed"
must otherwise parse text to know whether to fix the code, the proof or the spec.

**Proofs do not stop the checks, and `lake test` builds them.** The template kept its theorems
in the module that `Check.lean` and `Main.lean` import, so a broken proof stopped the checks
(rule 5.1 the wrong way round), and `lake test` built only what the checks import, so a `sorry`
in the proofs passed it. Now every theorem is in `App/Proofs.lean`, which nothing executable
imports, and the check program runs the checks first and then `lake build --wfail App.Proofs`
(`Testing.build`): a `sorry`, a warning, fails it as a result of kind `proof`.

**A binding is proved of its reference.** A function bound to C with `@[extern]` keeps its Lean
reference as its body (rule 2.7), so a theorem about it is a theorem about the reference, and
that the C computes the same is trusted (`Tests/Crypto.lean` compares them). D47 called such a
function trusted, by its file's row of `TRUSTED.md`, even when a headline theorem states it. A
new status says both: **proved of its reference, C trusted**, for an `@[extern]` definition with
a Lean body that would otherwise be proved. `Bytes.same` is one (`Bytes.same_iff`, now gated in
`Tests/Axioms/Lib.lean`). `Sha256.hash` stays trusted: its only theorem gives the digest's size,
which D47 does not count as what SHA-256 is.
