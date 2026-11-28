# D45. Everything is proved; the checker finds bugs, a proof is the evidence

Status: Partly superseded by D110-volatile-actors.md (the generated inventory of every public definition)

Lanes is for software that an agent writes and nobody reads line by line. That works only if
what the agent ships carries its own evidence, and the only evidence that does not need a person
to weigh it is a proof the Lean kernel checks. So the rule is no longer "library and protocol
code is proved, application code is model-checked": every definition Lanes ships, and every
application built in `examples/`, is proved against a spec, or binds something outside Lean that
is named in `TRUSTED.md`, or is IO that only performs and is named there too.

The model checker keeps its place before a proof (rule 5.1): it finds the bug, the missing
premise and the wrong spec in seconds, where a proof attempt would take an hour to fail. A
complete PASS is still a theorem about an instance, but it is no longer what a claim rests on.

Three things follow.

- **Proving an application has to be cheap.** The key-value store's refinement took about 300
  lines, most of them a relation and its cases that every request-and-reply service repeats; the
  ledger's refinement is checked on instances and not proved. A library for the usual simulation
  relations, a cheaper invariant rule and a counterexample-to-induction finder come before new
  features, and the ledger's refinement, proved with them, is the measure.
- **What is proved is stated by the code, not by prose.** A generated inventory gives every
  public definition one status: proved (with the theorem), checked, tested, trusted (bound or
  IO, with its row in `TRUSTED.md`), or none. Library code has no "none"; CI keeps the inventory
  current, and it is the page a reader checks a claim against.
- **The specs are the part a person reads.** A theorem says the code meets its spec, not that the
  spec says what was meant. Specs are kept short and in one place per system, each with its
  premises (links that do not duplicate, a gate that does not crash, the disk model) written
  next to it, and they are reviewed by a person before a claim is made in public. Where a
  standard or a reference implementation exists (an RFC, Go's standard library), the proved code
  is also tested against it on generated inputs, so that a spec that misreads the standard shows
  up as a disagreement.
