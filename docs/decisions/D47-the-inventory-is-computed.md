# D47. The inventory is computed from the built library

D45 asks that every public definition Lanes ships have one status, stated by the code and
generated. `lake exe lanes inventory` writes it to
`docs/INVENTORY.md`; `lanes lint` fails when that file is stale and when a definition of
`Lanes/` has no evidence and is not on `docs/inventory-none.md`.

The program (`LanesCli/Inventory.lean`, the executable `lanesInventory`) loads the built modules
of `Lanes`, `Lanes.Semantics`, `LanesCli`, `Tests` and `Examples` with `Lean`'s `importModules`
and reads their declarations: no list of definitions or of evidence is kept by hand. It links
`Lean`; `lanes` does not, and starts it with `lake exe`, which builds those libraries first
(`needs` in `lakefile.toml`), so the inventory is never read from stale `.olean` files.

**What is listed.** Every definition, abbreviation, instance and `opaque` of a module of `Lanes`
or `LanesCli` that is not private. Not listed, because Lean or a command writes them and they
state nothing: declarations without a source position (constructors' indices, `noConfusion`
and the like), projections, matchers, what `deriving` writes (its position is in the `deriving`
clause), parsers and categories that `syntax` and `declare_syntax_cat` write, `macro_rules` and
`elab_rules` (they have no name; a file of them is trusted when `TRUSTED.md` names it), and
types: an `inductive`, a `structure`, a `class`, a definition whose value is a type. A type
states no behaviour; what is proved is proved of the functions over it.

**Statuses**, the first that applies:

1. **spec**: a predicate (its type ends in `Prop`), or a definition used only to state things:
   a theorem or a predicate uses it, and nothing that runs does, a test included.
   `Kernel.abs`, the map from a kernel to the system state it stands for, is one.
2. **proved**: a headline theorem states it. A headline theorem is one with an axiom gate in
   `Tests/Axioms/` (rule 5.5). The gate is the mark: it exists already, costs nothing new, and
   says that the theorem depends on no `sorry` and no axiom of ours. A theorem states the
   definitions in its statement, what their values run in their own module, through
   definitions of that module, and anything the value of a spec in it uses:
   `Kernel.exec_reachable` names `Kernel.exec`, which runs `Kernel.apply`, which runs
   `Kernel.input`, `advance` and `batch` and their helpers in `Kernel.lean`; the inventory
   gives those as proved *through* `Kernel.apply`. A definition whose value carries its spec
   is proved by its type: a `Decidable`, a `Codec`, a `Codable` or an `Enum`, whose laws are
   fields.
3. **trusted**: its file is a row of `TRUSTED.md`, and nothing above applies; the row is the
   evidence.
4. **checked**: a model check uses it. A check is a declaration of `Tests/` that uses a
   function whose value is a `Check.Report` or a `Check.FuzzReport`.
5. **tested**: a declaration of `Tests/` uses it.
6. **none**.

A test or a check uses what it names, through the declarations of `Tests/` and `Examples/` it
names, and what those run in their own module, as for a theorem.

*Why a gate and not every theorem.* A lemma that is not gated does not make a definition
proved. That is the line between a spec and a property: `Sha256.size_hash` says a digest has 32
bytes, which is true and is not what SHA-256 is; it is not gated, and the hash is tested.
Gating a theorem is the claim that it states what its definitions are for, and a reviewer reads
that claim in one line of `Tests/Axioms/`. Which theorem is a spec is the one judgement the
inventory needs, and it is the one already kept.

*Why its own module.* A module hides its helpers behind its entry points (rule 1.3); what is
stated of the entry points is what the helpers are for, and the inventory says which entry
point carries each. A definition of another module is not covered by being called: it is that
module's entry point, and it has statements of its own or it has none.

*Amendment: abbreviations of predicates, and theorems' matchers.* A predicate abbreviation in a
statement (an `abbrev` whose value is a `Prop`) is read as its body, in whatever module it is, and
so are such abbreviations in that body: `System.ImplementsOnce sys env svc key` is `sys.Refines env
(svc.once key)` to Lean at reducible transparency, the statement written shorter, not an entry point
of its module; `System.Refines` is one too, through which refinement theorems state `System.sem`.
Predicates defined with `def` (`Lanes.Refines`, `System.Invariant`, `System.LeadsTo`) are not read
through, and neither is an `abbrev` of a value: a system is an `abbrev` so that instance search sees
its state, and reading systems through would call `Actor.mapEff`, `shardEffect` and `System.shard`
proved by being called. Following every predicate's value would credit what the semantics' own
predicates run, `Effect.isStop` among them, to theorems about systems. Separately, the definitions
Lean writes for a theorem's proof (its matchers, filed under the theorem's name or a private copy of
it) are part of the proof: they neither run nor state, and no longer stop what a proof matches on
from being a spec. They are what left `Service.once` and `Service.Once.take` with status none: the
two are specs, as are definitions it gave as proved, `EnvModel.lossy` and `Http.findL` among them.
`Tests/Inventory.lean` checks both rules on facts written by hand.

*Alternatives.* An attribute `@[proves f]` on theorems says what a gate says, with more
ceremony, with code in the library to define it, and without checking axioms. Counting every
theorem whose statement mentions a definition is computed too, but calls SHA-256 proved by its
length. Crediting everything a statement or a test reaches calls the whole checker tested by
any test that runs it. A table of definitions and their evidence is the prose the decision
rules out.

**The list of definitions without evidence** is `docs/inventory-none.md`. It began as the
truth on the day the inventory was introduced and only shrinks: `lanes lint` fails on a
definition of `Lanes/` with status none that is not on it, on an entry that is no longer none
or no longer exists, and on an entry under no `##` heading, the heading being the reason it is
there. `LanesCli/` is listed in the inventory but not held to this: it is a tool, not shipped
with an application.
