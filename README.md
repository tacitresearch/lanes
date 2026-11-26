# Lean on Lanes

**Proved logic, contained concurrency.**

Lanes is a framework for building verified software in Lean 4. Logic is a pure step function
per actor, nothing shares state, and IO happens only at the edges. The same step function runs
in production, in the simulator, in the model checker and in the proofs.

> Status: early. `docs/STATUS.md` lists what works today against the plan in `docs/DESIGN.md`;
> `docs/DECISIONS.md` records what has been settled.

## A system in three parts

```lean
-- 1. Logic is a pure step function: state and message in, state and effects out.
def account (opening : Nat) (self : A) : (sig A).Actor self Account where
  init := { balance := opening }
  step s
    | .transfer req dst amount =>
      if (amount : Int) ≤ s.balance then
        ({ balance := s.balance - amount }, [.send dst (.credit amount), .emit ⟨req, .accepted⟩])
      else (s, [.emit ⟨req, .insufficient⟩])
    | .credit amount => ({ balance := s.balance + amount }, [])
  recover s := (s, [])

-- 2. Prove what one actor guarantees; it lifts to every system, under every fault model.
theorem balance_nonneg (opening : Nat) (env : EnvModel (sig A)) (a : A) :
    (bank A opening).Invariant env fun c => 0 ≤ (c.state a).balance :=
  System.invariant_of_actor _ a (Account.balance_nonneg opening a) env

-- 3. Check system properties on a small instance before proving them.
#eval (Check.system (bank (Fin 2) 2) { driver := .anyOrder transfers }
  [.always "money is conserved" fun w => conserved w.state]).renderSystem
```

Under lossy links the checker answers in milliseconds with a shortest counterexample:

```
FAIL: "money is conserved" is violated after 4 steps
  1. input { req := 1, src := 0, dst := 1, amount := 1 }
  2. start 0
  3. deliver outside → 0: transfer 1 1 1
  4. drop 0 → 1: credit 1
```

## Start an application

```bash
lake exe lanes new my-app
cd my-app
lake exe cache get   # prebuilt Mathlib, once
lake test            # model checks
lake exe my-app      # serves http://127.0.0.1:8080
```

The generated app is a counter service: a spec-sized actor, its invariant proved in one line, a
model check with vacuity witnesses, and a server-rendered page.

Its types are declared with `lanes_data`, which writes the declaration and derives from the same
text a codec that carries its round-trip law, so the journal and its snapshots need no code of
their own:

```lean
lanes_data structure Response where
  req : ReqId
  value : Nat
  applied : Bool
  deriving DecidableEq, Repr, Hashable, Codable
```

`deriving Enum` lists the values of a finite type, such as the identities of a system's actors,
and `deriving LawfulBEq` compares a structure that holds a function field by field. `AGENTS.md`
says what is accepted.

## Views are Lean

```lean
open scoped Lanes.Html

namespace Routes
def count : Http.Route Unit := .get (.seg "count")
def increment : Http.Route Unit := .post (.seg "increment")
end Routes

def CounterView (response : Response) : Html :=
  <div id="counter">
    <p>{s!"Count: {response.value}"}</p>
    <button {Hx.request Routes.increment ()} {Hx.target "#counter"} {Hx.swap .outerHTML}>
      "Add one"
    </button>
  </div>
```

Templates are a Lean macro: no generate step, errors on the template line, text escaped by type.
A route is one value that prints links and matches requests, with a proof that the two agree, so
a view cannot link or post to a route that does not exist.

## What is proved, and what is trusted

- **The runtime's logic.** Every decision the runtime makes is a pure function, and whatever
  the IO loop around it does, the system stays in a state the semantics allows
  (`Kernel.exec_reachable`).
- **Durability.** A shard with a journal comes back after `kill -9` in the state its journal
  describes. Proved: the file format, that a file cut short by a crash opens and gives what
  was written before the cut, that anything else wrong with a file is refused, and that
  recovery rebuilds the kernel (`Journal.open?_cut`, `Journal.recover_kernel`). Because
  recovery is a replay through the same pure kernel, a restart is not a fault the proofs have
  to account for. Trusted: that the file holds what the shell wrote.
- **The model checker.** It lists exactly the enabled events, merging states is safe, a
  reported trace is real, and a complete PASS of the search means the property holds in every
  reachable state (`Check.search_sound`).
- **Proof tools.** Per-actor invariants lift to every system under every fault model. History
  variables cost nothing at run time (`Invariant.of_ghost`). Invariants about states and
  messages need five cases, not eight, and hold under loss, duplication, reordering and crashes
  (`Inductive.of_monotone`).
- **Several shards and processes.** Any number of shards joined behave as the one system
  (`System.SplitReachable.merged` for two, `System.ShardsReachable.unsharded` for `n`). A transport joins shards in different processes; what it
  decides is a pure function, run by the model checker against a network that fails.
- **The HTTP gate.** `Http.serve` runs the system with the gate joined in front of it, and the
  theorems are about that system, for every system and bridge: no request is answered more
  often than it arrived, a waiting request keeps its deadline armed, and in a fair run every
  request the gate admits is answered (`Http.served_answered_le_arrived`,
  `Http.served_deadlines_armed`, `Http.served_pending_answered`). A bridge's `prepare` runs
  before a request is journalled, so a password or a cookie need never reach the disk.
- **The HTTP client's wire format.** What the reader makes of a response written as a server
  writes it, and of every start of one, is proved, and so are its size limit and its ending
  (`Response.read_wire`, `Response.read_more`).
- **Trusted.** About 1,160 lines of IO and macro code and a 439-line HTTP wire format whose
  reading is proved for what a server's writer sends and only tested for other forms, listed with their sizes in `TRUSTED.md`; `lanes lint` fails if they
  grow, and `scripts/mutants.py` holds the known ways of breaking that code, each of which has
  to fail a test. It is a list, not a measure: a review found sixteen more, which are in it now,
  and `TRUSTED.md` says what it still does not check.

## Kill it and start it again

```bash
lake exe bankWeb 8080 bank.journal &
curl -X POST -d "src=0&dst=2&amount=42" http://127.0.0.1:8080/transfer
kill -9 %1
lake exe bankWeb 8080 bank.journal &
curl http://127.0.0.1:8080/accounts/2     # 142
```

The journal holds what the system was asked, not its state. Starting again replays it through
the same pure functions, so the system is back in the state the journal describes, and that
has a proof. From time to time the kernel is saved and the journal cut, so a restart replays
only what came after the last save; that this gives the same state has a proof too.

## A serious system built on it

`systems/raft-kv` is a replicated key-value store: Raft, as the step function of one actor.
It is checked against the map it replicates, and proved to be that one map to its clients,
for every number of nodes and every fault the model has: links that lose, repeat and reorder
messages, and nodes that crash and come back with what they had. It runs as three processes
that survive their leaders being killed, each saving its state and cutting its journal as it
goes. A node that comes back without its journal is outside the model, and does lose what was
acknowledged, so a node is not started without one unless it is told it is new:
`systems/raft-kv/README.md` says what else to know before running it.

```bash
cd systems/raft-kv && mkdir -p .lake && ln -s ../../../.lake/packages .lake/packages
lake build
lake exe raftProcs    # three processes over HTTP, killed with SIGKILL and started again
lake exe raftChaos    # a minute of writes while nodes are killed and paused at random
lake exe raftNode new 0 8800 node0.journal 7810 7811 7812   # one node; without `new` ever after
```

## Build Lanes itself

```bash
lake exe cache get
lake build
lake test
lake exe lanes lint
```

## A spec in five lines, checked without a refinement mapping

```lean
def spec : Service (sig K V F) (K → Option V) where
  init _ := none
  step store r :=
    match r.op with
    | .put key value => (fun k => if k = key then some value else store k, [⟨r.req, .ok⟩])
    | .get key => (store, [⟨r.req, .value (store key)⟩])
```

Monitor any system against it with `spec.monitored driver` and `Check.refines`. Give the front
ends of `Examples/KV.lean` a read cache and the checker reports the stale read:

```
FAIL: "every response is allowed by the map spec" is violated after 14 steps
  ...
  10. deliver front 1 → store: put 2 0 1
  11. output { req := 2, res := ok }
  12. input { req := 3, via := 0, op := get 0 }
  13. deliver outside → front 0: request { req := 3, via := 0, op := get 0 }
  14. output { req := 3, res := value none }
```

A service that fits in one actor needs no protocol at all: `Server.system spec` runs the spec
itself, and `Server.implements` proves it refines the spec for every interleaving.

## Documents

- `docs/STATUS.md`: what works today and what is next.
- `docs/ROADMAP.md`: the phases ahead and the open design questions.
- `docs/PLAN.md`: what is being done now and why.
- `docs/DESIGN.md`: what Lanes is and the build plan.
- `LANES_STYLE.md`: design and code rules, each with its reason.
- `docs/DECISIONS.md`: decisions taken during implementation.
- `TRUSTED.md`: everything that is trusted rather than proved.
- `AGENTS.md`: how to work in this repository.

## License

Apache 2.0. See `LICENSE`.
