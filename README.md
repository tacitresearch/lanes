# Lean on Lanes

**Proved logic, contained concurrency.**

Lanes is a framework for building verified software in Lean 4. Every actor runs in its own lane,
nothing shares state, and the runtime merges traffic only at the edges. The same step function
runs in production, in the simulator, in the model checker and in the proofs.

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

## Views are Lean

```lean
def CounterView (response : Response) : Html :=
  <div id="counter">
    <p>{s!"Count: {response.value}"}</p>
    <button hx-post="/increment" hx-target="#counter" hx-swap="outerHTML">"Add one"</button>
  </div>
```

Templates are a Lean macro: no generate step, errors on the template line, text escaped by type.

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

- `docs/DESIGN.md`: what Lanes is and the build plan.
- `LANES_STYLE.md`: design and code rules, each with its reason.
- `docs/DECISIONS.md`: decisions taken during implementation.
- `TRUSTED.md`: everything that is trusted rather than proved.
- `AGENTS.md`: how to work in this repository.

## License

Apache 2.0. See `LICENSE`.
