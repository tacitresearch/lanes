# Lean on Lanes

**Proved logic, contained concurrency.**

Lanes is a framework for building verified software in Lean 4. Every actor runs in its own lane,
nothing shares state, and the runtime merges traffic only at the edges. The same step function
runs in production, in the simulator, in the model checker and in the proofs.

> Status: early. The actor core, the semantics, the deterministic scheduler and the model
> checker work today. See `docs/DESIGN.md` for the full plan and `docs/DECISIONS.md` for what
> has been settled.

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

## Build

```bash
lake exe cache get
lake build
lake test
```

## Documents

- `docs/DESIGN.md`: what Lanes is and the build plan.
- `LANES_STYLE.md`: design and code rules, each with its reason.
- `docs/DECISIONS.md`: decisions taken during implementation.
- `AGENTS.md`: how to work in this repository.

## License

Apache 2.0. See `LICENSE`.
