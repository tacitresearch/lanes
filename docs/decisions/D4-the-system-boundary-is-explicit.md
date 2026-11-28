# D4. The system boundary is explicit: `In`, `Out`, `accept`

Status: Accepted

A signature declares external inputs `In` and outputs `Out`. `System.accept : In → (i : Id) × Msg i`
routes an input to an actor. Internal messages cannot be injected from outside.

Why: invariants of protocols do not survive forged internal messages, so "any message may
arrive" is the wrong open-system semantics. Inputs and outputs are also exactly the visible
labels for refinement to a service spec.
