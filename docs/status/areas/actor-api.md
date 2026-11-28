### Actor API

Where: `Lanes/Core/{Actor,System,Join}.lean`.

- The `actor_invariant` tactic.
- `Actor`, `Signature`, `Effect`, `System`, `EnvModel`.
- `System.join` (two systems wired into one), `System.filterMapIO` (other inputs and outputs, some outputs hidden) and `System.mapIO` (the same, none hidden).

Known limits:

- `System.join` leaves the inputs it wires open to the outside until `mapIO` or `filterMapIO` hides them, and keeps the outputs it wires in its signature though none is put out; `Http.fronted` hides both. A fair run of a join is a fair run of each side (`System.Run.Fair.left`, `System.Run.Fair.right`).
