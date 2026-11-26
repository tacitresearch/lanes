| Actor API | `Actor`, `Signature`, `Effect`, `System`, `EnvModel`; `actor_invariant` tactic; `System.join` (two systems wired into one), `System.filterMapIO` (other inputs and outputs, some outputs hidden) and `System.mapIO` (the same, none hidden) | `Lanes/Actors/{Actor,System,Join}.lean` |

- `System.join` leaves the inputs it wires open to the outside until `mapIO` or `filterMapIO`
  hides them, and keeps the outputs it wires in its signature though none is put out;
  `Http.fronted` hides both. The hand-built `gated` is still what `serve` runs and what the
  liveness theorem is about: there is no theorem yet that a fair run of a join, seen from one
  side, is a fair run of that side.
