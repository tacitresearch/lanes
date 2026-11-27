import Lanes.Semantics
import Counter.Counter

/-!
Proofs that need the proof layer (CSLib, Mathlib). Nothing executable imports this file, so the
application binary stays small.
-/

namespace Counter

open Lanes

/--
The running system implements the spec: whatever concurrent clients observe is a behaviour of
`service` with each request taking effect at one instant. It holds in any environment that
loses, duplicates and crashes nothing, which is what the runtime provides inside one process.
-/
theorem implements (config : Config) (env : EnvModel sig) (henv : env.Faultless) :
    (system config).Implements env (service config) :=
  Server.implements (service config) env henv

end Counter
