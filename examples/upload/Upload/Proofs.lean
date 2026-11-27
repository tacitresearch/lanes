import Lanes.Semantics
import Upload.Upload

/-!
Proofs that need the proof layer. Nothing executable imports this file.
-/

namespace Upload

open Lanes

/-- The running system implements the spec in any environment that loses, duplicates and
crashes nothing, which is what the runtime provides inside one process. -/
theorem implements (config : Config) (env : EnvModel sig) (henv : env.Faultless) :
    (system config).Implements env (service config) :=
  Server.implements (service config) env henv

/-- No more uploads are under way than the bound, in every reachable state of the system. -/
theorem system_uploads_le (config : Config) (env : EnvModel sig) :
    (system config).Invariant env fun c => (c.state () : State).length ≤ config.uploads_max :=
  System.invariant_of_actor (system config) () (uploads_le config) env

end Upload
