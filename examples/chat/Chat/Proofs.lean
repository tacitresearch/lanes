import Lanes.Semantics
import Chat.Chat

/-!
Proofs that need the proof layer. Nothing executable imports this file.
-/

namespace Chat

open Lanes

/-- The running system implements the spec in any environment that loses, duplicates and
crashes nothing, which is what the runtime provides inside one process. -/
theorem implements (config : Config) (env : EnvModel sig) (henv : env.Faultless) :
    (system config).Implements env (service config) :=
  Server.implements (service config) env henv

/-- The room stays within its bound and holds each member once, in every reachable state. -/
theorem system_bounded (config : Config) (env : EnvModel sig) :
    (system config).Invariant env fun c => Bounded config (c.state () : State) :=
  System.invariant_of_actor (system config) () (bounded config) env

end Chat
