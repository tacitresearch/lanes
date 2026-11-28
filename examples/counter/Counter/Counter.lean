import Lanes

/-!
# A counter service

The spec and the actor. This file is logic only: no IO (Lanes rule 2.4), and no theorems, so
that `Check.lean` and `Main.lean`, which import it, build while a proof is broken. The theorems
are in `Counter/Proofs.lean`.
-/

namespace Counter

open Lanes

/-- Identifies a client request, so its response can be matched to it. -/
abbrev ReqId := Nat

/-- Declared with `lanes_data`, whose `deriving` also takes `ToJson, FromJson`, with their
round-trip law, and whose `table` line maps a structure to rows of the typed store. -/
lanes_data inductive Request where
  | increment (req : ReqId)
  | read (req : ReqId)
  deriving DecidableEq, Repr, Hashable

lanes_data structure Response where
  req : ReqId
  value : Nat
  /-- Whether the request was applied. An increment at the limit is refused. -/
  applied : Bool
  deriving DecidableEq, Repr, Hashable

/-- Explicit configuration (rule 2.5). -/
structure Config where
  /-- The counter never exceeds this (rule 2.6: bounded everything). -/
  limit : Nat := 1000

abbrev sig : Signature := Server.sig Request Response

/--
The spec: what each request does, as if requests were handled one at a time. This is the part
to review. It is also the implementation, because the `Server` behaviour runs it as an actor.
-/
def service (config : Config) : Service sig.In sig.Out Nat where
  init := 0
  step count
    | .increment req =>
      if count < config.limit then (count + 1, [⟨req, count + 1, true⟩])
      else (count, [⟨req, count, false⟩])
    | .read req => (count, [⟨req, count, true⟩])

abbrev system (config : Config) : System sig :=
  Server.system (service config)

end Counter
