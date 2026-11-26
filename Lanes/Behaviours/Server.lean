/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Actors.Service

/-!
# The `Server` behaviour: request and reply

The simplest way to build a service: write its `Service` spec, a pure function from a state and
a request to a new state and responses, and run that function as one actor. The spec is the
implementation. `Server.system` adds the mailbox; `Lanes.Semantics.Service` proves that the
result refines the spec, so concurrent clients see exactly the sequential behaviour written
down.

A server owns its state alone (rule 3.6: one message, one atomic transition). Use it whenever
the state fits in one actor; move to several actors and a protocol only when it does not.
-/

@[expose] public section

namespace Lanes.Server

abbrev sig (In Out : Type) [DecidableEq In] [DecidableEq Out] : Signature where
  Id := Unit
  Msg _ := In
  In := In
  Out := Out

variable {In Out S : Type} [DecidableEq In] [DecidableEq Out]

/-- Its state is durable. -/
def actor (svc : Service (sig In Out) S) : (sig In Out).Actor () S where
  init := svc.init
  step s x := ((svc.step s x).1, (svc.step s x).2.map .emit)
  recover s := (s, [])

abbrev system (svc : Service (sig In Out) S) : System (sig In Out) where
  State _ := S
  actor _ := actor svc
  accept x := ⟨(), x⟩

end Lanes.Server
