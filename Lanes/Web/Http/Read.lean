/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Core.System
public import Lanes.Web.Http.Basic

/-!
A request answered from the state of one actor, without entering the system: a proposal
(`docs/decisions/new-reads.md`), off unless an application names its reads. The server peeks at
the actor's state as the shard has it once everything before is written out and handed over
(`Batch.chain_peek`), and answers with `answer` of it; nothing is journalled
(`Batch.run_erase_peeks`).
-/

@[expose] public section

namespace Lanes.Http

variable {σ : Signature}

/-- Which actor a request reads, and the response made from that actor's state. -/
structure Read (sys : System σ) where
  actor : σ.Id
  answer : sys.State actor → Response

end Lanes.Http
