/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Runtime.Batch
public import Lanes.Web.Http.Admit

/-!
Reads answered from the state (`docs/decisions/new-reads-from-state.md`). A request that changes
nothing is declared by a `View` beside the bridge: the actors it reads, and its response from
their states. The server answers it from a peek at the end of a batch (`Runtime.tryPeek`): it
never enters the system, so it takes no entry in the journal and no step, and it reads the states
of every actor it names at one boundary between entries (`Batch.run_peeks`). Leaving the reads
out of the journal changes nothing else the shard does (`Batch.run_erase_peeks`).

A read waits for its peek behind a gate of its own, with its own bounds (`ServerConfig.reads`):
the gate's decisions (`Gate.step`) over `readSig`, where a read enters as its id and the peek's
answer is its response. So a read is answered once, at most `maxPending` wait at once, and one the
shard has not answered by its deadline is answered `504`, as a request the system has not
answered is. Whether a view answers what the request would if it entered the system is the
application's claim, proved of its views.
-/

@[expose] public section

namespace Lanes.Http

variable {σ : Signature}

/-- How a request that changes nothing is answered from the state: the actors it reads, and its
response from their states. -/
structure View (sys : System σ) where
  reads : List σ.Id
  answer : ((i : σ.Id) → i ∈ reads → sys.State i) → Response

variable {sys : System σ}

/-- The response to a view from the states a peek read. -/
def View.respond (v : View sys) (peek : Batch.Peek sys v.reads) : Response :=
  v.answer peek.get

/-- A view answered from a peek of a kernel is its answer from that kernel's states. -/
theorem View.respond_of [Hashable σ.Id] (v : View sys) (k : Kernel sys) :
    v.respond (Batch.Peek.of k v.reads) = v.answer fun i _ => (k.cell i).state := by
  simp only [View.respond]
  congr
  funext i h
  exact Batch.Peek.get_of k v.reads i h

/-- A view of `sys` as the shard behind the server's front reads it. -/
def View.fronted {bridge : Bridge σ} (v : View sys) : View (admittedFronted sys bridge) where
  reads := v.reads.map .inr
  answer get := v.answer fun i h => get (.inr i) (List.mem_map_of_mem h)

def View.admitted {bridge : Bridge σ} (v : View sys) : View (admitted sys bridge) where
  reads := v.reads.map .inr
  answer get := v.answer fun i h => get (.inr i) (List.mem_map_of_mem h)

/-- A view of `sys` behind the front answers from a kernel of the shard as it does from the
states of `sys`'s actors in it. -/
theorem View.fronted_respond [Hashable σ.Id] {bridge : Bridge σ} (v : View sys)
    (k : Kernel (Http.admittedFronted sys bridge)) :
    (v.fronted (bridge := bridge)).respond (Batch.Peek.of k (v.reads.map .inr))
      = v.answer fun i _ => (k.cell (.inr i)).state :=
  View.respond_of v.fronted k

theorem View.admitted_respond [Hashable σ.Id] {bridge : Bridge σ} (v : View sys)
    (k : Kernel (Http.admitted sys bridge)) :
    (v.admitted (bridge := bridge)).respond (Batch.Peek.of k (v.reads.map .inr))
      = v.answer fun i _ => (k.cell (.inr i)).state :=
  View.respond_of v.admitted k

/-- What the gate of reads sees: a read enters as its id, and the answer to it is its response. -/
abbrev readSig : Signature where
  Id := Empty
  Msg := Empty.elim
  In := ReqId
  Out := ReqId × Response
  decEqMsg := fun e => e.elim

def readBridge : Bridge readSig where
  decode id _ := .ok id
  encode := some

/-- The gate of reads decides on an arrival as the gate does on a request it admits. -/
theorem readBridge_arrive {E : Type} (config : GateConfig) (does : Gate.Effects readSig E)
    (pending : List ReqId) (id : ReqId) (request : Request) :
    Gate.step readBridge config does pending (.arrive id request)
      = Gate.admit config does pending id (.ok id) := rfl

/-- The gate of reads decides on a read's response as the gate does on an answer. -/
theorem readBridge_answer {E : Type} (does : Gate.Effects readSig E) (config : GateConfig)
    (pending : List ReqId) (answer : ReqId × Response) :
    Gate.step readBridge config does pending (.answer answer) = Gate.receive does pending answer :=
  Gate.step_answer_eq readBridge config does pending answer

end Lanes.Http
