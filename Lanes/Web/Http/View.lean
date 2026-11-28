/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Runtime.Peek
public import Lanes.Web.Http.Admit

/-!
Reads answered from the state (`docs/decisions/new-reads-from-state.md`). A request that changes
nothing is declared by a `View` beside the bridge: the actors it reads, and its response from
their states. The server answers it from a peek (`Runtime.tryPeek`): it never enters the
system, so it takes no step and changes nothing the actors do. Each actor it names is read
between two of its steps; the states of different actors are not read at one moment
(`docs/decisions/new-free-running.md`).

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

/-- How a request that changes nothing is answered from the state: the actors it reads, those
of every actor started that `every` holds of, and its response from their states. An actor
`every` holds of that is not among them was never started: it has its initial state
(`Peek.init_of_not_others`). -/
structure View (sys : System σ) where
  reads : List σ.Id
  every : σ.Id → Bool := fun _ => false
  answer : ((i : σ.Id) → i ∈ reads → sys.State i) → List ((i : σ.Id) × sys.State i) → Response

variable {sys : System σ}

/-- The response to a view from the states a peek read. -/
def View.respond (v : View sys) (peek : Peek sys v.reads) : Response :=
  v.answer peek.get peek.others

/-- A view answered from a peek of a kernel is its answer from that kernel's states. -/
theorem View.respond_of [Hashable σ.Id] (v : View sys) (k : Kernel sys) :
    v.respond (Peek.of k v.reads v.every)
      = v.answer (fun i _ => (k.cell i).state) (Peek.of k v.reads v.every).others := by
  simp only [View.respond]
  congr
  funext i h
  exact Peek.get_of k v.reads v.every i h

/-- The states of the actors of `sys` among those of the shard behind the server. -/
def unfront {α : Type} {S : α ⊕ σ.Id → Type} (others : List ((i : α ⊕ σ.Id) × S i)) :
    List ((i : σ.Id) × S (.inr i)) :=
  others.filterMap fun
    | ⟨.inr i, s⟩ => some ⟨i, s⟩
    | ⟨.inl _, _⟩ => none

/-- What `every` holds of, for the actors of `sys` behind the server. -/
def frontEvery {α : Type} (every : σ.Id → Bool) : α ⊕ σ.Id → Bool
  | .inr i => every i
  | .inl _ => false

/-- A view of `sys` as the shard behind the server's front reads it. -/
def View.fronted {bridge : Bridge σ} (v : View sys) : View (admittedFronted sys bridge) where
  reads := v.reads.map .inr
  every := frontEvery v.every
  answer get others := v.answer (fun i h => get (.inr i) (List.mem_map_of_mem h)) (unfront others)

def View.admitted {bridge : Bridge σ} (v : View sys) : View (admitted sys bridge) where
  reads := v.reads.map .inr
  every := frontEvery v.every
  answer get others := v.answer (fun i h => get (.inr i) (List.mem_map_of_mem h)) (unfront others)

/-- A view of `sys` behind the front answers from a kernel of the shard as it does from the
states of `sys`'s actors in it. -/
theorem View.fronted_respond [Hashable σ.Id] {bridge : Bridge σ} (v : View sys)
    (k : Kernel (Http.admittedFronted sys bridge)) :
    (v.fronted (bridge := bridge)).respond (Peek.of k (v.reads.map .inr) (frontEvery v.every))
      = v.answer (fun i _ => (k.cell (.inr i)).state)
          (unfront (Peek.of k (v.reads.map .inr) (frontEvery v.every)).others) :=
  View.respond_of v.fronted k

theorem View.admitted_respond [Hashable σ.Id] {bridge : Bridge σ} (v : View sys)
    (k : Kernel (Http.admitted sys bridge)) :
    (v.admitted (bridge := bridge)).respond (Peek.of k (v.reads.map .inr) (frontEvery v.every))
      = v.answer (fun i _ => (k.cell (.inr i)).state)
          (unfront (Peek.of k (v.reads.map .inr) (frontEvery v.every)).others) :=
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
