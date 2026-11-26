/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Actors.System
public import Lanes.Http.Basic
public import Lanes.Actors.Outside

/-!
The gate is the HTTP adapter's logic as an actor. It sits in front of a system: it parses each
request into an input, remembers which requests are waiting, and answers each one with the
system's response or with `504` when its deadline passes. `gated sys` is the system with the
gate added, so the model checker and proofs see the adapter's decisions and the application
together. What is left in IO is reading and writing sockets.

`Lanes.Http.GateSound` proves, for every system behind the gate, that an arrival is answered at
most once and that a waiting request keeps its deadline armed. `Lanes.Semantics.GateLive` proves
that a request the gate has admitted is answered, in every fair run in which the gate does not
crash. That an arrival reaches the gate, and so that every arrival is answered exactly once, is
model-checked in `Tests/Gate.lean`, not proved.
-/

@[expose] public section

namespace Lanes.Http

variable {σ : Signature}

abbrev ReqId := Nat

structure Bridge (σ : Signature) where
  /-- Parse a request into an input, or answer it directly without entering the system. The
  identifier must travel with the input so the matching output can name it. -/
  decode : ReqId → Request → Except Response σ.In
  /-- The request an output answers, or `none` for an output that is not an HTTP response. -/
  encode : σ.Out → Option (ReqId × Response)

structure GateConfig where
  requestTimeout_ms : Nat := 30000
  /-- Requests waiting for the system at once. Beyond it a request gets `503` (rule 2.6). -/
  maxPending : Nat := 1024

inductive GateMsg (σ : Signature) where
  | arrive (id : ReqId) (request : Request)
  | answer (out : σ.Out)
  | expire (id : ReqId)
  deriving DecidableEq

instance [Hashable σ.Out] : Hashable (GateMsg σ) where
  hash
    | .arrive id request => mixHash 1 (mixHash (hash id) (hash request))
    | .answer out => mixHash 2 (hash out)
    | .expire id => mixHash 3 (hash id)

instance [Repr σ.Out] : Repr (GateMsg σ) where
  reprPrec m _ :=
    match m with
    | .arrive id request => f!"arrive {id} {repr request}"
    | .answer out => f!"answer {repr out}"
    | .expire id => f!"expire {id}"

/-- The actors of a gated system: the gate (`none`) and the system's own. -/
abbrev GatedMsg (σ : Signature) : Option σ.Id → Type
  | none => GateMsg σ
  | some i => σ.Msg i

instance : ∀ i, DecidableEq (GatedMsg σ i)
  | none => inferInstanceAs (DecidableEq (GateMsg σ))
  | some i => inferInstanceAs (DecidableEq (σ.Msg i))

abbrev gatedSig (σ : Signature) : Signature where
  Id := Option σ.Id
  Msg := GatedMsg σ
  In := ReqId × Request
  Out := ReqId × Response

/-- An effect of an inner actor, in the gated system. Its outputs go to the gate. -/
def liftEffect {i : σ.Id} : Effect σ i → Effect (gatedSig σ) (some i)
  | .send to msg => .send (some to) msg
  | .emit out => .send none (.answer out)
  | .after delay_ms msg => .after delay_ms msg
  | .cancel msg => .cancel msg
  | .stop => .stop

def busy : Response := .text "the system is busy\n" 503

def timedOut : Response := .text "the system did not answer in time\n" 504

/-- The gate's state is the requests waiting for the system. -/
def gate (sys : System σ) (bridge : Bridge σ) (config : GateConfig) :
    (gatedSig σ).Actor none (List ReqId) where
  init := []
  step pending
    | .arrive id request =>
      if id ∈ pending then (pending, [])
      else if pending.length ≥ config.maxPending then (pending, [.emit (id, busy)])
      else
        match bridge.decode id request with
        | .error response => (pending, [.emit (id, response)])
        | .ok x =>
          (id :: pending,
            [.send (some (sys.accept x).1) (sys.accept x).2,
             .after config.requestTimeout_ms (.expire id)])
    | .answer out =>
      match bridge.encode out with
      | some (id, response) =>
        if id ∈ pending then (pending.erase id, [.cancel (.expire id), .emit (id, response)])
        else (pending, [])
      | none => (pending, [])
    | .expire id =>
      if id ∈ pending then (pending.erase id, [.emit (id, timedOut)]) else (pending, [])
  recover pending := (pending, pending.map fun id => .after config.requestTimeout_ms (.expire id))

/-- The gate never holds more than `maxPending` requests, and never the same one twice. -/
theorem gate_bounded (sys : System σ) (bridge : Bridge σ) (config : GateConfig) :
    (gate sys bridge config).Invariant fun pending =>
      pending.length ≤ config.maxPending ∧ pending.Nodup := by
  apply Actor.Inductive.invariant
  refine ⟨by simp [gate], ?_, fun _ h => h⟩
  intro pending msg ⟨hlen, hnodup⟩
  cases msg with
  | arrive id request =>
    simp only [gate]
    split
    · exact ⟨hlen, hnodup⟩
    · next hnew =>
      split
      · exact ⟨hlen, hnodup⟩
      · next hroom =>
        split
        · exact ⟨hlen, hnodup⟩
        · exact ⟨by simp only [List.length_cons]; omega, List.nodup_cons.mpr ⟨hnew, hnodup⟩⟩
  | answer out =>
    simp only [gate]
    split
    · split
      · exact ⟨Nat.le_trans (List.length_erase_le ..) hlen, hnodup.erase _⟩
      · exact ⟨hlen, hnodup⟩
    · exact ⟨hlen, hnodup⟩
  | expire id =>
    simp only [gate]
    split
    · exact ⟨Nat.le_trans (List.length_erase_le ..) hlen, hnodup.erase _⟩
    · exact ⟨hlen, hnodup⟩

/-- `sys` with the gate in front of it. -/
abbrev gated (sys : System σ) (bridge : Bridge σ) (config : GateConfig := {}) :
    System (gatedSig σ) where
  State
    | none => List ReqId
    | some i => sys.State i
  actor
    | none => gate sys bridge config
    | some i => (sys.actor i).mapEff fun eff => [liftEffect eff]
  accept x := ⟨none, .arrive x.1 x.2⟩
  boot := none :: sys.boot.map some

/-- What the gate assumes of whoever sends it requests: an id is used once. The gate's
at-most-once guarantee is stated for exactly these runs (`answered_nodup`), and the server
adapter is tested to stay within them. -/
def outside (σ : Signature) : Outside (gatedSig σ) (List ReqId) where
  init := []
  allow used x := if x.1 ∈ used then none else some (x.1 :: used)

end Lanes.Http
