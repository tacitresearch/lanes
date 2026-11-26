/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Actors.System
public import Lanes.Http.Basic
public import Lanes.Actors.Outside
public import Lanes.Actors.Snapshot

/-!
The gate is the HTTP adapter's logic as an actor. It sits in front of a system: it parses each
request into an input, remembers which requests are waiting, and answers each one with the
system's response or with `504` when its deadline passes. `gated sys` is the system with the
gate added, so the model checker and proofs see the adapter's decisions and the application
together. What is left in IO is reading and writing sockets.

The decisions are `Gate.step`, which does not know where the gate sits. `Lanes.Http.Front` has
the gate as a system of its own, joined in front of a system that keeps outputs and inputs of
its own; in `gated sys` every output of `sys` goes to the gate.

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

/-- The four things a gate does, as effects of the place where it sits. -/
structure Gate.Effects (σ : Signature) (E : Type) where
  respond : ReqId → Response → E
  forward : σ.In → E
  arm : ReqId → E
  disarm : ReqId → E

/-- The gate's decisions, the same wherever it sits: `pending` is the requests waiting for the
system. -/
def Gate.step {E : Type} (bridge : Bridge σ) (config : GateConfig) (does : Gate.Effects σ E)
    (pending : List ReqId) : GateMsg σ → List ReqId × List E
  | .arrive id request =>
    if id ∈ pending then (pending, [])
    else if pending.length ≥ config.maxPending then (pending, [does.respond id busy])
    else
      match bridge.decode id request with
      | .error response => (pending, [does.respond id response])
      | .ok x => (id :: pending, [does.forward x, does.arm id])
  | .answer out =>
    match bridge.encode out with
    | some (id, response) =>
      if id ∈ pending then (pending.erase id, [does.disarm id, does.respond id response])
      else (pending, [])
    | none => (pending, [])
  | .expire id =>
    if id ∈ pending then (pending.erase id, [does.respond id timedOut]) else (pending, [])

/-- A step keeps the waiting list within `maxPending` and free of repeats, wherever the gate
sits. -/
theorem Gate.step_bounded {E : Type} (bridge : Bridge σ) (config : GateConfig)
    (does : Gate.Effects σ E) {pending : List ReqId} (msg : GateMsg σ)
    (h : pending.length ≤ config.maxPending ∧ pending.Nodup) :
    (Gate.step bridge config does pending msg).1.length ≤ config.maxPending
      ∧ (Gate.step bridge config does pending msg).1.Nodup := by
  obtain ⟨hlen, hnodup⟩ := h
  cases msg with
  | arrive id request =>
    simp only [Gate.step]
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
    simp only [Gate.step]
    split
    · split
      · exact ⟨Nat.le_trans (List.length_erase_le ..) hlen, hnodup.erase _⟩
      · exact ⟨hlen, hnodup⟩
    · exact ⟨hlen, hnodup⟩
  | expire id =>
    simp only [Gate.step]
    split
    · exact ⟨Nat.le_trans (List.length_erase_le ..) hlen, hnodup.erase _⟩
    · exact ⟨hlen, hnodup⟩

/-- The gate in front of `sys`, as one of the actors of `gated sys`. -/
def gate (sys : System σ) (bridge : Bridge σ) (config : GateConfig) :
    (gatedSig σ).Actor none (List ReqId) where
  init := []
  step := Gate.step bridge config
    { respond := fun id response => .emit (id, response)
      forward := fun x => .send (some (sys.accept x).1) (sys.accept x).2
      arm := fun id => .after config.requestTimeout_ms (.expire id)
      disarm := fun id => .cancel (.expire id) }
  recover pending := (pending, pending.map fun id => .after config.requestTimeout_ms (.expire id))

/-- The gate never holds more than `maxPending` requests, and never the same one twice. -/
theorem gate_bounded (sys : System σ) (bridge : Bridge σ) (config : GateConfig) :
    (gate sys bridge config).Invariant fun pending =>
      pending.length ≤ config.maxPending ∧ pending.Nodup :=
  Actor.Inductive.invariant
    ⟨by simp [gate], fun _ msg h => Gate.step_bounded bridge config _ msg h, fun _ h => h⟩

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

/-- How the actors of a gated system are written to a snapshot, given how the system's own
are, and its outputs, which may be on their way to the gate. -/
def gatedActors {sys : System σ} (actors : Kernel.Image.Codecs sys) (out : Codec σ.Out)
    (bridge : Bridge σ) (config : GateConfig := {}) :
    Kernel.Image.Codecs (gated sys bridge config) where
  id := Codec.option actors.id
  state
    | none => Codec.list Codec.nat
    | some i => actors.state i
  msg
    | none => Codec.sum% GateMsg { arrive (id := Codec.nat) (request := Request.codec),
        answer (out := out), expire (id := Codec.nat) }
    | some i => actors.msg i

/-- What the gate assumes of whoever sends it requests: an id is used once. The gate's
at-most-once guarantee is stated for exactly these runs (`answered_nodup`), and the server
adapter is tested to stay within them. -/
def outside (σ : Signature) : Outside (gatedSig σ) (List ReqId) where
  init := []
  allow used x := if x.1 ∈ used then none else some (x.1 :: used)

end Lanes.Http
