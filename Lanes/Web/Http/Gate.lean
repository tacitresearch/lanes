/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Core.System
public import Lanes.Web.Http.Basic

/-!
The gate is the HTTP adapter's logic: it parses each request into an input, remembers which
requests are waiting, and answers each one with the system's response or with `504` when its
deadline passes. What is left in IO is reading and writing sockets.

The decisions are `Gate.step`, which does not know where the gate sits. `Lanes.Web.Http.Front` has
the gate as a system of its own (`gateSystem`), `fronted sys` with it joined in front of `sys`,
and `served sys`, which is what `Http.serve` runs.
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
  /-- What the server makes of a request before it gives it an id, on the request's own task:
  the system, its journal and its theorems see only what this returns. A secret is turned here
  into what the system needs of it (a password into its digest, a cookie into the user it
  verifies), so it is never journalled, and work too slow for the shard's one thread is done
  here, once, not again at every replay. -/
  prepare : Request → Request := id

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

end Lanes.Http
