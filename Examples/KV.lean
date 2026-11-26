/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
# Reference app: a key-value store behind front ends

Clients talk to front-end actors; one store actor owns the data. The service spec is five lines:
a map, where `put` writes and `get` reads (`spec`). The system must look like that map to its
clients, however requests interleave.

The front ends can be configured to cache reads. That is the classic bug: a front end keeps
serving a value after another front end has overwritten it. The model checker finds it as a
refinement violation against the spec, with no refinement mapping written
(`Tests/KV.lean`). Without the cache the system passes.

Everything is generic over keys `K`, values `V` and front ends `F`, so the checker runs it with
one key, two values and two front ends.
-/

namespace Examples.KV

open Lanes

/-- Identifies a client request. -/
abbrev ReqId := Nat

/-- An operation on the store. -/
inductive Op (K V : Type) where
  | put (key : K) (value : V)
  | get (key : K)
  deriving DecidableEq, Repr, Hashable

/-- The result of an operation. -/
inductive Res (V : Type) where
  | ok
  | value (v : Option V)
  deriving DecidableEq, Repr, Hashable

/-- A client request, sent to the front end `via`. -/
structure Request (K V F : Type) where
  req : ReqId
  via : F
  op : Op K V
  deriving DecidableEq, Repr, Hashable

/-- The response to request `req`. -/
structure Response (V : Type) where
  req : ReqId
  res : Res V
  deriving DecidableEq, Repr, Hashable

/-- The actors: the front ends and the store. -/
inductive Id (F : Type) where
  | front (f : F)
  | store
  deriving DecidableEq, Repr, Hashable

/-- What a front end accepts. -/
inductive FrontMsg (K V F : Type) where
  /-- A client request. -/
  | request (r : Request K V F)
  /-- The store's answer to a read this front end forwarded. -/
  | got (req : ReqId) (key : K) (value : Option V)
  deriving DecidableEq, Repr, Hashable

/-- What the store accepts. -/
inductive StoreMsg (K V F : Type) where
  | put (req : ReqId) (key : K) (value : V)
  | get (req : ReqId) (key : K) (replyTo : F)
  deriving DecidableEq, Repr, Hashable

variable {K V F : Type} [DecidableEq K] [DecidableEq V] [DecidableEq F]

/-- Each actor's message type. -/
abbrev Msg (K V F : Type) : Id F → Type
  | .front _ => FrontMsg K V F
  | .store => StoreMsg K V F

instance : ∀ i, DecidableEq (Msg K V F i)
  | .front _ => inferInstanceAs (DecidableEq (FrontMsg K V F))
  | .store => inferInstanceAs (DecidableEq (StoreMsg K V F))

/-- The interface: requests in, responses out. -/
abbrev sig (K V F : Type) [DecidableEq K] [DecidableEq V] [DecidableEq F] : Signature where
  Id := Id F
  Msg := Msg K V F
  In := Request K V F
  Out := Response V

/-! ## The spec -/

/-- The service spec: a map. A `put` writes and answers `ok`; a `get` answers what the map
holds. Each request takes effect at one instant. -/
def spec (K V F : Type) [DecidableEq K] [DecidableEq V] [DecidableEq F] :
    Service (sig K V F) (K → Option V) where
  init _ := none
  step store r :=
    match r.op with
    | .put key value => (fun k => if k = key then some value else store k, [⟨r.req, .ok⟩])
    | .get key => (store, [⟨r.req, .value (store key)⟩])

/-! ## The implementation -/

/-- The store owns the data and answers one message at a time. -/
def store : (sig K V F).Actor .store (K → Option V) where
  init _ := none
  step data
    | .put req key value =>
      (fun k => if k = key then some value else data k, [.emit ⟨req, .ok⟩])
    | .get req key replyTo => (data, [.send (.front replyTo) (.got req key (data key))])
  recover data := (data, [])

/--
A front end forwards requests to the store. With `caching`, it remembers what it has read and
answers later reads of the same key itself. Nothing ever invalidates that memory, which is the
bug.
-/
def front (caching : Bool) (self : F) : (sig K V F).Actor (.front self) (List (K × Option V)) where
  init := []
  step cache
    | .request r =>
      match r.op with
      | .put key value => (cache, [.send .store (.put r.req key value)])
      | .get key =>
        match (if caching then cache.lookup key else none) with
        | some value => (cache, [.emit ⟨r.req, .value value⟩])
        | none => (cache, [.send .store (.get r.req key self)])
    | .got req key value =>
      (if caching then (key, value) :: cache.filter (·.1 ≠ key) else cache,
        [.emit ⟨req, .value value⟩])

/-- The system: front ends and one store. -/
abbrev system (K V F : Type) [DecidableEq K] [DecidableEq V] [DecidableEq F] (caching : Bool) :
    System (sig K V F) where
  State
    | .front _ => List (K × Option V)
    | .store => K → Option V
  actor
    | .front f => front caching f
    | .store => store
  accept r := ⟨.front r.via, .request r⟩

end Examples.KV
