/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Outside.Rpc

/-!
# A cache

A key-value cache as Redis or memcached gives one, in front of the store that holds the truth.
What makes it a cache and not a store: a key may be gone at any moment, evicted or expired, so
a get may always miss; and a write takes effect at some moment between its request and its
answer, or, if the answer was lost, at any moment after or never. A get answers what the key
held at some moment while it was open.

A lease (memcached's, as Facebook's paper describes it) is the right to fill a key after a
miss: a get that misses may grant a token, a `fill` with that token sets the key only while the
token is the key's lease, and any write to the key (or an eviction) ends the lease. It is what
stops a reader that missed from putting back a value older than a write and its invalidation
that came between its read of the store and its fill.

With `stale`, a get may answer any value ever written to its key, as a replica that lags or a
failover that lost the last writes may (Redis's replication is asynchronous). The model has no
time: a time to live is an eviction at some moment.

Proved: a get is answered only with a value a write sent under its key (`Cache.read_sent`), and
a fill sent when its token was not the key's lease is never stored (`Cache.fill_unleased`).

Not yet checked against a real service: no run recorded from Redis or memcached
(`oracles/README.md`).
-/

@[expose] public section

namespace Lanes.Cache

inductive Request (K V : Type) where
  | get (key : K)
  /-- A get that may grant a lease when it misses. -/
  | lease (key : K)
  | set (key : K) (value : V)
  /-- Set only while `token` is the key's lease. -/
  | fill (key : K) (token : Nat) (value : V)
  | delete (key : K)
  deriving DecidableEq, Repr, Hashable

inductive Answer (V : Type) where
  | hit (value : V)
  /-- Not there, with the token of a lease if one was granted. -/
  | miss (token : Option Nat)
  | stored
  /-- A fill whose lease had ended: nothing was set. -/
  | refused
  | deleted
  deriving DecidableEq, Repr, Hashable

variable {K V : Type}

def Request.key : Request K V → K
  | .get key | .lease key | .set key _ | .fill key _ _ | .delete key => key

/-- What a set or a delete leaves under its key if it lands. A fill is not here: whether it
lands depends on its lease. -/
def Request.leaves : Request K V → Option (Option V)
  | .set _ value => some (some value)
  | .delete _ => some none
  | _ => none

/-- A write answered: what it left, the token of a fill, and its call. -/
structure Landing (V : Type) where
  left : Option V
  token : Option Nat
  call : Nat
  deriving DecidableEq, Repr, Hashable

/-- A call open at the cache. -/
structure Pending (K V : Type) where
  call : Nat
  request : Request K V
  /-- What the key may have held when it was sent. -/
  before : List (Option V)
  /-- Each write to its key answered while it was open. -/
  landed : List (Landing V)
  /-- The tokens granted before it was sent: a fill with one of them landed before any write
  answered while it was open, since that write ended the lease when it landed. -/
  granted : List Nat
  /-- For a fill: whether its token was the key's lease when it was sent. -/
  leased : Bool
  deriving DecidableEq, Repr, Hashable

structure Core (K V : Type) where
  open_ : List (Pending K V) := []
  /-- What a key may hold after the last write to it answered. -/
  settled : List (K × List (Option V)) := []
  leases : List (K × Nat) := []
  granted : List Nat := []
  deriving DecidableEq, Repr, Hashable

structure State (K V : Type) where
  core : Core K V := {}
  /-- Every value a write sent, under its key. -/
  sent : List (K × V) := []
  /-- Every value a get was answered with, under its key. -/
  read : List (K × V) := []
  deriving DecidableEq, Repr, Hashable

structure Config where
  /-- A get may answer any value ever written to its key. -/
  stale : Bool := false

variable [DecidableEq K] [DecidableEq V]

namespace Core

/-- What `key` may hold now. -/
def possible (d : Core K V) (key : K) : List (Option V) :=
  (d.settled.lookup key).getD [none] ++ d.open_.filterMap fun p =>
    if p.request.key = key then
      match p.request with
      | .fill _ token value =>
        if p.leased && p.landed.isEmpty && d.leases.lookup key == some token then some (some value)
        else none
      | request => request.leaves
    else none

def receive (d : Core K V) (call : Rpc.Call (Request K V)) : Core K V :=
  let key := call.request.key
  let leased := match call.request with
    | .fill _ token _ => d.leases.lookup key == some token
    | _ => false
  { d with open_ := ⟨call.id, call.request, d.possible key, [], d.granted, leased⟩ :: d.open_ }

/-- The write `p` answered, having left `left`. A fill that was overwritten while it was open
(`lands` false) landed before each set and delete answered since, which would have ended its
lease: only a call open before those may have seen it. Every write ends its key's lease. -/
def settle (d : Core K V) (p : Pending K V) (left : Option V) (lands : Bool) (token : Option Nat) :
    Core K V :=
  let key := p.request.key
  let after := (p.landed.filter fun l => l.token.all (· ∉ p.granted)).map (·.left)
  let enders := (p.landed.filter (·.token.isNone)).map (·.call)
  { d with
    open_ := (d.open_.filter (·.call != p.call)).map fun q =>
      if q.request.key = key && (lands || enders.all fun c => q.landed.any (·.call == c)) then
        { q with landed := ⟨left, token, p.call⟩ :: q.landed }
      else q
    settled := if lands then (key, left :: after) :: d.settled.filter (·.1 != key) else d.settled
    leases := d.leases.filter (·.1 != key) }

def answer (d : Core K V) (p : Pending K V) : Answer V → Option (Core K V)
  | .hit _ => match p.request with
    | .get _ | .lease _ => some { d with open_ := d.open_.filter (·.call != p.call) }
    | _ => none
  | .miss none => match p.request with
    | .get _ | .lease _ => some { d with open_ := d.open_.filter (·.call != p.call) }
    | _ => none
  | .miss (some token) => match p.request with
    | .lease key =>
      if token ∈ d.granted then none
      else some { d with open_ := d.open_.filter (·.call != p.call)
                         leases := (key, token) :: d.leases.filter (·.1 != key)
                         granted := token :: d.granted }
    | _ => none
  | .stored => match p.request with
    | .set _ value => some (d.settle p (some value) true none)
    | .fill _ token value =>
      if p.leased then some (d.settle p (some value) p.landed.isEmpty (some token)) else none
    | _ => none
  | .refused => match p.request with
    | .fill .. => some { d with open_ := d.open_.filter (·.call != p.call) }
    | _ => none
  | .deleted => match p.request with
    | .delete _ => some (d.settle p none true none)
    | _ => none

end Core

/-- The key and value a get was answered with. -/
def readOf : Request K V → Answer V → Option (K × V)
  | .get key, .hit value | .lease key, .hit value => some (key, value)
  | _, _ => none

/-- A value a request sends. -/
def sentOf : Request K V → Option (K × V)
  | .set key value | .fill key _ value => some (key, value)
  | _ => none

/-- Whether a get open as `p` may be answered `value`: what its key held at some moment while
it was open, or with `stale` any value written to it. -/
def mayRead (config : Config) (d : State K V) (p : Pending K V) (kv : K × V) : Bool :=
  kv ∈ d.sent &&
    (config.stale || some kv.2 ∈ p.before ++ p.landed.map (·.left) ++ d.core.possible kv.1)

def server (config : Config) : Rpc.Server (State K V) (Request K V) (Answer V) Unit where
  init := {}
  receive d call :=
    { d with core := d.core.receive call
             sent := (sentOf call.request).toList ++ d.sent }
  answer d call a := do
    let p ← d.core.open_.find? (·.call == call)
    let core ← d.core.answer p a
    match readOf p.request a with
    | some kv => if mayRead config d p kv then some { d with core, read := kv :: d.read } else none
    | none => some { d with core }

/-- A fill sent when its token was not the key's lease is never stored. -/
theorem fill_unleased (config : Config) {d : State K V} {call : Nat} {p : Pending K V}
    (hp : d.core.open_.find? (·.call == call) = some p) {key : K} {token : Nat} {value : V}
    (hfill : p.request = .fill key token value) (hleased : p.leased = false) :
    (server config).answer d call .stored = none := by
  simp [server, hp, Core.answer, hfill, hleased]

/-- A get is answered only with a value a write sent under its key, in every run the model
allows: the cache invents nothing, whatever was lost or stale. -/
theorem read_sent (config : Config) {σ : Signature} (port : Rpc.Port σ (Request K V) (Answer V) Unit)
    {events : List (Event σ)} {d : Rpc.State (State K V)}
    (h : (Rpc.outside port (server config)).after events = some d) :
    ∀ kv ∈ d.server.read, kv ∈ d.server.sent := by
  refine Rpc.server_invariant port _ (fun _ => True) (fun d => ∀ kv ∈ d.read, kv ∈ d.sent)
    (by simp [server]) ?_ ?_ (fun _ _ _ _ h => by simp only [server] at h; cases h) (fun _ _ _ _ => trivial) h
  · intro s call hs _ kv hkv
    simp only [server, List.mem_append]
    exact .inr (hs kv hkv)
  · intro s call a s' hs hanswer kv hkv
    simp only [server, Option.bind_eq_bind, Option.bind_eq_some_iff] at hanswer
    obtain ⟨p, -, core, -, hanswer⟩ := hanswer
    split at hanswer
    · next kv' _ =>
      split at hanswer
      · next hmay =>
        obtain rfl := Option.some.inj hanswer
        simp only [mayRead, Bool.and_eq_true, decide_eq_true_eq] at hmay
        rcases List.mem_cons.mp hkv with rfl | hkv
        · exact hmay.1
        · exact hs kv hkv
      · simp at hanswer
    · obtain rfl := Option.some.inj hanswer
      exact hs kv hkv

end Lanes.Cache
