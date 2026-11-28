/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
The cache model (`Lanes/Outside/Cache.lean`) in front of a store, read through: a reader gets
the key from the cache, and on a miss reads the store and puts what it read in the cache. A
writer writes the store and then deletes the key. A reader that read the store before the write
and puts its value after the delete leaves the old value for every later reader: the checker
finds it (`lanesCheck`). With a lease the late fill is refused, and every read begun after the update gives
the new value, however the cache evicts. A cache that may answer stale values, as a lagging
replica or a failover does, breaks that too, and the checker finds it.
-/

namespace Tests.Cache

open Lanes

abbrev Request := Lanes.Cache.Request Unit Nat

abbrev Answer := Lanes.Cache.Answer Nat

lanes_data inductive Id where
  | reader (i : Fin 2)
  | writer
  | db
  deriving DecidableEq, Repr, Hashable, Enum

inductive DbMsg where
  | read (who : Fin 2)
  | write (value : Nat)
  deriving DecidableEq, Repr, Hashable

inductive ClientMsg where
  | start
  | cache (reply : Rpc.Reply Answer)
  /-- The store's value, to a reader; that the write is done, to the writer. -/
  | value (v : Nat)
  deriving DecidableEq, Repr, Hashable

abbrev Msg : Id → Type
  | .db => DbMsg
  | _ => ClientMsg

instance : ∀ i, DecidableEq (Msg i) := by instance_by_cases

inductive In where
  | read (i : Fin 2)
  | update
  | reply (call : Nat) (reply : Rpc.Reply Answer)
  deriving DecidableEq, Repr, Hashable

inductive Out where
  | cache (c : Rpc.Call Request)
  | result (i : Fin 2) (v : Nat)
  | updated
  deriving DecidableEq, Repr, Hashable

abbrev sig : Signature where
  Id := Id
  Msg := Msg
  In := In
  Out := Out

instance : sig.Inspect := by instance_by_cases

def ask (id : Nat) (request : Request) : Effect sig i := .emit (.cache ⟨id, 1000, request⟩)

/-- `lease` off seeds the bug: on a miss the reader sets the key to what it read. -/
def reader (lease : Bool) (i : Fin 2) : sig.Actor (.reader i) (Option Nat) where
  init := none
  step token
    | .start => (token, [ask (10 * i.val) (if lease then .lease () else .get ())])
    | .cache (.answer (.hit v)) => (token, [.emit (.result i v)])
    | .cache (.answer (.miss t)) => (t, [.send .db (.read i)])
    | .cache _ => (token, [])
    | .value v =>
      (token, .emit (.result i v) ::
        if lease then token.toList.map fun t => ask (10 * i.val + 1) (.fill () t v)
        else [ask (10 * i.val + 1) (.set () v)])
  recover token := (token, [])

def writer : sig.Actor .writer Unit where
  init := ()
  step _
    | .start => ((), [.send .db (.write 1)])
    | .value _ => ((), [ask 20 (.delete ())])
    | .cache (.answer .deleted) => ((), [.emit .updated])
    | .cache _ => ((), [])
  recover _ := ((), [])

def db : sig.Actor .db Nat where
  init := 0
  step value
    | .read who => (value, [.send (.reader who) (.value value)])
    | .write v => (v, [.send .writer (.value v)])
  recover value := (value, [])

abbrev system (lease : Bool) : System sig where
  State
    | .reader _ => Option Nat
    | .writer => Unit
    | .db => Nat
  actor
    | .reader i => reader lease i
    | .writer => writer
    | .db => db
  accept
    | .read i => ⟨.reader i, .start⟩
    | .update => ⟨.writer, .start⟩
    | .reply call r =>
      if call < 10 then ⟨.reader 0, .cache r⟩
      else if call < 20 then ⟨.reader 1, .cache r⟩
      else ⟨.writer, .cache r⟩

instance (lease : Bool) : (system lease).Inspect := by instance_by_cases

def port : Rpc.Port sig Request Answer Unit where
  called | .cache c => some c | _ => none
  replied | .reply id r => some (id, r) | _ => none

/-- Who has been asked to read, whether the update was asked for and has been done, the reads
begun after it was done, and whether one of those gave the old value. -/
structure Clients where
  asked : List (Fin 2) := []
  updating : Bool := false
  updated : Bool := false
  late : List (Fin 2) := []
  lateAnswered : Bool := false
  stale : Bool := false
  deriving DecidableEq, Repr, Hashable

def clients : Outside sig Clients where
  init := {}
  allow d
    | .read i => if i ∈ d.asked then none
      else some { d with asked := i :: d.asked, late := if d.updated then i :: d.late else d.late }
    | .update => if d.updating then none else some { d with updating := true }
    | .reply .. => none
  observe d
    | .updated => { d with updated := true }
    | .result i v =>
      if i ∈ d.late then { d with lateAnswered := true, stale := d.stale || v == 0 } else d
    | _ => d

abbrev Model := Rpc.State (Lanes.Cache.State Unit Nat)

def world (stale : Bool) :=
  clients.both (Rpc.outside port (Lanes.Cache.server { stale })) fun x => !(x matches .reply ..)

def answers (granted : List Nat) : Request → List Answer
  | .get _ => [.hit 0, .hit 1, .miss none]
  | .lease _ => [.hit 0, .hit 1, .miss none, .miss (some granted.length)]
  | .set .. => [.stored]
  | .fill .. => [.stored, .refused]
  | .delete _ => [.deleted]

def samples (d : Clients × Model) : List In :=
  [.read 0, .read 1, .update] ++ d.2.server.core.open_.flatMap fun p =>
    (answers d.2.server.core.granted p.request).map (.reply p.call ∘ .answer)

def check (lease stale : Bool) :=
  Check.system (system lease) { driver := (world stale).driver samples }
    [ .always "a read begun after the update gives the new value" fun w => !w.driver.1.stale,
      .sometimes "a read begun after the update is answered" (·.driver.1.lateAnswered) ]

def steps {S L : Type} : Option (Check.Failure S L) → Nat
  | some (.violated _ t) => t.steps.length
  | _ => 0

def call (id : Nat) (r : Request) : Lanes.Event sig := .output (.cache ⟨id, 1000, r⟩)

def answer (id : Nat) (a : Answer) : Lanes.Event sig := .input (.reply id (.answer a))

def model (stale : Bool := false) := Rpc.outside port (Lanes.Cache.server { stale })

/-- The model checks, run by `lanesCheck`: the fixed one explores about a hundred thousand
states. -/
def checks : IO (List (String × Bool)) := do
  let buggy := check false false
  let fixed := check true false
  let failover := check true true
  return [ (s!"cache model: a read-through fill that lands after the invalidation leaves the old value "
        ++ s!"({steps buggy.failure} steps)",
      match buggy.failure with
      | some (.violated "a read begun after the update gives the new value" _) => true
      | _ => false),
    (s!"cache model: with a lease the late fill is refused, whatever is evicted ({fixed.states} states)",
      fixed.ok),
    (s!"cache model: a cache that may answer stale values serves the old one even so "
        ++ s!"({steps failover.failure} steps)",
      match failover.failure with
      | some (.violated "a read begun after the update gives the new value" _) => true
      | _ => false) ]

def tests : List (String × Bool) :=
  [ ("cache model: a get may miss at any time, and hit only what was written",
      (model).allows [call 0 (.set () 3), answer 0 .stored, call 1 (.get ()), answer 1 (.miss none)]
        && (model).allows [call 0 (.set () 3), answer 0 .stored, call 1 (.get ()), answer 1 (.hit 3)]
        && !(model).allows [call 0 (.set () 3), answer 0 .stored, call 1 (.get ()), answer 1 (.hit 4)]),
    ("cache model: a get open while a write lands may see the value before it",
      (model).allows [call 0 (.set () 3), answer 0 .stored, call 1 (.get ()), call 2 (.set () 4),
        answer 2 .stored, answer 1 (.hit 3)]
        && !(model).allows [call 0 (.set () 3), answer 0 .stored, call 2 (.set () 4),
          answer 2 .stored, call 1 (.get ()), answer 1 (.hit 3)]),
    ("cache model: a write whose answer was lost may land later",
      (model).allows [call 0 (.set () 3), .input (.reply 0 .unknown), call 1 (.get ()),
        answer 1 (.hit 3)]),
    ("cache model: a fill after a delete of its key is refused, and one before it is overwritten",
      !(model).allows [call 0 (.lease ()), answer 0 (.miss (some 5)), call 1 (.delete ()),
          answer 1 .deleted, call 2 (.fill () 5 7), answer 2 .stored]
        && (model).allows [call 0 (.lease ()), answer 0 (.miss (some 5)), call 1 (.delete ()),
          call 2 (.fill () 5 7), answer 2 .stored, answer 1 .deleted, call 3 (.get ()),
          answer 3 (.miss none)]
        && !(model).allows [call 0 (.lease ()), answer 0 (.miss (some 5)), call 1 (.delete ()),
          call 2 (.fill () 5 7), answer 2 .stored, answer 1 .deleted, call 3 (.get ()),
          answer 3 (.hit 7)]),
    ("cache model: a stale cache may answer a value overwritten long ago",
      (model true).allows [call 0 (.set () 3), answer 0 .stored, call 1 (.set () 4),
        answer 1 .stored, call 2 (.get ()), answer 2 (.hit 3)]) ]

end Tests.Cache
