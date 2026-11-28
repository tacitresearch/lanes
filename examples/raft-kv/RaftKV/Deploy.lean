/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RaftKV.Store

/-!
One node as a process: the shard of the cluster that hosts it, with the other nodes reached
over TCP and a journal for what it must not forget. How the protocol's messages are written to
the wire and to the journal, and a node's state to a snapshot, is here, from the codecs
`lanes_data` derives for the protocol's types, which carry their round-trip law.

The store a process runs keeps its map in a tree, not in a function as the checked instance
does: a function built by updates is walked from the newest update back on every read. The
tree is the extensional one, equal when its contents are, because a snapshot must read back as
the state that was written.
-/

namespace RaftKV

open Lanes Std.Async

abbrev Text := String

/-- The map as a process keeps it. -/
def treeStore : Machine (Op Text Text) (Res Text) (Std.ExtTreeMap Text Text) where
  init := {}
  apply m
    | .put key value => (m.insert key value, .ok)
    | .get key => (m, .value m[key]?)

abbrev Command := Op Text Text
abbrev Answer := Res Text

/-- A cluster of `n` nodes replicating the map. -/
abbrev TextCluster (n : Nat) (config : Config) :=
  cluster (Fin n) config treeStore

abbrev TextShard (n : Nat) (config : Config) (self : Fin n) :=
  (TextCluster n config).shard (· == self)

structure NodeConfig (n : Nat) where
  self : Fin n
  raft : Config := {}
  listen : Peers.Address
  /-- Where each node listens for the others. -/
  home : Fin n → BaseIO (Option Peers.Address)
  journal : Option System.FilePath := none
  /-- Whether a journal that is not there is begun: at a node's first start, and at no other. -/
  create : Bool := false
  /-- The key the nodes share, which their handshake checks. -/
  key : ByteArray

def message (n : Nat) (_ : Fin n) : Codec (Msg (Fin n) Command) := Codec.of _

/-- What a node's shard is handed: a client's request, or a message from another node. -/
def shardInput (n : Nat) : Codec (shardSig (sig (Fin n) Command Answer)).In := Codec.of _

def shardOutput (n : Nat) : Codec (shardSig (sig (Fin n) Command Answer)).Out := Codec.of _

/-- How a node's shard is written to a snapshot. -/
def shardActors (n : Nat) (config : Config) (self : Fin n) :
    Kernel.Image.Codecs (TextShard n config self) where
  id := Codec.fin
  state _ := Codec.of _
  msg := message n

deriving instance Repr for Config

/-- The name a node's journal is kept under, and without which it is refused. A journal holds
what the node was asked and when, and a start runs the step functions over it again. They read
the configuration: a timer is due at the clock's reading plus the configured delay, so with
another timeout the replay elects, votes and commits otherwise than the node did. So the name
holds every field of the configuration, and the number stands for the step functions. -/
def journalName (n : Nat) (self : Fin n) (config : Config) : String :=
  s!"raft-kv 2, node {self} of {n}, {repr config}"

/-- Start node `self`. Commands go in with `Runtime.input (.inl request)`, and the answers to
those this node took come to `onAnswer`. -/
/-- The system the nodes' handshake names. -/
def peerSystem (n : Nat) : String := s!"raft-kv of {n} nodes"

/-- What the nodes' messages are, which their handshake compares: it changes with `Msg`,
`Command` and their codecs. -/
def peerSchema (n : Nat) : String := s!"RaftKV.Msg (Fin {n}) RaftKV.Command by lanes_data, 1"

def startNode {n : Nat} (config : NodeConfig n) (runtime : Runtime.Config := {})
    (onAnswer : Response Answer → Async Unit := fun _ => pure ()) :
    Async (Runtime (TextShard n config.raft config.self) × Peers (sig (Fin n) Command Answer)) := do
  let log ← config.journal.mapM fun path =>
    Journal.Store.open (sys := TextShard n config.raft config.self)
      { path, system := journalName n config.self config.raft, input := shardInput n
        actors := some (shardActors n config.raft config.self), create := config.create }
  Peers.shard (TextCluster n config.raft) (· == config.self)
    { listen := config.listen, home := config.home, id := Codec.fin, msg := message n
      system := peerSystem n, schema := peerSchema n, key := config.key }
    runtime onAnswer log

end RaftKV
