/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RaftKV.Store

/-!
One node as a process: the shard of the cluster that hosts it, with the other nodes reached
over TCP and a journal for what it must not forget. How the protocol's messages are written to
the wire and to the journal is here, built from codecs that carry their round-trip law.

The store a process runs keeps its map in a tree, not in a function as the checked instance
does: a function built by updates is walked from the newest update back on every read.
-/

namespace RaftKV

open Lanes Std.Async

def Op.codec (k : Codec K) (v : Codec V) : Codec (Op K V) :=
  Codec.sum% Op { put (key := k) (value := v), get (key := k) }

def Entry.codec (n : Codec N) (c : Codec C) : Codec (Entry N C) :=
  Codec.struct% Entry { term := Codec.nat, origin := n, req := Codec.nat, cmd := c }

def Msg.codec (n : Codec N) (c : Codec C) : Codec (Msg N C) :=
  Codec.sum% Msg { electionTimeout, heartbeat,
    requestVote (term := Codec.nat) (candidate := n) (lastIndex := Codec.nat)
      (lastTerm := Codec.nat),
    vote (term := Codec.nat) (voter := n),
    append (term := Codec.nat) (leader := n) (prevIndex := Codec.nat) (prevTerm := Codec.nat)
      (entries := Codec.list (Entry.codec n c)) (commit := Codec.nat),
    appended (term := Codec.nat) (follower := n) (matched := Codec.nat),
    propose (req := Codec.nat) (cmd := c) }

def Request.codec (n : Codec N) (c : Codec C) : Codec (Request N C) :=
  Codec.struct% Request { req := Codec.nat, via := n, cmd := c }

abbrev Text := String

/-- The map as a process keeps it. -/
def treeStore : Machine (Op Text Text) (Res Text) (Std.TreeMap Text Text) where
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

def command : Codec Command := Op.codec Codec.string Codec.string

/-- Start node `self`. Commands go in with `Runtime.input (.inl request)`, and the answers to
those this node took come to `onAnswer`. -/
def startNode {n : Nat} (config : NodeConfig n)
    (onAnswer : Response Answer → Async Unit := fun _ => pure ()) :
    Async (Runtime (TextShard n config.raft config.self) × Peers (sig (Fin n) Command Answer)) := do
  let message := fun (_ : Fin n) => Msg.codec (Codec.fin (n := n)) command
  let log ← config.journal.mapM fun path =>
    Journal.Store.open (sys := TextShard n config.raft config.self)
      { path, system := s!"raft-kv 1, node {config.self} of {n}"
        input := Codec.sum (Request.codec Codec.fin command) (Codec.sigma Codec.fin message) }
  Peers.shard (TextCluster n config.raft) (· == config.self)
    { listen := config.listen, home := config.home, id := Codec.fin, msg := message } {} onAnswer log

end RaftKV
