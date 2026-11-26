/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RaftKV

/-!
One node of the key-value store as a process:

    raftNode new <id> <http-port> <journal> <peer-port>...    its first start
    raftNode <id> <http-port> <journal> <peer-port>...        every later one

The node is the shard of the cluster that hosts it, behind an HTTP front, with the other nodes
reached over TCP at the given ports on this machine, the `id`th being its own. `PUT /kv/<key>`
with the value as body writes, `GET /kv/<key>` reads. Only the leader answers; another node
lets the request run into its deadline, `504`, and the client asks the next.

A node's journal is its memory of the votes it gave and the entries it acknowledged. Started
without one it would give them again, so only `new` begins a journal, and without `new` a
journal that is not there is a refusal to start.
-/

open Lanes RaftKV Std Std.Async

namespace Routes

def write : Http.Route Http.Slug := .put ("kv" /> .slug)
def read : Http.Route Http.Slug := .get ("kv" /> .slug)

end Routes

def bridge {n : Nat} (self : Fin n) : Http.Bridge (sig (Fin n) Command Answer) where
  decode id request :=
    (Http.dispatch [
      Routes.write.handle fun key r =>
        match r.text? with
        | some value => .ok ⟨id, self, .put key.text value⟩
        | none => .error (.text "the value must be text\n" 400),
      Routes.read.handle fun key _ => .ok ⟨id, self, .get key.text⟩
    ] request).getD (.error (.text "not found\n" 404))
  encode answer :=
    some (answer.req, match answer.res with
      | .ok => .text "ok\n"
      | .value (some value) => .text value
      | .value none => .text "no such key\n" 404)

def usage : String :=
  "usage: raftNode [new] [--snapshot-every <entries>] <id> <http-port> <journal> <peer-port>...\n"
    ++ "  new   this node has never run: begin its journal. Without it the journal must be there."

/--
How many journal entries a node writes between two saves of its state. A save cuts the journal,
so this bounds the journal and what a start replays. It also writes the node's whole state, its
log included, and the log is never compacted, so saves must not come often.

Measured with three nodes on one machine. An idle follower writes 60 entries a second and the
leader 160, of 70 to 90 bytes, which uncut is 470 and 930 MB a day; at this number an idle node
saves every 7 to 18 minutes and its journal stays under 6 MB. Under load a write is about ten
entries on the leader, so a save comes every six thousand writes or so. After 10,000 small
writes the state is 0.6 MB, saving it delays no write by a tenth of a second, and a start,
snapshot and replay together, takes a few tenths.
-/
def defaultSnapshotEvery : Nat := 65536

structure Args where
  create : Bool
  snapshotEvery : Nat
  id : Nat
  httpPort : Nat
  journal : System.FilePath
  ports : List Nat

def Args.parse (args : List String) : Option Args := do
  let (create, args) := match args with
    | "new" :: rest => (true, rest)
    | _ => (false, args)
  let (every, args) ← match args with
    | "--snapshot-every" :: entries :: rest => entries.toNat?.map (·, rest)
    | _ => some (defaultSnapshotEvery, args)
  let id :: httpPort :: journal :: ports := args | none
  return { create, snapshotEvery := every, id := ← id.toNat?, httpPort := ← httpPort.toNat?
           journal, ports := ← ports.mapM String.toNat? }

/-- A file with nothing in it is what a start that died before its first write leaves. -/
def hasJournal (path : System.FilePath) : IO Bool := do
  if ← path.pathExists then return (← path.metadata).byteSize > 0 else return false

def serve {n : Nat} (args : Args) (self : Fin n) : IO UInt32 := do
  let raft : Config := { electionTimeout_ms := 300 + 150 * self.val, heartbeat_ms := 50 }
  let http : Http.ServerConfig :=
    { port := args.httpPort.toUInt16, gate := { requestTimeout_ms := 1500 } }
  let log ← Journal.Store.open
    (sys := Http.fronted (TextShard n raft self) (bridge self).shard http.gate)
    { path := args.journal, create := args.create
      -- The gate is an actor of the node's system, and its step function reads its own
      -- configuration as the nodes read theirs (`journalName`).
      system := s!"{journalName n self raft}, behind a gate of "
        ++ s!"{http.gate.requestTimeout_ms} ms and {http.gate.maxPending} requests"
      input := Codec.sum (Codec.pair Codec.nat Http.Request.codec) (shardInput n)
      actors := some (Http.frontedActors (shardActors n raft self) (shardOutput n)
        (bridge self).shard http.gate) }
  let (server, _) ← (Http.serveShard (TextCluster n raft) (· == self) (bridge self)
    { listen := { port := (args.ports[self.val]?.getD 0).toUInt16 }
      home := fun i => return args.ports[i.val]?.map fun port => { port := port.toUInt16 }
      id := Codec.fin, msg := message n } http { snapshotEvery := args.snapshotEvery }
    (log := some log)).block
  IO.println s!"raft-kv node {self} of {n} on http://127.0.0.1:{server.port.getD 0}"
  (← IO.getStdout).flush
  server.wait.block
  return 0

def main (args : List String) : IO UInt32 := do
  let some args := Args.parse args | do IO.eprintln usage; return 2
  if h : args.id < args.ports.length then
    if args.create && (← hasJournal args.journal) then
      IO.eprintln (s!"raftNode: {args.journal} is there already, so this node has run: "
        ++ "start it without `new`")
      return 1
    try serve args ⟨args.id, h⟩
    catch e =>
      IO.eprintln s!"raftNode: {e}"
      unless args.create || (← hasJournal args.journal) do
        IO.eprintln ("raftNode: a node's first start is `raftNode new ...`. If this node has "
          ++ "run, its journal is lost, and with it the votes it gave and the entries it "
          ++ "acknowledged: started as new it may help elect a leader that lacks a write the "
          ++ "cluster has answered")
      return 1
  else
    IO.eprintln usage
    return 2
