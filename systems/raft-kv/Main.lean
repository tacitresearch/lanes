/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RaftKV

/-!
One node of the key-value store as a process:

    raftNode <id> <http-port> <journal> <peer-port>...

The node is the shard of the cluster that hosts it, behind an HTTP front, with the other nodes
reached over TCP at the given ports on this machine, the `id`th being its own. `PUT /kv/<key>`
with the value as body writes, `GET /kv/<key>` reads. Only the leader answers; another node
lets the request run into its deadline, `504`, and the client asks the next.
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

def usage : String := "usage: raftNode <id> <http-port> <journal> <peer-port>..."

def main (args : List String) : IO UInt32 := do
  let id :: httpPort :: journal :: ports := args | do IO.eprintln usage; return 2
  let ports := ports.filterMap String.toNat?
  let n := ports.length
  let (some id, some httpPort) := (id.toNat?, httpPort.toNat?) | do IO.eprintln usage; return 2
  if h : id < n then
    let self : Fin n := ⟨id, h⟩
    let raft : Config := { electionTimeout_ms := 300 + 150 * id, heartbeat_ms := 50 }
    let http : Http.ServerConfig :=
      { port := httpPort.toUInt16, gate := { requestTimeout_ms := 1500 } }
    let message := fun (_ : Fin n) => Msg.codec (Codec.fin (n := n)) command
    let log ← Journal.Store.open
      (sys := Http.fronted (TextShard n raft self) (bridge self).shard http.gate)
      { path := journal, system := s!"raft-kv 1, node {id} of {n}"
        input := Codec.sum (Codec.pair Codec.nat Http.Request.codec)
          (Codec.sum (Request.codec Codec.fin command) (Codec.sigma Codec.fin message)) }
    let (server, _) ← (Http.serveShard (TextCluster n raft) (· == self) (bridge self)
      { listen := { port := (ports[id]?.getD 0).toUInt16 }
        home := fun i => return ports[i.val]?.map fun port => { port := port.toUInt16 }
        id := Codec.fin, msg := message } http {} (log := some log)).block
    IO.println s!"raft-kv node {id} of {n} on http://127.0.0.1:{server.port.getD 0}"
    (← IO.getStdout).flush
    server.wait.block
    return 0
  else
    IO.eprintln usage
    return 2
