/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Durable.Frame
public import Lanes.Lib.Crypto.Native

/-!
The handshake that opens every connection between peers, as a pure function. Each side first
writes a hello: the magic, the version of the handshake, the system's name, the digest of what
its codecs write and a nonce of its own. Each reads the other's hello and refuses one that
differs, naming both sides' values. Then each writes its proof, the HMAC-SHA-256 under the key
the processes share of its role and of both hellos, and a side is connected once the other's
proof checks (`Reachable.ready_proved`).

A proof covers the hello of the side that checks it, whose nonce is new on every connection,
so a handshake recorded and played again does not check; and it names the role of its maker,
so a proof sent back to the side that made it does not check either. What the handshake shows
is that the other side held the key when the connection opened. The bytes after it are not
authenticated or hidden: whoever can change bytes on the network can still change parcels.

The handler (`Lanes/Net/IO/Peers.lean`) writes what `step` answers and tells it what it reads.
-/

@[expose] public section

namespace Lanes.Peers.Handshake

/-- The first bytes on every connection between peers: `LANESNET`. -/
def magic : ByteArray := "LANESNET".toUTF8

/-- The version of the handshake and of what follows it on a connection. -/
def version : Nat := 1

/-- The size of a proof, an HMAC-SHA-256. -/
def proofSize : Nat := 32

structure Hello where
  version : Nat := Handshake.version
  system : String
  /-- The SHA-256 of the description of the codecs of the system's messages. -/
  digest : ByteArray
  nonce : ByteArray
  deriving DecidableEq

namespace Hello

/-- The version is the first record, so a hello of another version is known as one whatever
follows it. -/
def records (h : Hello) : List ByteArray :=
  [(toString h.version).toUTF8, h.system.toUTF8, h.digest, h.nonce]

def write (h : Hello) : ByteArray :=
  magic ++ Frame.encode h.records

inductive Read where
  /-- What has arrived may still become a hello. -/
  | more
  /-- The first bytes are not the magic: the other side is not a peer. -/
  | foreign (head : ByteArray)
  /-- A hello of another version, whose other records are not read. -/
  | version (theirs : Nat)
  | malformed
  /-- A hello, and the bytes it took. -/
  | hello (h : Hello) (taken : Nat)
  deriving DecidableEq

def read (bytes : ByteArray) : Read :=
  if bytes.size < magic.size then
    if bytes = magic.extract 0 bytes.size then .more else .foreign bytes
  else if bytes.extract 0 magic.size ≠ magic then .foreign (bytes.extract 0 magic.size)
  else
    let body := bytes.extract magic.size bytes.size
    let frames := Frame.decode body
    match frames with
    | [] => if Frame.unfinished body 0 then .more else .malformed
    | first :: rest =>
      match (String.fromUTF8? first).bind String.toNat? with
      | none => .malformed
      | some n =>
        if n ≠ Handshake.version then .version n
        else match rest with
          | name :: digest :: nonce :: _ =>
            match String.fromUTF8? name with
            | some system =>
              .hello { version := n, system, digest, nonce }
                (magic.size + Frame.span [first, name, digest, nonce])
            | none => .malformed
          | _ => if Frame.unfinished body (Frame.span frames) then .more else .malformed

end Hello

inductive Role where
  /-- The side that made the connection. -/
  | dialer
  | acceptor
  deriving DecidableEq, Repr

def Role.other : Role → Role
  | .dialer => .acceptor
  | .acceptor => .dialer

/-- What a proof starts with. Neither is a prefix of the other, and what follows starts with the
magic, so a proof of one role is never a proof of the other. -/
def Role.label : Role → ByteArray
  | .dialer => "lanes peer dialer ".toUTF8
  | .acceptor => "lanes peer acceptor ".toUTF8

structure Setup where
  role : Role
  /-- The key every process of the system shares. -/
  key : ByteArray
  /-- This side's hello, with a nonce made for this connection. -/
  ours : Hello
  /-- The most bytes the other side's hello may take. -/
  maxHelloBytes : Nat

/-- Why a connection is refused. Each that compares names both sides' values. -/
inductive Refusal where
  | foreign (head : ByteArray)
  | version (ours theirs : Nat)
  | system (ours theirs : String)
  | digest (ours theirs : ByteArray)
  | malformed
  | tooLong (limit : Nat)
  /-- The other side's proof does not check. -/
  | proof
  /-- The other side left before the handshake ended. -/
  | ended
  | timeout
  deriving DecidableEq

def Refusal.message : Refusal → String
  | .foreign head => s!"the other side is not a Lanes peer: it began with {Bytes.hex head}, \
      not {Bytes.hex magic}"
  | .version ours theirs => s!"the other side speaks version {theirs} of the peers' handshake, \
      and this one version {ours}"
  | .system ours theirs => s!"the other side runs the system \"{theirs}\", and this one \
      \"{ours}\""
  | .digest ours theirs => s!"the other side writes its messages otherwise: the digest of its \
      schema is {Bytes.hex theirs}, and this one's {Bytes.hex ours}"
  | .malformed => "the other side's hello is malformed"
  | .tooLong limit => s!"the other side's hello is longer than {limit} bytes"
  | .proof => "the other side's proof does not check: it has another key, or it plays back an \
      old handshake"
  | .ended => "the other side left during the handshake"
  | .timeout => "the other side did not finish the handshake in time"

/-- A refusal that says nothing about a peer: a connection opened and closed, as a port scan or
a health check does. -/
def Refusal.quiet : Refusal → Bool
  | .ended => true
  | _ => false

inductive State where
  /-- What has arrived of the other side's hello. -/
  | hello (received : ByteArray)
  /-- The other side's hello agrees: `heard` is its bytes, and `received` what has arrived of
  its proof. -/
  | proof (theirs : Hello) (heard received : ByteArray)
  | ready
  | refused

inductive Event where
  | received (bytes : ByteArray)
  /-- The other side left. -/
  | ended
  /-- The time the handshake may take has passed. -/
  | timeout
  deriving Inhabited

inductive Action where
  | write (bytes : ByteArray)
  /-- Connected. `rest` is what was read after the handshake: the start of the parcels. -/
  | ready (rest : ByteArray)
  | refuse (why : Refusal)
  deriving DecidableEq

/-- Both hellos, the dialer's first. -/
def transcript (s : Setup) (heard : ByteArray) : ByteArray :=
  match s.role with
  | .dialer => s.ours.write ++ heard
  | .acceptor => heard ++ s.ours.write

def proofOf (key : ByteArray) (role : Role) (transcript : ByteArray) : ByteArray :=
  hmac key (role.label ++ transcript)

def differs (ours theirs : Hello) : Option Refusal :=
  if ours.version ≠ theirs.version then some (.version ours.version theirs.version)
  else if ours.system ≠ theirs.system then some (.system ours.system theirs.system)
  else if ours.digest ≠ theirs.digest then some (.digest ours.digest theirs.digest)
  else none

def refuse (why : Refusal) : State × List Action := (.refused, [.refuse why])

/-- Wait for the whole proof, then check it. -/
def check (s : Setup) (theirs : Hello) (heard received : ByteArray) : State × List Action :=
  if received.size < proofSize then (.proof theirs heard received, [])
  else if Bytes.same (received.extract 0 proofSize)
      (proofOf s.key s.role.other (transcript s heard)) then
    (.ready, [.ready (received.extract proofSize received.size)])
  else refuse .proof

/-- Read the other side's hello; once it is there and agrees, write this side's proof. -/
def hear (s : Setup) (received : ByteArray) : State × List Action :=
  match Hello.read received with
  | .more =>
    if received.size > s.maxHelloBytes then refuse (.tooLong s.maxHelloBytes)
    else (.hello received, [])
  | .foreign head => refuse (.foreign head)
  | .version theirs => refuse (.version s.ours.version theirs)
  | .malformed => refuse .malformed
  | .hello theirs taken =>
    if taken > s.maxHelloBytes then refuse (.tooLong s.maxHelloBytes)
    else match differs s.ours theirs with
      | some why => refuse why
      | none =>
        let heard := received.extract 0 taken
        let (state, actions) := check s theirs heard (received.extract taken received.size)
        (state, .write (proofOf s.key s.role (transcript s heard)) :: actions)

def start (s : Setup) : State × List Action :=
  (.hello .empty, [.write s.ours.write])

def step (s : Setup) : State → Event → State × List Action
  | .hello received, .received bytes => hear s (received ++ bytes)
  | .proof theirs heard received, .received bytes => check s theirs heard (received ++ bytes)
  | .hello _, .ended | .proof .., .ended => refuse .ended
  | .hello _, .timeout | .proof .., .timeout => refuse .timeout
  | .ready, _ => (.ready, [])
  | .refused, _ => (.refused, [])

end Lanes.Peers.Handshake
