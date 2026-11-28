/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std.Async
public import Lanes.Runtime.IO.Shell
public import Lanes.Services.Postgres.Settings
public import Lanes.Services.Postgres.Table
public import Lanes.Lib.Crypto.Certificate
public import Lanes.Web.IO.Tls

/-!
The IO of a connection to PostgreSQL. It opens a TCP socket, tells the connection (`Postgres.Conn.step`)
what happened, and does what it answers: send bytes, run the TLS handshake, report a reply. It
decides nothing (rule 3.9): whether to ask for TLS, what the server's answer means, which bytes
to send, with which channel binding, what the server's bytes mean, which reply answers which
request and what a reply to `COMMIT` means are `Conn.step`'s, proved in
`Lanes/Services/Postgres/ConnSound.lean`. It draws the SCRAM nonce from `randomBytes`, reads no more than
`Conn.room` bytes at a time, and tells the connection the socket broke when a send or a read
fails or a request's deadline passes.

TLS is `Tls.Session` over the same socket: when the connection asks for it, the handshake runs
there, and from then on every byte goes through the session. The hash of the server's
certificate for channel binding is `Certificate.endPoint`, pure.

`Session` is a connection used by one task at a time. `Store.handler` runs the transactional
store of `Lanes/Outside/Store/Basic.lean` on a table (`Lanes/Services/Postgres/Table.lean`) as an
adapter: each transaction on a connection of its own, each request on a task of its own, its
answer handed back as an input.

`connect` resolves the host at each call, so that a new connection, the pool's too, follows a
name to a new address after a failover. `Client.fromEnv` reads the configuration from the
environment through `Settings.read`, pure.
-/

public section

namespace Lanes.Postgres

open Std Std.Async

structure Client.Config where
  /-- An IPv4 or IPv6 address, or a name, resolved at each connect to its first IPv4 address,
  or its first IPv6 address if it has none (`Address.of`, `Address.preferred`). -/
  host : String
  port : UInt16 := 5432
  conn : Conn.Config
  /-- How long connecting and authenticating, and each request, may take (rule 3.4). -/
  timeout_ms : Nat := 10000
  /-- No TLS to this machine, full verification elsewhere, unless given. -/
  sslmode : SslMode := SslMode.defaultFor host
  /-- The authorities the server's certificate must chain to: for RDS, its bundle. -/
  trust : Tls.Trust := .system
  /-- The name the certificate must be for, and the one sent as SNI: `host` if none. An IP
  address is checked as an address, and sent as no SNI, which RFC 6066 leaves to names. -/
  serverName : Option String := none
  /-- PostgreSQL 17's direct TLS: the handshake at once, with ALPN, without `SSLRequest`. -/
  direct : Bool := false

/-- The encryption `Conn.step` is told to use. -/
def Client.Config.encryption (cfg : Client.Config) : Conn.Encryption :=
  if cfg.sslmode = .disable then .plain else if cfg.direct then .direct else .negotiated

theorem Client.Config.sslmode_default (host : String) (conn : Conn.Config) :
    ({ host, conn } : Client.Config).sslmode = SslMode.defaultFor host := rfl

/-- The configuration the settings give. -/
def Client.Config.ofSettings (s : Settings) : Client.Config :=
  { host := s.host, port := s.port, sslmode := s.sslmode,
    trust := s.rootCert.elim .system fun path => .file path,
    conn := { user := s.user, database := s.database, password := s.password,
              channelBinding := s.channelBinding } }

/-- The process's environment and files. -/
def Env.io : Env IO where
  var name := IO.getEnv name
  file path := do try return some (← IO.FS.readFile path) catch _ => return none
  present path := System.FilePath.pathExists path

/-- The configuration libpq's environment variables give, or a deploy's (`Settings.read`), with
TLS as `SslMode.defaultFor` the host unless `PGSSLMODE` says; an error says what cannot be
done. -/
def Client.fromEnv : IO Client.Config := do
  match ← (Settings.read Env.io).run with
  | .ok s => return .ofSettings s
  | .error why => throw (IO.userError s!"lanes: PostgreSQL: {why}")

structure Session where
  socket : TCP.Socket.Client
  cfg : Conn.Config
  conn : IO.Ref Conn
  next : IO.Ref Nat
  timeout_ms : Nat
  /-- A new TLS session with the server, as the configuration says. -/
  startTls : IO Tls.Session
  /-- Once the handshake is done. -/
  tls : IO.Ref (Option Tls.Session)

namespace Session

def flush (s : Session) (t : Tls.Session) : Async Unit := do
  let out ← t.take
  unless out.isEmpty do s.socket.send out

/-- Bytes to the server: through TLS once it is up. -/
def transmit (s : Session) (bytes : ByteArray) : Async Unit := do
  match ← s.tls.get with
  | some t => t.write bytes; s.flush t
  | none => s.socket.send bytes

/-- At most `max` bytes from the server, decrypted once TLS is up; `none` at its end. -/
partial def receive (s : Session) (max : Nat) : Async (Option ByteArray) := do
  match ← s.tls.get with
  | none => s.socket.recv? max.toUInt64
  | some t =>
    let got ← t.read max.toUInt32
    unless got.isEmpty do return some got
    let some bytes ← s.socket.recv? 65536 | return none
    if bytes.isEmpty then return some .empty
    t.feed bytes
    s.flush t
    s.receive max

/-- The TLS handshake on the socket, and what it gave: the hash of the server's certificate for
channel binding and the ALPN protocol chosen, or why it failed. -/
def handshake (s : Session) : Async Conn.Event := do
  try
    let t ← s.startTls
    repeat
      let done ← t.handshake
      s.flush t
      if done then break
      let some bytes ← s.socket.recv? 65536 | return .insecure "the server closed the connection"
      if bytes.isEmpty then return .insecure "the server closed the connection"
      t.feed bytes
    s.tls.set (some t)
    return .secured (Certificate.endPoint (← t.peer)) (← t.alpn)
  catch e => return .insecure (toString e)

mutual
/-- Do what the connection answered, in order; what it answers then is returned too. A send that
fails is told as a broken socket, and the end of a handshake as `secured` or `insecure`. -/
partial def perform (s : Session) (actions : List Conn.Action) : Async (List Conn.Action) := do
  let mut failed := false
  let mut tls := false
  for a in actions do
    match a with
    | .send bytes | .query _ bytes =>
      if !failed then
        try s.transmit bytes catch _ => failed := true
    | .startTls => tls := true
    | .close _ => s.socket.close
    | _ => pure ()
  if failed then return actions ++ (← s.tell .broken)
  if tls then return actions ++ (← s.tell (← s.handshake))
  return actions

/-- Tell the connection `e` and do what it answers; what it answers is returned. -/
partial def tell (s : Session) (e : Conn.Event) : Async (List Conn.Action) := do
  let (c, actions) := (← s.conn.get).step s.cfg e
  s.conn.set c
  s.perform actions
end

/-- Read and tell until `found` picks something out of what the connection answers, or it
closes. -/
partial def await {α : Type} (s : Session) (found : List Conn.Action → Option α)
    (seen : List Conn.Action) : Async (Option α) := do
  if let some a := found seen then return some a
  if seen.any (fun | .close _ => true | _ => false) then return none
  let room := (← s.conn.get).room s.cfg
  let bytes ← try s.receive (min room 65536) catch _ => pure (some .empty)
  let actions ← match bytes with
    | some b => if b.isEmpty then s.tell .broken else s.tell (.received b)
    | none => s.tell .ended
  s.await found actions

def within {α : Type} (timeout_ms : Nat) (work : Async (Option α)) : Async (Option α) :=
  Async.race work ((fun _ => none) <$> Async.sleep (.ofNat timeout_ms))

/-- Send `r` and wait for its reply. A deadline that passes breaks the connection, and the reply
is then `unknown`. -/
def exec (s : Session) (r : Request) : Async Reply := do
  let id ← s.next.modifyGet fun n => (n, n + 1)
  let pick := fun (actions : List Conn.Action) => actions.findSome? fun
    | .reply i reply => if i == id then some reply else none
    | _ => none
  let first ← s.tell (.submit id r)
  match ← within s.timeout_ms (s.await pick first) with
  | some reply => return reply
  | none =>
    let late ← s.tell .broken
    return (pick late).getD .unknown

/-- Tell the server the session is over, and close. Over TLS, `Terminate` goes through the
session and the socket closes without `close_notify`, which PostgreSQL does not need: a task
given up on may still be reading through the session, and a session is used by one task at a
time. -/
def close (s : Session) : Async Unit := do
  discard <| s.tell .stop
  s.socket.close

end Session

def socketAddress (a : Ip.Addr) (port : UInt16) : Option Std.Net.SocketAddress :=
  match a with
  | .v4 n =>
    match Digits.split 256 4 n.val with
    | [a, b, c, d] => some (.v4 ⟨.ofParts a.toUInt8 b.toUInt8 c.toUInt8 d.toUInt8, port⟩)
    | _ => none
  | .v6 n =>
    match (Digits.split 65536 8 n.val).map Nat.toUInt16 with
    | [a, b, c, d, e, f, g, h] => some (.v6 ⟨.ofParts a b c d e f g h, port⟩)
    | _ => none

/-- Where `host` is now: a name is resolved at each call, to the address `Address.preferred`
picks, so that a new connection follows it to a new address. -/
def resolve (host : String) (port : UInt16) : Async (Option Std.Net.SocketAddress) := do
  match Address.of host with
  | .ip a => return socketAddress a port
  | .name name =>
    let found ← DNS.getAddrInfo name ""
    return (Address.preferred (· matches .v4 _) found.toList).map fun
      | .v4 addr => .v4 ⟨addr, port⟩
      | .v6 addr => .v6 ⟨addr, port⟩

/-- Connect and authenticate: a session open for requests, or why it closed. The host is
resolved again at each call. -/
def connect (cfg : Client.Config) : Async (Except (Option Closing) Session) := do
  let nonce := Base64.encode .std (← randomBytes 18)
  let conn := { cfg.conn with nonce, encryption := cfg.encryption }
  let name := cfg.serverName.getD cfg.host
  let startTls := match cfg.sslmode with
    | .verifyFull => Tls.Session.start cfg.trust name ["postgresql"]
    | _ => Tls.Session.startChain cfg.trust name ["postgresql"]
  let socket ← TCP.Socket.Client.mk
  let s : Session := { socket, cfg := conn, conn := ← IO.mkRef {}, next := ← IO.mkRef 0,
                       timeout_ms := cfg.timeout_ms, startTls, tls := ← IO.mkRef none }
  let opened := fun (actions : List Conn.Action) => actions.findSome? fun
    | .opened => some (Except.ok ())
    | .close why => some (.error why)
    | _ => none
  let attempt : Async (Option (Except Closing Unit)) := do
    let some addr ← resolve cfg.host cfg.port | return none
    socket.connect addr
    let (c, actions) := Conn.start conn
    s.conn.set c
    s.await opened (← s.perform actions)
  match ← (try Session.within cfg.timeout_ms attempt catch _ => pure none) with
  | some (.ok ()) => return .ok s
  | some (.error why) => socket.close; return .error (some why)
  | none => socket.close; return .error none

namespace Store

/-- The sessions of the transactions open. -/
abbrev Sessions := IO.Ref (List (Nat × Session))

/-- Perform one request on its transaction's session, opening one for `begin`, and closing it
once the transaction is over or its session failed. -/
def perform (cfg : Client.Config) (table : Table) (isolation : Lanes.Store.Isolation)
    (sessions : Sessions) (r : Lanes.Store.Request Nat String) : Async (Lanes.Store.Answer Nat String) := do
  let request := table.request isolation r.op
  let session ← match r.op with
    | .begin =>
      match ← connect cfg with
      | .ok s =>
        sessions.modify ((r.txn, s) :: ·)
        pure (some s)
      | .error _ => pure none
    | _ => pure ((← sessions.get).lookup r.txn)
  let some s := session | return .failed
  let reply ← try s.exec request catch _ => pure .unknown
  let answer := Table.answer r.op reply
  if Table.over r.op answer then
    sessions.modify (·.filter (·.1 != r.txn))
    try s.close catch _ => pure ()
  return answer

/-- The store as an adapter: each request on a task of its own, its answer handed back as an
input. An answer that finds the inbox full is dropped, which the model allows as a lost one. -/
def handler {σ : Signature} {sys : System σ} [Hashable σ.Id] (port : Lanes.Store.Port σ Nat String)
    (cfg : Client.Config) (table : Table) (isolation : Lanes.Store.Isolation) (sessions : Sessions)
    (rt : Runtime sys) (out : σ.Out) : Async Unit := do
  if let some r := port.request out then
    background do
      let answer ← try perform cfg table isolation sessions r catch _ => pure .unknown
      discard <| rt.tryInput (port.reply { id := r.id, answer })

end Store

end Lanes.Postgres
