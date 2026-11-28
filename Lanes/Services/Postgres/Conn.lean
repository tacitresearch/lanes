/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Services.Postgres.Message
public import Lanes.Services.Postgres.Scram

/-!
# A connection to PostgreSQL, as a pure function

The IO that runs a connection (`Lanes.Services.Postgres.IO.Client`) tells it what happened
(`Postgres.Conn.Event`: bytes received, the end of them, a broken socket, a request to send, the
TLS handshake done or failed, `stop`) and does what it answers (`Postgres.Conn.Action`: send
bytes, send a request's bytes, start TLS, report the connection open, answer a request, close),
and asks it how many bytes it takes (`Conn.room`). Everything else is decided here: whether to
ask for TLS (`SSLRequest`) and what the server's answer means, that nothing else is sent before
the handshake is done, the start-up, which authentication to answer and how, with which channel
binding, whether the server proved it knows the password, what the bytes received are as
messages, which request each reply answers, and what a reply to `COMMIT` means.

Requests are sent only once the connection is open, at most `inflight_max` at a time, each
ended by its own `Sync` (or a simple query), so the server answers each with one
`ReadyForQuery`, and replies are matched to requests in the order they were sent. The state of
the transaction is the one the last `ReadyForQuery` reported. A connection that ends, breaks or
receives what the protocol does not allow answers every request in flight with `unknown`, and
closes (rule 3.1).

What it promises is proved in `Lanes/Services/Postgres/ConnSound.lean`, and model-checked against a
server that answers in any pieces and may fail any statement or leave at any moment
(`Tests/PostgresConn.lean`).
-/

@[expose] public section

namespace Lanes.Postgres

inductive Isolation where
  | readCommitted
  | repeatableRead
  | serializable
  deriving DecidableEq, Repr, Hashable

def Isolation.sql : Isolation → String
  | .readCommitted => "READ COMMITTED"
  | .repeatableRead => "REPEATABLE READ"
  | .serializable => "SERIALIZABLE"

/-- SQL with `$1`, `$2`, … and their values in text, `none` for `NULL`. -/
structure Statement where
  sql : String
  params : List (Option String) := []
  deriving DecidableEq, Repr, Hashable

inductive Request where
  | begin (isolation : Isolation)
  | statement (s : Statement)
  | commit
  | rollback
  deriving DecidableEq, Repr, Hashable

/-- The rows of a reply, in text, and the server's tag (`SELECT 3`, `INSERT 0 1`, `BEGIN`). -/
structure Rows where
  columns : List String := []
  rows : List (List (Option String)) := []
  tag : String := ""
  deriving DecidableEq, Repr, Hashable

/-- Why a request was not sent. -/
inductive Refusal where
  /-- The connection is not open yet, or closed. -/
  | notReady
  /-- `inflight_max` requests are in flight. -/
  | busy
  /-- It cannot be written: a NUL in the SQL, too many parameters, more than `message_max`. -/
  | invalid
  deriving DecidableEq, Repr, Hashable

inductive Reply where
  | rows (rows : Rows)
  /-- The server's `ErrorResponse`; the SQLSTATE is the field of code `C`. -/
  | error (fields : List Field)
  /-- The server committed the transaction. -/
  | committed
  /-- No transaction was committed: a `ROLLBACK`, or a `COMMIT` in a transaction that had failed
  or outside one. -/
  | rolledBack
  /-- More than `rows_max` rows; the rest were read and dropped. -/
  | tooManyRows
  | refused (why : Refusal)
  /-- The connection ended before the reply: whether the request took effect is unknown. -/
  | unknown
  deriving DecidableEq, Repr, Hashable

/-- Why a connection closed. -/
inductive Closing where
  | ended
  | broken
  | stopped
  /-- What the server sent is not what the protocol allows now. -/
  | protocol
  /-- The server refused, with its `ErrorResponse`. -/
  | server (fields : List Field)
  /-- The server asked for an authentication this client may not answer. -/
  | method
  /-- The server did not prove it knows the password. -/
  | signature
  | scram (why : Scram.Refusal)
  /-- The configuration cannot be sent: a NUL in the user, an empty nonce. -/
  | invalid
  /-- The server answered `SSLRequest` with `N`, and TLS is required. -/
  | refusedTls
  /-- The TLS handshake failed, with OpenSSL's reason. -/
  | tls (why : String)
  /-- Direct TLS, and the server did not choose the ALPN protocol `postgresql`. -/
  | alpn
  deriving DecidableEq, Repr

namespace Conn

/-- How a connection is encrypted. There is no `prefer`: a connection that asked for TLS and is
answered `N` closes, rather than go on in the clear. -/
inductive Encryption where
  | plain
  /-- TLS after PostgreSQL's `SSLRequest` and the server's `S`. -/
  | negotiated
  /-- TLS from the first byte, with the ALPN protocol `postgresql`: PostgreSQL 17's
  `sslnegotiation=direct`. -/
  | direct
  deriving DecidableEq, Repr, Hashable

/-- Whether SCRAM binds the TLS channel (`SCRAM-SHA-256-PLUS`, `tls-server-end-point`). With
`prefer`, a server that offers it is answered with it, and one that does not is told the client
could have (`Scram.Binding.unoffered`), which a server that did offer it refuses. -/
inductive ChannelBinding where
  | require
  | prefer
  | disable
  deriving DecidableEq, Repr, Hashable

/-- Every limit is explicit (rule 2.6). -/
structure Config where
  user : String
  database : String
  password : Option String := none
  /-- The SCRAM nonce: printable ASCII but `,`, drawn at random by the IO for each connection. -/
  nonce : String := ""
  /-- Whether the password may be sent as it is when the server asks so. Over plain TCP anyone
  on the path reads it, so it is off unless asked for. -/
  allowCleartext : Bool := false
  /-- Whether an MD5 digest of the password may be sent when the server asks for one. The digest
  can be guessed against offline by whoever asked, so it is off unless asked for. -/
  allowMd5 : Bool := false
  /-- With a password, whether the server must prove it knows it, by SCRAM, before the
  connection opens: an `AuthenticationOk` before SCRAM's last message, or a request for a
  cleartext password or an MD5 digest, closes it. A server that skips SCRAM could be anyone on
  the path. Turn it off, with `allowMd5` or `allowCleartext`, only for a server that has no
  SCRAM. -/
  requireScram : Bool := true
  /-- A message's length, counting its four bytes of length. -/
  message_max : Nat := 1048576
  rows_max : Nat := 100000
  inflight_max : Nat := 16
  /-- SCRAM's iteration count, which the server chooses and the client pays for. -/
  iterations_max : Nat := 100000
  /-- Set by the IO from its TLS mode. -/
  encryption : Encryption := .plain
  channelBinding : ChannelBinding := .prefer

inductive Kind where
  | begin
  | statement
  | commit
  | rollback
  deriving DecidableEq, Repr, Hashable

def Request.kind : Request → Kind
  | .begin _ => .begin
  | .statement _ => .statement
  | .commit => .commit
  | .rollback => .rollback

/-- A request sent whose reply is being read. -/
structure Pending where
  id : Nat
  kind : Kind
  columns : List String := []
  /-- Newest first. -/
  rows : List (List (Option String)) := []
  count : Nat := 0
  tag : Option String := none
  error : Option (List Field) := none
  deriving DecidableEq, Repr, Hashable

inductive Phase where
  /-- `SSLRequest` is sent; the server is to answer `S` or `N`. -/
  | sslRequest
  /-- The IO runs the TLS handshake. -/
  | handshake
  /-- The start-up is sent; the server is to say how to authenticate. -/
  | startup
  /-- A password or its digest is sent. -/
  | password
  /-- SCRAM's first message is sent, with this channel binding. -/
  | sasl (binding : Scram.Binding)
  /-- SCRAM's last message is sent, and the server must answer with `signature`. -/
  | saslFinal (signature : ByteArray)
  /-- The server proved it knows the password. -/
  | saslDone
  /-- Authenticated; the server is to say it is ready. -/
  | authed
  | ready
  | closed
  deriving DecidableEq

inductive Event where
  | received (bytes : ByteArray)
  /-- The server sends no more. -/
  | ended
  | broken
  | submit (id : Nat) (request : Request)
  /-- The TLS handshake is done: the hash of the server's certificate for channel binding
  (`Certificate.endPoint`), if it has one, and the ALPN protocol the server chose, empty if
  none. -/
  | secured (endPoint : Option ByteArray) (alpn : ByteArray)
  | insecure (why : String)
  /-- The client is done with the connection. -/
  | stop

inductive Action where
  /-- Bytes of the start-up, of authentication, or `Terminate`. -/
  | send (bytes : ByteArray)
  /-- The bytes of the request numbered `id`. -/
  | query (id : Nat) (bytes : ByteArray)
  /-- Run the TLS handshake, and from then on send and receive through it. -/
  | startTls
  /-- Authenticated and ready for requests. -/
  | opened
  | reply (id : Nat) (reply : Reply)
  | close (why : Closing)
  deriving DecidableEq

end Conn

structure Conn where
  phase : Conn.Phase := .startup
  status : TxStatus := .idle
  buffer : ByteArray := .empty
  /-- Where the next message starts in `buffer`. -/
  pos : Nat := 0
  /-- The requests sent whose replies are not complete, oldest first. -/
  queue : List Conn.Pending := []
  /-- What the TLS handshake gave to bind SCRAM to. -/
  endPoint : Option ByteArray := none

namespace Conn

instance (s : String) : Decidable (Named s) := inferInstanceAs (Decidable (Plain s ∧ s ≠ ""))

instance : DecidablePred ValueOk
  | none => isTrue trivial
  | some v => inferInstanceAs (Decidable (v.size < 0x80000000))

instance : DecidablePred Frontend.Ok
  | .startup params => inferInstanceAs (Decidable (∀ p ∈ params, Named p.1 ∧ Plain p.2))
  | .password p => inferInstanceAs (Decidable (Plain p))
  | .saslInitial m d => inferInstanceAs (Decidable (Plain m ∧ d.size < 0x80000000))
  | .saslResponse _ => isTrue trivial
  | .query sql => inferInstanceAs (Decidable (Plain sql))
  | .parse st sql types =>
    inferInstanceAs (Decidable (Plain st ∧ Plain sql ∧ types.length < 65536 ∧ ∀ t ∈ types, t < 4294967296))
  | .bind portal st formats params results =>
    inferInstanceAs (Decidable (Plain portal ∧ Plain st ∧ (formats.length < 65536 ∧ ∀ f ∈ formats, f < 65536)
      ∧ (params.length < 65536 ∧ ∀ v ∈ params, ValueOk v)
      ∧ (results.length < 65536 ∧ ∀ f ∈ results, f < 65536)))
  | .describe _ name => inferInstanceAs (Decidable (Plain name))
  | .execute portal rows => inferInstanceAs (Decidable (Plain portal ∧ rows < 4294967296))
  | .sync => isTrue trivial
  | .terminate => isTrue trivial

/-- A message the server reads back as sent (`Frontend.decode_encode`) and within the bound. -/
def fits (cfg : Config) (m : Frontend) : Bool :=
  decide m.Ok && m.body.length + 4 ≤ cfg.message_max && m.body.length + 4 < 4294967296

def Request.messages : Request → List Frontend
  | .begin isolation => [.query ("BEGIN ISOLATION LEVEL " ++ isolation.sql)]
  | .commit => [.query "COMMIT"]
  | .rollback => [.query "ROLLBACK"]
  | .statement s =>
    [.parse "" s.sql [], .bind "" "" [] (s.params.map (·.map String.toUTF8)) [], .describe true "",
      .execute "" 0, .sync]

def Request.encode (r : Request) : ByteArray :=
  (Request.messages r).foldl (fun acc m => acc ++ m.encode) .empty

variable (cfg : Config)

def valid (r : Request) : Bool := (Request.messages r).all (fits cfg)

def room (c : Conn) : Nat := cfg.message_max + 1 - (c.buffer.size - c.pos)

/-- Every request in flight is answered `unknown`, and the connection closes. -/
def fail (c : Conn) (why : Closing) : Conn × List Action :=
  ({ c with phase := .closed, queue := [] },
    c.queue.map (fun p => .reply p.id .unknown) ++ [.close why])

/-- What a request's reply is, from what the server sent for it and the state of the
transaction before (`before`) and after it. A `COMMIT` is committed only when the server answered
`COMMIT` without an error, from inside a transaction that had not failed, and is then idle. -/
def outcome (p : Pending) (before after : TxStatus) : Reply :=
  match p.error with
  | some fields => .error fields
  | none =>
    match p.kind with
    | .commit =>
      if p.tag = some "COMMIT" ∧ before = .inTx ∧ after = .idle then .committed else .rolledBack
    | .rollback => .rolledBack
    | _ =>
      if cfg.rows_max < p.count then .tooManyRows
      else .rows { columns := p.columns, rows := p.rows.reverse, tag := p.tag.getD "" }

def texts : List (Option ByteArray) → Option (List (Option String))
  | [] => some []
  | none :: rest => (texts rest).map (none :: ·)
  | some v :: rest => do
    let s ← String.fromUTF8? v
    let rest ← texts rest
    pure (some s :: rest)

/-- A message that is a part of the reply at the head of the queue. -/
def onReply (c : Conn) (p : Pending) (rest : List Pending) : Backend → Conn × List Action
  | .parseComplete | .bindComplete | .noData | .parameterDescription _ | .emptyQuery
  | .noticeResponse _ | .parameterStatus .. => (c, [])
  | .rowDescription columns => ({ c with queue := { p with columns := columns.map (·.name) } :: rest }, [])
  | .dataRow values =>
    if cfg.rows_max ≤ p.count then ({ c with queue := { p with count := p.count + 1 } :: rest }, [])
    else
      match texts values with
      | some row => ({ c with queue := { p with rows := row :: p.rows, count := p.count + 1 } :: rest }, [])
      | none => fail c .protocol
  | .commandComplete tag => ({ c with queue := { p with tag := some tag } :: rest }, [])
  | .errorResponse fields => ({ c with queue := { p with error := some fields } :: rest }, [])
  | .readyForQuery status =>
    ({ c with queue := rest, status }, [.reply p.id (outcome cfg p c.status status)])
  | _ => fail c .protocol

/-- Whether the nonce can be sent in SCRAM's first message. -/
def nonceOk (nonce : String) : Bool :=
  !nonce.isEmpty && nonce.toList.all fun ch => '!' ≤ ch && ch ≤ '~' && ch != ','

/-- Whether the server must prove it knows the password by SCRAM before the connection opens. -/
def Config.scramOnly (cfg : Config) : Bool := cfg.requireScram && cfg.password.isSome

/-- SCRAM without channel binding, if it may be: `y` with TLS when the server did not offer
binding, else `n`. -/
def unbound (mechanisms : List String) : Option Scram.Binding :=
  if cfg.channelBinding = .require ∨ Scram.mechanism ∉ mechanisms then none
  else if cfg.encryption ≠ .plain ∧ cfg.channelBinding = .prefer
      ∧ Scram.mechanismPlus ∉ mechanisms then some .unoffered
  else some .none

/-- The channel binding to answer the server's mechanisms with, if any may be: bound to the
certificate's hash whenever there is TLS, the server offers it and it is not disabled. -/
def choose (c : Conn) (mechanisms : List String) : Option Scram.Binding :=
  match c.endPoint with
  | some hash =>
    if cfg.encryption ≠ .plain ∧ cfg.channelBinding ≠ .disable ∧ Scram.mechanismPlus ∈ mechanisms
    then some (.endPoint hash)
    else unbound cfg mechanisms
  | none => unbound cfg mechanisms

/-- The server asks how to authenticate. -/
def onAuth (c : Conn) : Backend → Conn × List Action
  | .authOk => if cfg.scramOnly then fail c .signature else ({ c with phase := .authed }, [])
  | .authCleartext =>
    match cfg.password with
    | some password =>
      if cfg.allowCleartext && !cfg.requireScram then
        ({ c with phase := .password }, [.send (Frontend.password password).encode])
      else fail c .method
    | none => fail c .method
  | .authMd5 salt =>
    match cfg.password with
    | some password =>
      if cfg.allowMd5 && !cfg.requireScram then
        ({ c with phase := .password },
          [.send (Frontend.password (md5Answer cfg.user password salt)).encode])
      else fail c .method
    | none => fail c .method
  | .authSasl mechanisms =>
    match cfg.password with
    | some _ =>
      if !nonceOk cfg.nonce then fail c .invalid
      else
        match choose cfg c mechanisms with
        | some b =>
          ({ c with phase := .sasl b },
            [.send (Frontend.saslInitial b.mechanism (Scram.first b "" cfg.nonce).toUTF8).encode])
        | none => fail c .method
    | none => fail c .method
  | .errorResponse fields => fail c (.server fields)
  | .noticeResponse _ => (c, [])
  | _ => fail c .protocol

def onSasl (c : Conn) (binding : Scram.Binding) : Backend → Conn × List Action
  | .authSaslContinue data =>
    match String.fromUTF8? data, cfg.password with
    | some serverFirst, some password =>
      match Scram.respond binding "" password cfg.nonce serverFirst cfg.iterations_max with
      | .ok (final, signature) =>
        ({ c with phase := .saslFinal signature }, [.send (Frontend.saslResponse final.toUTF8).encode])
      | .error why => fail c (.scram why)
    | _, _ => fail c .protocol
  | .errorResponse fields => fail c (.server fields)
  | .noticeResponse _ => (c, [])
  | .authOk => fail c .signature
  | _ => fail c .protocol

def onSaslFinal (c : Conn) (signature : ByteArray) : Backend → Conn × List Action
  | .authSaslFinal data =>
    match String.fromUTF8? data with
    | some final => if Scram.verify signature final then ({ c with phase := .saslDone }, []) else fail c .signature
    | none => fail c .signature
  | .errorResponse fields => fail c (.server fields)
  | .noticeResponse _ => (c, [])
  | .authOk => fail c .signature
  | _ => fail c .protocol

/-- What one message from the server does, in the phase the connection is in. -/
def onMessage (c : Conn) (m : Backend) : Conn × List Action :=
  match c.phase with
  | .startup => onAuth cfg c m
  | .password =>
    match m with
    | .authOk => ({ c with phase := .authed }, [])
    | .errorResponse fields => fail c (.server fields)
    | .noticeResponse _ => (c, [])
    | _ => fail c .protocol
  | .sasl binding => onSasl cfg c binding m
  | .saslFinal signature => onSaslFinal c signature m
  | .saslDone =>
    match m with
    | .authOk => ({ c with phase := .authed }, [])
    | .errorResponse fields => fail c (.server fields)
    | .noticeResponse _ => (c, [])
    | _ => fail c .protocol
  | .authed =>
    match m with
    | .parameterStatus .. | .backendKeyData .. | .noticeResponse _ => (c, [])
    | .readyForQuery status => ({ c with phase := .ready, status }, [.opened])
    | .errorResponse fields => fail c (.server fields)
    | _ => fail c .protocol
  | .ready =>
    match c.queue with
    | p :: rest => onReply cfg c p rest m
    | [] =>
      match m with
      | .noticeResponse _ | .parameterStatus .. => (c, [])
      | .errorResponse fields => fail c (.server fields)
      | _ => fail c .protocol
  | .closed => (c, [])
  | .sslRequest | .handshake => fail c .protocol

/-- Every message whole in the buffer, in turn. Each takes at least five bytes, so `fuel` one
more than the bytes there is enough. -/
def drain : Nat → Conn → Conn × List Action
  | 0, c => (c, [])
  | fuel + 1, c =>
    if c.phase = .closed then (c, [])
    else
      match Frame.read cfg.message_max c.buffer c.pos with
      | .more => (c, [])
      | .refuse => fail c .protocol
      | .done tag body next =>
        match Backend.decode tag body with
        | none => fail c .protocol
        | some m =>
          let (c, first) := onMessage cfg { c with pos := next } m
          let (c, later) := drain fuel c
          (c, first ++ later)

/-- Consumed bytes are dropped here, when more arrive. -/
def receive (bytes : ByteArray) (c : Conn) : Conn :=
  { c with buffer := (if c.pos = 0 then c.buffer else c.buffer.extract c.pos c.buffer.size) ++ bytes
           pos := 0 }

def submit (id : Nat) (r : Request) (c : Conn) : Conn × List Action :=
  if c.phase ≠ .ready then (c, [.reply id (.refused .notReady)])
  else if cfg.inflight_max ≤ c.queue.length then (c, [.reply id (.refused .busy)])
  else if !valid cfg r then (c, [.reply id (.refused .invalid)])
  else ({ c with queue := c.queue ++ [{ id, kind := Request.kind r }] }, [.query id (Request.encode r)])

/-- The start-up message, with `client_encoding` UTF-8, so that text is UTF-8 both ways. -/
def startup : Frontend :=
  .startup [("user", cfg.user), ("database", cfg.database), ("client_encoding", "UTF8")]

/-- `SSLRequest`: a length of 8 and the code 80877103. -/
def sslRequest : ByteArray := ⟨(putU32 8 ++ putU32 80877103).toArray⟩

/-- The ALPN protocol of PostgreSQL. -/
def alpn : ByteArray := "postgresql".toUTF8

/-- The connection as it starts: the start-up message, or first `SSLRequest`, or first TLS. -/
def start : Conn × List Action :=
  if !fits cfg (startup cfg) then ({ phase := .closed }, [.close .invalid])
  else
    match cfg.encryption with
    | .plain => ({}, [.send (startup cfg).encode])
    | .negotiated => ({ phase := .sslRequest }, [.send sslRequest])
    | .direct => ({ phase := .handshake }, [.startTls])

/-- Bytes before TLS: the server's answer to `SSLRequest`, one byte, `S` or `N`, and none during
the handshake. Bytes after an `S` were sent before the handshake, in the clear, and are not
taken as the server's (CVE-2021-23222). -/
def beforeTls (c : Conn) (bytes : ByteArray) : Conn × List Action :=
  if c.phase = .handshake then if bytes.isEmpty then (c, []) else fail c .protocol
  else
    match bytes.data.toList with
    | [] => (c, [])
    | [83] => ({ c with phase := .handshake }, [.startTls])
    | 78 :: _ => fail c .refusedTls
    | _ => fail c .protocol

/-- With direct TLS, the server must have chosen `postgresql`, so that a server of another
protocol that takes the certificate is not spoken to; otherwise it chose it or none. -/
def alpnOk (selected : ByteArray) : Bool :=
  match cfg.encryption with
  | .direct => selected == alpn
  | _ => selected.isEmpty || selected == alpn

/-- The handshake is done: only now is the start-up sent. -/
def secure (c : Conn) (endPoint : Option ByteArray) (selected : ByteArray) : Conn × List Action :=
  if c.phase ≠ .handshake then fail c .protocol
  else if !alpnOk cfg selected then fail c .alpn
  else ({ c with phase := .startup, endPoint }, [.send (startup cfg).encode])

/-- Whether the connection is before TLS: nothing but `SSLRequest` has been sent. -/
def Phase.beforeTls : Phase → Bool
  | .sslRequest | .handshake => true
  | _ => false

/-- Whether a connection may be handed to another client: open, outside a transaction, and with
no request in flight. -/
def reusable (c : Conn) : Bool :=
  c.phase == .ready && c.status == .idle && c.queue.isEmpty

/-- What the connection does about one thing that happened. A closed connection refuses every
request and does nothing else. More bytes than `room` closes it. -/
def step (c : Conn) (e : Event) : Conn × List Action :=
  match e with
  | .submit id r => submit cfg id r c
  | .received bytes =>
    if c.phase = .closed then (c, [])
    else if c.phase.beforeTls then beforeTls c bytes
    else if room cfg c < bytes.size then fail c .protocol
    else
      let c := receive bytes c
      drain cfg (c.buffer.size - c.pos + 1) c
  | .ended => if c.phase = .closed then (c, []) else fail c .ended
  | .broken => if c.phase = .closed then (c, []) else fail c .broken
  | .secured endPoint selected => if c.phase = .closed then (c, []) else secure cfg c endPoint selected
  | .insecure why => if c.phase = .closed then (c, []) else fail c (.tls why)
  | .stop =>
    if c.phase = .closed then (c, [])
    else if c.phase.beforeTls then fail c .stopped
    else
      let (c, actions) := fail c .stopped
      (c, .send Frontend.terminate.encode :: actions)

/-- The connection after `events`, and what it asked for. -/
def run (c : Conn) : List Event → Conn × List Action
  | [] => (c, [])
  | e :: rest =>
    let (c, first) := step cfg c e
    let (c, later) := run c rest
    (c, first ++ later)

end Conn

end Lanes.Postgres
