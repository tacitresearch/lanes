/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Lib.Postgres.Message
public import Lanes.Lib.Postgres.Scram

/-!
# A connection to PostgreSQL, as a pure function

The IO that runs a connection (`Lanes.Lib.Postgres.IO.Client`) tells it what happened
(`Postgres.Conn.Event`: bytes received, the end of them, a broken socket, a request to send, `stop`)
and does what it answers (`Postgres.Conn.Action`: send bytes, send a request's bytes, report the
connection open, answer a request, close), and asks it how many bytes it takes (`Conn.room`).
Everything else is decided here: the start-up, which authentication to answer and how, whether
the server proved it knows the password, what the bytes received are as messages, which request
each reply answers, and what a reply to `COMMIT` means.

Requests are sent only once the connection is open, at most `inflight_max` at a time, each
ended by its own `Sync` (or a simple query), so the server answers each with one
`ReadyForQuery`, and replies are matched to requests in the order they were sent. The state of
the transaction is the one the last `ReadyForQuery` reported. A connection that ends, breaks or
receives what the protocol does not allow answers every request in flight with `unknown`, and
closes (rule 3.1).

What it promises is proved in `Lanes/Lib/Postgres/ConnSound.lean`, and model-checked against a
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
  deriving DecidableEq, Repr

namespace Conn

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
  allowMd5 : Bool := true
  /-- A message's length, counting its four bytes of length. -/
  message_max : Nat := 1048576
  rows_max : Nat := 100000
  inflight_max : Nat := 16
  /-- SCRAM's iteration count, which the server chooses and the client pays for. -/
  iterations_max : Nat := 100000

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
  /-- The start-up is sent; the server is to say how to authenticate. -/
  | startup
  /-- A password or its digest is sent. -/
  | password
  /-- SCRAM's first message is sent. -/
  | sasl
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
  /-- The client is done with the connection. -/
  | stop

inductive Action where
  /-- Bytes of the start-up, of authentication, or `Terminate`. -/
  | send (bytes : ByteArray)
  /-- The bytes of the request numbered `id`. -/
  | query (id : Nat) (bytes : ByteArray)
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

/-- The server asks how to authenticate. -/
def onAuth (c : Conn) : Backend → Conn × List Action
  | .authOk => ({ c with phase := .authed }, [])
  | .authCleartext =>
    match cfg.password with
    | some password =>
      if cfg.allowCleartext then ({ c with phase := .password }, [.send (Frontend.password password).encode])
      else fail c .method
    | none => fail c .method
  | .authMd5 salt =>
    match cfg.password with
    | some password =>
      if cfg.allowMd5 then
        ({ c with phase := .password },
          [.send (Frontend.password (md5Answer cfg.user password salt)).encode])
      else fail c .method
    | none => fail c .method
  | .authSasl mechanisms =>
    match cfg.password with
    | some _ =>
      if !nonceOk cfg.nonce then fail c .invalid
      else if Scram.mechanism ∈ mechanisms then
        ({ c with phase := .sasl },
          [.send (Frontend.saslInitial Scram.mechanism (Scram.first "" cfg.nonce).toUTF8).encode])
      else fail c .method
    | none => fail c .method
  | .errorResponse fields => fail c (.server fields)
  | .noticeResponse _ => (c, [])
  | _ => fail c .protocol

def onSasl (c : Conn) : Backend → Conn × List Action
  | .authSaslContinue data =>
    match String.fromUTF8? data, cfg.password with
    | some serverFirst, some password =>
      match Scram.respond "" password cfg.nonce serverFirst cfg.iterations_max with
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
  | .sasl => onSasl cfg c m
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

/-- The connection as it starts: the start-up message, with `client_encoding` UTF-8, so that
text is UTF-8 both ways. -/
def start : Conn × List Action :=
  let m := Frontend.startup [("user", cfg.user), ("database", cfg.database), ("client_encoding", "UTF8")]
  if fits cfg m then ({}, [.send m.encode])
  else ({ phase := .closed }, [.close .invalid])

/-- What the connection does about one thing that happened. A closed connection refuses every
request and does nothing else. More bytes than `room` closes it. -/
def step (c : Conn) (e : Event) : Conn × List Action :=
  match e with
  | .submit id r => submit cfg id r c
  | .received bytes =>
    if c.phase = .closed then (c, [])
    else if room cfg c < bytes.size then fail c .protocol
    else
      let c := receive bytes c
      drain cfg (c.buffer.size - c.pos + 1) c
  | .ended => if c.phase = .closed then (c, []) else fail c .ended
  | .broken => if c.phase = .closed then (c, []) else fail c .broken
  | .stop =>
    if c.phase = .closed then (c, [])
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
