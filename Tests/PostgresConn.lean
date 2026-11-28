/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
A connection to PostgreSQL against a server that does what it may. The server is a model written
here: it reads what the client sends with `Frontend.decode`, authenticates it by trust, MD5 or
SCRAM (or answers SCRAM with a signature that is not the password's, or skips it to a client that
requires it), runs a transaction's statements (one returns rows, one fails, one succeeds) and
keeps which `COMMIT`s it committed. Over TLS it answers `SSLRequest`, or refuses it, and the
handshake is done or fails at any moment after the client starts it; it offers
`SCRAM-SHA-256-PLUS` and checks the client's proof with the hash of its own certificate, so a
client that reached it through a relay with another certificate, or to which a relay hid the
offer, is refused.
What it writes reaches the client in pieces of one, seven or all the bytes, only while the
connection takes them; the server may leave at any moment, losing what it has not delivered; the
client submits its requests whenever it is open, pipelining up to the bound, and may stop. The
search explores every order of these and checks what the connection promises (rule 5.1),
before and beside the proofs of `Lanes/Lib/Postgres/ConnSound.lean`.
-/

namespace Tests.PostgresConn

open Lanes Lanes.Check Lanes.Postgres Lanes.Postgres.Conn

inductive Method where
  | trust
  | md5
  | scram
  /-- SCRAM, but the server's last message carries a signature that is not the password's. -/
  | forged
  /-- `AuthenticationOk` at once, as trust, to a client that requires SCRAM. -/
  | impostor
  /-- TLS, and SCRAM bound to the server's certificate. -/
  | tls
  /-- `N` to the client's `SSLRequest`. -/
  | refusing
  /-- TLS through a relay that holds another certificate, valid for the name. -/
  | relayed
  /-- TLS through a relay that hides `SCRAM-SHA-256-PLUS` from the client. -/
  | stripped
  deriving DecidableEq, Hashable, Repr

def Method.encrypted : Method → Bool
  | .tls | .refusing | .relayed | .stripped => true
  | _ => false

/-- The hash of the server's certificate. -/
def serverHash : ByteArray := ⟨#[1, 2, 3]⟩

/-- What the client's handshake gives as the certificate's hash. -/
def Method.endPoint : Method → ByteArray
  | .relayed => ⟨#[9, 9, 9]⟩
  | _ => serverHash

def password : String := "pw"

def nonce : String := "cn"

def salt : ByteArray := ⟨#[1, 2, 3, 4]⟩

def serverFirst : String := "r=" ++ nonce ++ "sv,s=" ++ Base64.encode .std salt ++ ",i=2"

def cfg : Config :=
  { user := "u", database := "d", password := some password, nonce, message_max := 96,
    inflight_max := 2, iterations_max := 4 }

/-- A server of trust or MD5 is reached only by a client that lets it skip SCRAM. -/
def cfgOf : Method → Config
  | .trust | .md5 => { cfg with requireScram := false, allowMd5 := true }
  | .scram | .forged | .impostor => cfg
  | .tls | .refusing | .relayed | .stripped => { cfg with encryption := .negotiated }

inductive ServerPhase where
  | sslRequest
  | startup
  | password
  | saslInitial
  | saslResponse
  | ready
  deriving DecidableEq, Hashable, Repr

structure Server where
  method : Method
  phase : ServerPhase := .startup
  status : TxStatus := .idle
  /-- The SQL of the statement whose `Sync` has not come yet. -/
  statement : Option String := none
  /-- How many requests it has answered. -/
  answered : Nat := 0
  /-- The numbers, in the order answered, of the requests that committed. -/
  commits : List Nat := []
  /-- The binding the client's first SCRAM message asked for, as the server checks it. -/
  binding : Scram.Binding := .none
  deriving DecidableEq, Hashable

def frame (m : Backend) : ByteArray := m.encode

def ready (status : TxStatus) : ByteArray := frame (.readyForQuery status)

def errorWith (code : String) : ByteArray :=
  frame (.errorResponse [{ code := 83, value := "ERROR" }, { code := 67, value := code }])

def welcome : ByteArray :=
  frame .authOk ++ frame (.parameterStatus "server_version" "16") ++ frame (.backendKeyData 7 9)
    ++ ready .idle

/-- What the server makes of the GS2 header of SCRAM's first message: the binding it then checks
the proof with, its own certificate's hash for `p`; none if it refuses. A server that offers
binding refuses `y`, which says the client saw no offer. -/
def bindingOf (offers : Bool) (data : ByteArray) : Option Scram.Binding :=
  let text := (String.fromUTF8? data).getD ""
  if text.startsWith "p=tls-server-end-point,," then if offers then some (.endPoint serverHash) else none
  else if text.startsWith "y,," then if offers then none else some .unoffered
  else if text.startsWith "n,," then some .none
  else none

/-- What the server does with one message from the client: its new state and the bytes it
writes. -/
def serve (s : Server) (m : Frontend) : Server × ByteArray :=
  match s.phase, m with
  | .startup, .startup _ =>
    match s.method with
    | .trust | .impostor => ({ s with phase := .ready }, welcome)
    | .md5 => ({ s with phase := .password }, frame (.authMd5 salt))
    | .scram | .forged => ({ s with phase := .saslInitial }, frame (.authSasl ["SCRAM-SHA-256"]))
    | .tls | .refusing | .relayed =>
      ({ s with phase := .saslInitial }, frame (.authSasl ["SCRAM-SHA-256-PLUS", "SCRAM-SHA-256"]))
    | .stripped => ({ s with phase := .saslInitial }, frame (.authSasl ["SCRAM-SHA-256"]))
  | .password, .password p =>
    if p == md5Answer "u" password salt then ({ s with phase := .ready }, welcome)
    else ({ s with phase := .startup }, errorWith "28P01")
  | .saslInitial, .saslInitial _ data =>
    match bindingOf s.method.encrypted data with
    | some binding =>
      ({ s with phase := .saslResponse, binding }, frame (.authSaslContinue serverFirst.toUTF8))
    | none => ({ s with phase := .startup }, errorWith "28000")
  | .saslResponse, .saslResponse data =>
    match Scram.respond s.binding "" password nonce serverFirst 4 with
    | .ok (final, signature) =>
      if data != final.toUTF8 then ({ s with phase := .startup }, errorWith "28P01")
      else
        let signature := if s.method == .forged then Sha256.hash signature else signature
        ({ s with phase := .ready },
          frame (.authSaslFinal ("v=" ++ Base64.encode .std signature).toUTF8) ++ welcome)
    | .error _ => (s, .empty)
  | .ready, .query sql =>
    let s' := { s with answered := s.answered + 1 }
    if sql.startsWith "BEGIN" then
      ({ s' with status := if s.status == .idle then .inTx else s.status },
        frame (.commandComplete "BEGIN") ++ ready (if s.status == .idle then .inTx else s.status))
    else if sql == "COMMIT" then
      match s.status with
      | .inTx => ({ s' with status := .idle, commits := s.commits ++ [s.answered] },
          frame (.commandComplete "COMMIT") ++ ready .idle)
      | .failed => ({ s' with status := .idle }, frame (.commandComplete "ROLLBACK") ++ ready .idle)
      | .idle => (s', frame (.noticeResponse [{ code := 77, value := "no transaction" }])
          ++ frame (.commandComplete "COMMIT") ++ ready .idle)
    else ({ s' with status := .idle }, frame (.commandComplete "ROLLBACK") ++ ready .idle)
  | .ready, .parse _ sql _ => ({ s with statement := some sql }, frame .parseComplete)
  | .ready, .bind .. => (s, frame .bindComplete)
  | .ready, .describe .. | .ready, .execute .. => (s, .empty)
  | .ready, .sync =>
    let s' := { s with answered := s.answered + 1, statement := none }
    if s.status == .failed then (s', errorWith "25P02" ++ ready .failed)
    else
      match s.statement with
      | some "rows" =>
        (s', frame (.rowDescription [{ name := "v", type := 25, size := 65535, modifier := 4294967295 }])
          ++ frame (.dataRow [some "a".toUTF8]) ++ frame (.dataRow [none])
          ++ frame (.commandComplete "SELECT 2") ++ frame (.parameterStatus "TimeZone" "UTC")
          ++ ready s.status)
      | some "boom" =>
        let status := if s.status == .inTx then .failed else .idle
        ({ s' with status }, frame .noData ++ errorWith "22012" ++ ready status)
      | _ => (s', frame .noData ++ frame (.commandComplete "OK") ++ ready s.status)
  | _, .terminate => (s, .empty)
  | _, _ => (s, errorWith "08P01")

/-- The server's answer to `SSLRequest`. -/
def answerSsl (s : Server) : Server × ByteArray :=
  if s.method == .refusing then ({ s with phase := .startup }, ⟨#[78]⟩)
  else ({ s with phase := .startup }, ⟨#[83]⟩)

/-- What the server expects in its phase. -/
def expect : ServerPhase → Frontend.Expect
  | .sslRequest | .startup => .startup
  | .password => .password
  | .saslInitial => .saslInitial
  | .saslResponse => .saslResponse
  | .ready => .query

/-- The client's messages in one write, as the server reads them. -/
def messages (s : Server) (bytes : ByteArray) : List Frontend :=
  if s.phase == .startup || s.phase == .sslRequest then (Frontend.decode .startup bytes).toList
  else go bytes.size 0
where
  go : Nat → Nat → List Frontend
    | 0, _ => []
    | fuel + 1, pos =>
      match Frame.read 1048576 bytes pos with
      | .done _ _ next =>
        (Frontend.decode (expect s.phase) (bytes.extract pos next)).toList ++ go fuel next
      | _ => []

def serveAll (s : Server) (bytes : ByteArray) : Server × ByteArray :=
  if s.phase == .sslRequest then if bytes == Conn.sslRequest then answerSsl s else (s, .empty)
  else
    (messages s bytes).foldl (fun (s, out) m => let (s, more) := serve s m; (s, out ++ more)) (s, .empty)

structure World where
  conn : Conn
  server : Server
  /-- What the server wrote; `delivered` bytes of it have reached the client. -/
  wire : ByteArray := .empty
  delivered : Nat := 0
  /-- The requests still to submit. -/
  script : List Request
  submitted : List (Nat × Request) := []
  queried : List Nat := []
  replies : List (Nat × Reply) := []
  opened : Bool := false
  closes : Nat := 0
  gone : Bool := false
  stopped : Bool := false
  /-- An action came after the connection closed. -/
  stray : Bool := false
  /-- The IO has said the handshake is done. -/
  secured : Bool := false
  /-- What was sent before. -/
  plain : List ByteArray := []
  pieced : Bool := false
  wasFull : Bool := false

def phaseCode : Phase → Nat × ByteArray
  | .sslRequest => (8, .empty)
  | .handshake => (9, .empty)
  | .startup => (0, .empty)
  | .password => (1, .empty)
  | .sasl b => (2, b.data)
  | .saslFinal sig => (3, sig)
  | .saslDone => (4, .empty)
  | .authed => (5, .empty)
  | .ready => (6, .empty)
  | .closed => (7, .empty)

def key (w : World) :=
  ((phaseCode w.conn.phase, w.conn.status, w.conn.buffer, w.conn.pos, w.conn.queue),
    (w.server, w.wire.size, w.delivered, w.script.length, w.queried, w.replies),
    (w.opened, w.closes, w.gone, w.stopped, w.stray, w.pieced, w.wasFull, w.secured, w.plain))

instance : BEq World := ⟨fun a b => key a == key b⟩
instance : Hashable World := ⟨fun w => hash (key w)⟩

def perform (w : World) : Action → World
  | .send bytes =>
    let (server, out) := serveAll w.server bytes
    { w with server, wire := w.wire ++ out, plain := if w.secured then w.plain else w.plain ++ [bytes] }
  | .query id bytes =>
    let (server, out) := serveAll w.server bytes
    { w with server, wire := w.wire ++ out, queried := w.queried ++ [id] }
  | .opened => { w with opened := true }
  | .reply id r => { w with replies := w.replies ++ [(id, r)] }
  | .close _ => { w with closes := w.closes + 1 }
  | .startTls => w

def tell (w : World) (e : Event) : World :=
  let closed := w.conn.phase == .closed
  let (conn, actions) := w.conn.step (cfgOf w.server.method) e
  let notRefusal := actions.any fun | .reply _ (.refused _) => false | _ => true
  let w := actions.foldl perform { w with conn, stray := w.stray || (closed && notRefusal) }
  { w with wasFull := w.wasFull || conn.queue.length == cfg.inflight_max }

def initial (method : Method) (script : List Request) : World :=
  let (conn, actions) := Conn.start (cfgOf method)
  let phase := if method.encrypted then .sslRequest else .startup
  actions.foldl perform { conn, server := { method, phase }, script }

def next (w : World) : List (String × World) :=
  if w.conn.phase == .closed then []
  else
    let left := w.wire.size - w.delivered
    let room := w.conn.room (cfgOf w.server.method)
    let deliveries := if w.gone then [] else
      [1, 7, 1000].filterMap fun piece =>
        let n := min piece (min room left)
        if n = 0 then none
        else
          let pieced := w.pieced || (w.conn.pos < w.conn.buffer.size && n < left)
          some ("deliver", tell { w with delivered := w.delivered + n, pieced }
            (.received (w.wire.extract w.delivered (w.delivered + n))))
    let submits := match w.script with
      | r :: rest =>
        if w.opened then
          let id := w.submitted.length
          [("submit", tell { w with script := rest, submitted := w.submitted ++ [(id, r)] } (.submit id r))]
        else []
      | [] => []
    let handshake :=
      if w.conn.phase == .handshake && !w.secured && !w.gone then
        [("the handshake is done",
            tell { w with secured := true } (.secured (some w.server.method.endPoint) .empty)),
          ("the handshake fails", tell w (.insecure "refused"))]
      else []
    deliveries ++ submits ++ handshake
      ++ (if w.gone then [] else [("the server leaves", tell { w with gone := true } .ended)])
      ++ (if w.stopped then [] else [("the client stops", tell { w with stopped := true } .stop)])

def model (method : Method) (script : List Request) : Model World String where
  init := [initial method script]
  next := next

def answers (w : World) : List Nat :=
  w.replies.filterMap fun | (_, .refused _) => none | (id, _) => some id

/-- The number, among the requests the server answered, of the request numbered `id`. -/
def served (w : World) (id : Nat) : Option Nat := w.queried.idxOf? id

def committedByServer (w : World) (id : Nat) : Bool :=
  (served w id).any (w.server.commits.contains ·)

def properties (method : Method) : List (Property World) :=
  [ .always "replies answer the requests sent, in the order they were sent" fun w =>
      answers w == w.queried.take (answers w).length,
    .always "each request is answered at most once" fun w =>
      (w.replies.map (·.1)).Nodup,
    .always "a request is sent only once the connection is open" fun w =>
      w.queried.isEmpty || w.opened,
    .always "committed only when the server committed it" fun w =>
      w.replies.all fun (id, r) => r != .committed || committedByServer w id,
    .always "a commit the server made and whose reply arrived is reported committed" fun w =>
      w.replies.all fun (id, r) => !committedByServer w id || r == .committed || r == .unknown,
    .always "a closed connection has answered every request submitted" fun w =>
      w.conn.phase != .closed || w.submitted.all fun (id, _) => w.replies.any (·.1 == id),
    .always "the connection closes once and does nothing after" fun w =>
      w.closes ≤ 1 && !w.stray,
    .always "the buffer stays within its bound" fun w =>
      w.conn.pos ≤ w.conn.buffer.size && w.conn.buffer.size - w.conn.pos ≤ cfg.message_max + 1,
    .always "no more requests are in flight than the bound" fun w =>
      w.conn.queue.length ≤ cfg.inflight_max,
    .always "a server that does not prove the password is never trusted" fun w =>
      (method != .forged && method != .impostor) || !w.opened,
    .always "with TLS, nothing but SSLRequest is sent before the handshake is done" fun w =>
      !method.encrypted || w.plain.all (· == Conn.sslRequest),
    .always "with TLS, the connection opens only once the handshake is done" fun w =>
      !method.encrypted || !w.opened || w.secured,
    .always "a server that refuses TLS, or a relay, is never opened" fun w =>
      (method != .refusing && method != .relayed && method != .stripped) || !w.opened ]

def sometimes (method : Method) (failing : Bool) : List (Property World) :=
  if method == .forged || method == .impostor || method == .refusing || method == .relayed
      || method == .stripped then
    [.sometimes "the server that did not prove the password, or refused TLS, closes the connection" fun w =>
      w.conn.phase == .closed && !w.gone]
  else
    [ .sometimes "the connection opens" (·.opened),
      .sometimes "a reply is read from more than one piece" (·.pieced),
      .sometimes "a reply is lost: the connection ends with a request answered unknown" fun w =>
        w.replies.any (·.2 == .unknown) ] ++
    if failing then
      [ .sometimes "a commit in a failed transaction is answered rolled back" fun w =>
          w.replies.any (·.2 == .rolledBack),
        .sometimes "rows are read" fun w => w.replies.any fun | (_, .rows r) => r.rows.length == 2 | _ => false ]
    else
      [ .sometimes "a commit is answered committed" fun w => w.replies.any (·.2 == .committed),
        .sometimes "the server committed and the reply was lost" fun w =>
          w.replies.any fun (id, r) => r == .unknown && committedByServer w id,
        .sometimes "the requests in flight reach the bound" (·.wasFull) ]

def committing : List Request := [.begin .serializable, .statement { sql := "ok" }, .commit]

/-- A transaction that fails and its `COMMIT`, rows, and a `COMMIT` with no transaction, which the
server answers with the tag `COMMIT` and which commits nothing. -/
def failing : List Request := [.begin .readCommitted, .statement { sql := "boom" }, .commit,
  .statement { sql := "rows" }, .commit]

@[never_extract] def report (method : Method) (script : List Request) (fails : Bool) :=
  search (model method script) (properties method ++ sometimes method fails) {} id

def checks : IO (List (String × Bool)) := do
  let cases : List (String × Method × List Request × Bool) :=
    [ ("trust, a transaction that commits", .trust, committing, false),
      ("trust, a transaction that fails, then rows", .trust, failing, true),
      ("MD5, a transaction that commits", .md5, committing, false),
      ("SCRAM, a transaction that commits", .scram, committing, false),
      ("SCRAM with a forged signature", .forged, committing, false),
      ("trust to a client that requires SCRAM", .impostor, committing, false),
      ("TLS and SCRAM-SHA-256-PLUS, a transaction that commits", .tls, committing, false),
      ("TLS refused with N", .refusing, committing, false),
      ("TLS through a relay with another certificate", .relayed, committing, false),
      ("TLS through a relay that hides SCRAM-SHA-256-PLUS", .stripped, committing, false) ]
  return cases.map fun (name, method, script, fails) =>
    let r := report method script fails
    (s!"postgres conn: {name}: every promise holds against a server that may do anything", r.ok)

end Tests.PostgresConn
