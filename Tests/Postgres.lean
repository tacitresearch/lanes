/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Services.Postgres.Conn
import Lanes.Services.Postgres.Table
import Lanes.Lib.Crypto.Certificate

/-!
PostgreSQL's client against what a real server sent. `Tests/Postgres/psql-*.txt` are sessions of
`psql` (libpq 16) with PostgreSQL 16, recorded by a proxy between them; `Tests/Postgres/lanes-*.txt`
are sessions of this client with the same server (`Tests/PostgresLive.lean` records them). Each
line is `C` or `S`, for what the client or the server wrote, and the bytes of one write in hex.

Every frame of every recording is read by `Frame.read` and decoded, and written again by the
encoders as the same bytes: a differential test of the decoders and the encoders against libpq
and the server. The authentication libpq computed is computed again, from the same password,
nonce and salt, and the connection is replayed through `Conn.step` with what the server sent,
for the replies it must give. The hash functions are tested against their RFCs' vectors.
-/

namespace Tests.Postgres

open Lanes Lanes.Postgres

def hex (s : String) : ByteArray := (Bytes.unhex? s).getD .empty

def recording (path : String) : IO (List (Bool × ByteArray)) := do
  let text ← IO.FS.readFile path
  return (text.splitOn "\n").filterMap fun line =>
    match line.splitOn " " with
    | [dir, bytes] => some (dir == "C", hex bytes)
    | _ => none

/-- The frames of one write, or `none` if it is not whole frames. -/
def frames (bytes : ByteArray) : Option (List (UInt8 × ByteArray × ByteArray)) :=
  go bytes.size 0
where
  go : Nat → Nat → Option (List (UInt8 × ByteArray × ByteArray))
    | 0, _ => none
    | fuel + 1, pos =>
      if pos = bytes.size then some []
      else
        match Frame.read 1073741824 bytes pos with
        | .done tag body next => (go fuel next).map ((tag, body, bytes.extract pos next) :: ·)
        | _ => none

/-- What the server expects next, from the last message it sent. -/
def expectAfter : Option Backend → Frontend.Expect
  | some .authCleartext | some (.authMd5 _) => .password
  | some (.authSasl _) => .saslInitial
  | some (.authSaslContinue _) => .saslResponse
  | _ => .query

/-- Every message of a recording, decoded; `none` where one is not read back or not written
again as the same bytes. -/
def decodeAll (writes : List (Bool × ByteArray)) : Option (List (Sum Frontend Backend)) :=
  go writes none true
where
  go : List (Bool × ByteArray) → Option Backend → Bool → Option (List (Sum Frontend Backend))
    | [], _, _ => some []
    | (true, bytes) :: rest, last, first => do
      let ms ← if first then
          (Frontend.decode .startup bytes).filter (·.encode == bytes) |>.map ([·])
        else
          (frames bytes).bind fun fs => fs.mapM fun (_, _, whole) =>
            (Frontend.decode (expectAfter last) whole).filter (·.encode == whole)
      return ms.map .inl ++ (← go rest last false)
    | (false, bytes) :: rest, _, first => do
      let fs ← frames bytes
      let ms ← fs.mapM fun (tag, body, whole) =>
        (Backend.decode tag body).filter (·.encode == whole)
      return ms.map .inr ++ (← go rest ms.getLast? first)

def frontends (ms : List (Sum Frontend Backend)) : List Frontend :=
  ms.filterMap fun | .inl m => some m | _ => none

def backends (ms : List (Sum Frontend Backend)) : List Backend :=
  ms.filterMap fun | .inr m => some m | _ => none

/-- The request a client message of `psql` stands for. -/
def requestOf : Frontend → Option Request
  | .query sql =>
    if sql.startsWith "BEGIN" then some (.begin .readCommitted)
    else if sql.startsWith "COMMIT" then some .commit
    else if sql.startsWith "ROLLBACK" then some .rollback
    else some (.statement { sql })
  | .parse _ sql _ => some (.statement { sql })
  | _ => none

/-- `psql`'s session replayed through `Conn.step`: each request `psql` sent submitted when
`psql` sent it, and each write of the server received as it came. -/
def replay (cfg : Conn.Config) (writes : List (Bool × ByteArray)) : List Conn.Action :=
  let (c, first) := Conn.start cfg
  let (_, _, actions) := writes.foldl (init := (c, 0, first)) fun (c, n, acc) (client, bytes) =>
    if client then
      match (frames bytes).bind fun fs => fs.head?.bind fun (_, _, w) => Frontend.decode .query w with
      | some m =>
        match requestOf m with
        | some r =>
          let (c, out) := c.step cfg (.submit n r)
          (c, n + 1, acc ++ out)
        | none => (c, n, acc)
      | none => (c, n, acc)
    else
      let (c, out) := c.step cfg (.received bytes)
      (c, n, acc ++ out)
  actions

def replies (actions : List Conn.Action) : List Reply :=
  actions.filterMap fun | .reply _ r => some r | _ => none

def sqlstate (r : Reply) : Option String :=
  match r with
  | .error fields => (fields.find? (·.code == 67)).map (·.value)
  | _ => none

def text (s : String) : Option String := some s

def trustReplies : List Reply := [
  .rows { columns := ["one", "nothing", "greeting"], rows := [[text "1", none, text "héllo, wörld"]]
          tag := "SELECT 1" },
  .rows { columns := ["answer", "echo"], rows := [[text "42", text "a 'quoted' value"]], tag := "SELECT 1" },
  .rows { columns := ["n", "label"], rows := [[text "1", text "row 1"], [text "2", text "row 2"],
          [text "3", text "row 3"]], tag := "SELECT 3" },
  .rows { tag := "BEGIN" },
  .rows { tag := "CREATE TABLE" },
  .rows { columns := ["id"], rows := [[text "1"]], tag := "INSERT 0 1" },
  .rows { columns := ["id", "title"], rows := [[text "1", text "buy milk"]], tag := "SELECT 1" },
  .committed,
  .rows { tag := "BEGIN" },
  .rolledBack,
  .rolledBack ]

def refusal : Except Scram.Refusal (String × ByteArray) → Option Scram.Refusal
  | .error why => some why
  | .ok _ => none

def vectorTests : List (String × Bool) :=
  let md5 (s : String) := Bytes.hex (Md5.hash s.toUTF8)
  [ ("postgres: MD5 gives RFC 1321's digests",
      md5 "" == "d41d8cd98f00b204e9800998ecf8427e" && md5 "a" == "0cc175b9c0f1b6a831c399e269772661"
        && md5 "abc" == "900150983cd24fb0d6963f7d28e17f72"
        && md5 "message digest" == "f96b697d7cb7938d525a2f31aaf161d0"
        && md5 "abcdefghijklmnopqrstuvwxyz" == "c3fcd3d76192e4007dfb496cca67e13b"
        && md5 (String.join (List.replicate 8 "1234567890")) == "57edf4a22be3c955ac49da2e2107b67a"),
    ("postgres: PBKDF2-HMAC-SHA-256 gives RFC 7914's and hashlib's keys",
      Bytes.hex (Pbkdf2.derive "passwd".toUTF8 "salt".toUTF8 1 64)
          == "55ac046e56e3089fec1691c22544b605f94185216dde0465e68b9d57c20dacbc49ca9cccf179b645991664b39d77ef317c71b845b1e30bd509112041d3a19783"
        && Bytes.hex (Pbkdf2.derive "password".toUTF8 "salt".toUTF8 4096 32)
          == "c5e478d59288c841aa530db6845c4c8d962893a001ce4e11a4963873aa98134a"),
    ("postgres: SCRAM-SHA-256 gives RFC 7677's messages",
      let serverFirst := "r=rOprNGfwEbeRWgbNEkqO%hvYDpWUa2RaTCAfuxFIlj)hNlF$k0,s=W22ZaJ0SNY7soEsUEjb6gQ==,i=4096"
      match Scram.respond .none "user" "pencil" "rOprNGfwEbeRWgbNEkqO" serverFirst 4096 with
      | .ok (final, signature) =>
        final == "c=biws,r=rOprNGfwEbeRWgbNEkqO%hvYDpWUa2RaTCAfuxFIlj)hNlF$k0,p=dHzbZapWIk4jUhN+Ute9ytag9zjfMHgsqmmiz7AndVQ="
          && Scram.verify signature "v=6rriTRBi23WpRR/wtup+mMhUZUn/dB5nLTJRsjl95G4="
          && !Scram.verify signature "v=6rriTRBi23WpRR/wtup+mMhUZUn/dB5nLTJRsjl95G5="
          && !Scram.verify signature "e=invalid-proof"
      | .error _ => false),
    ("postgres: SCRAM refuses a server nonce that does not extend the client's, and too many iterations",
      refusal (Scram.respond .none "" "p" "abc" "r=abd1,s=AAAA,i=1" 10) == some .nonce
        && refusal (Scram.respond .none "" "p" "abc" "r=abc,s=AAAA,i=1" 10) == some .nonce
        && refusal (Scram.respond .none "" "p" "abc" "r=abcd,s=AAAA,i=11" 10) == some .iterations
        && refusal (Scram.respond .none "" "p" "abc" "m=x,r=abcd,s=AAAA,i=1" 10) == some .malformed),
    ("postgres: SCRAM's first message names no user, or escapes its name",
      Scram.mechanism == "SCRAM-SHA-256" && Scram.first .none "" "abc" == "n,,n=,r=abc"
        && Scram.first .none "a=b,c" "x" == "n,,n=a=3Db=2Cc,r=x"),
    ("postgres: SCRAM-SHA-256-PLUS binds the certificate's hash, as Python's hashlib computes it",
      let serverFirst := "r=rOprNGfwEbeRWgbNEkqO%hvYDpWUa2RaTCAfuxFIlj)hNlF$k0,s=W22ZaJ0SNY7soEsUEjb6gQ==,i=4096"
      let hash : ByteArray := ⟨(List.range 32).toArray.map (·.toUInt8)⟩
      let bound := Scram.respond (.endPoint hash) "user" "pencil" "rOprNGfwEbeRWgbNEkqO" serverFirst 4096
      let unoffered := Scram.respond .unoffered "user" "pencil" "rOprNGfwEbeRWgbNEkqO" serverFirst 4096
      Scram.first (.endPoint hash) "" "abc" == "p=tls-server-end-point,,n=,r=abc"
        && Scram.first .unoffered "" "abc" == "y,,n=,r=abc"
        && (Scram.Binding.endPoint hash).mechanism == "SCRAM-SHA-256-PLUS"
        && Scram.Binding.unoffered.mechanism == "SCRAM-SHA-256"
        && (match bound, unoffered with
          | .ok (final, signature), .ok (final', signature') =>
            final == "c=cD10bHMtc2VydmVyLWVuZC1wb2ludCwsAAECAwQFBgcICQoLDA0ODxAREhMUFRYXGBkaGxwdHh8=,r=rOprNGfwEbeRWgbNEkqO%hvYDpWUa2RaTCAfuxFIlj)hNlF$k0,p=nY1Wus9a+gM2DrbQ1msXFgyhW6KM5ktOxWiU+/P/EGY="
              && Scram.verify signature "v=RwppMGddhz/J0lFYaRReBjXcQeNUFP5Qc76Lo5Exrig="
              && final' == "c=eSws,r=rOprNGfwEbeRWgbNEkqO%hvYDpWUa2RaTCAfuxFIlj)hNlF$k0,p=FoqiHTtQEDE8lz1CdaEe3tK4mS+iMDTl77SPyDS53DY="
              && Scram.verify signature' "v=dI4KpiQJwBr1+V+K6U1dA6l6I4I9DUNXWND4pcpRU3U="
          | _, _ => false)),
    ("postgres: a table's operations are sent as their SQL",
      let t : Table := { name := "t" }
      t.request .serializable .begin == .begin .serializable
        && t.request .readCommitted .begin == .begin .readCommitted
        && t.request .serializable (.read 3) == .statement { sql := "SELECT value FROM t WHERE key = $1", params := [some "3"] }
        && t.request .serializable .scan == .statement { sql := "SELECT key, value FROM t ORDER BY key" }
        && t.request .serializable (.insert 3 "x") == .statement { sql := "INSERT INTO t (key, value) VALUES ($1, $2)", params := [some "3", some "x"] }
        && t.request .serializable (.append "x") == .statement { sql := "INSERT INTO t (value) VALUES ($1) RETURNING key", params := [some "x"] }
        && t.request .serializable (.delete 3) == .statement { sql := "DELETE FROM t WHERE key = $1", params := [some "3"] }
        && (match t.request .serializable (.write 3 "x") with
            | .statement st => st.params == [some "3", some "x"] && (st.sql.splitOn "ON CONFLICT").length == 2
            | _ => false)
        && t.request .serializable .commit == .commit && t.request .serializable .rollback == .rollback
        && t.create.sql.startsWith "CREATE TABLE IF NOT EXISTS t "),
    ("postgres: what a reply to a table's operation means",
      let rows (r : List (List (Option String))) : Reply := .rows { rows := r }
      Table.answer (.read 1) (rows []) == .value none
        && Table.answer (.read 1) (rows [[some "x"]]) == .value (some "x")
        && Table.answer (.read 1) (rows [[some "x"], [some "y"]]) == .failed
        && Table.answer .scan (rows [[some "1", some "a"], [some "2", some "b"]]) == .rows [(1, "a"), (2, "b")]
        && Table.answer .scan (rows [[some "one", some "a"]]) == .failed
        && Table.answer (.append "a") (rows [[some "9"]]) == .key 9
        && Table.answer (.insert 1 "a") (.error []) == .failed
        && Table.answer .commit .committed == .committed && Table.answer .commit .rolledBack == .failed
        && Table.answer .commit .unknown == .unknown && Table.answer .rollback .rolledBack == .ok
        && Table.answer .begin (rows []) == .ok && Table.answer (.write 1 "a") (.refused .busy) == .failed
        && scanRows [[some "1", none]] == none),
    ("postgres: a transaction is over after commit, rollback, a failure or no answer",
      Table.over .commit .committed && Table.over .rollback .ok && Table.over (.read 1) .failed
        && Table.over (.read 1) .unknown && !Table.over (.read 1) (.value none) && !Table.over .begin .ok) ]

/-- This client's session replayed: the server's writes received as they came, and each request
submitted where the recording has the client send it. What the connection sends, all of it,
must be the bytes the recording has the client send. -/
def replayExact (cfg : Conn.Config) (writes : List (Bool × ByteArray)) (requests : List Request) :
    Bool :=
  let sent (actions : List Conn.Action) : ByteArray := actions.foldl (init := .empty) fun acc a =>
    match a with
    | .send b | .query _ b => acc ++ b
    | _ => acc
  let (c, first) := Conn.start cfg
  let (_, _, out) := (writes.drop 1).foldl (init := (c, requests, sent first)) fun (c, rs, out) (client, bytes) =>
    if client then
      if bytes[0]? == some 112 then (c, rs, out)
      else if bytes[0]? == some 88 then
        let (c, actions) := c.step cfg .stop
        (c, rs, out ++ sent (actions.take 1))
      else
        match rs with
        | r :: rest =>
          let (c, actions) := c.step cfg (.submit 0 r)
          (c, rest, out ++ sent actions)
        | [] => (c, rs, out)
    else
      let (c, actions) := c.step cfg (.received bytes)
      (c, rs, out ++ sent actions)
  out == writes.foldl (fun acc (client, bytes) => if client then acc ++ bytes else acc) .empty

def recorded (name : String) : IO (List (Bool × ByteArray)) := recording s!"Tests/Postgres/{name}.txt"

def scramConfig (nonce : String) : Conn.Config :=
  { user := "lanes_scram", database := "lanes_test", password := some "scram-pw", nonce }

def scramConfig' (nonce : String) : Conn.Config := { scramConfig nonce with user := "lanes_scram" }

def md5Config : Conn.Config :=
  { user := "lanes_md5", database := "lanes_test", password := some "md5-pw", allowMd5 := true,
    requireScram := false }

def clearConfig (allow : Bool) : Conn.Config :=
  { user := "lanes_clear", database := "lanes_test", password := some "clear-pw", allowCleartext := allow,
    requireScram := false }

/-- What a connection with a password does when the server answers its start-up with `first`
and then says it is ready. -/
def afterAuth (cfg : Conn.Config) (first : Backend) : List Conn.Action :=
  let (c, _) := Conn.start cfg
  let (c, a) := Conn.step cfg c (.received first.encode)
  let (_, b) := Conn.step cfg c (.received (Backend.readyForQuery .idle).encode)
  a ++ b

def sends (actions : List Conn.Action) : Bool := actions.any fun | .send _ => true | _ => false

/-- A server that never proves it knows the password: `AuthenticationOk` at once, which is
`trust`, or a request for MD5 or a cleartext password, any of which an impostor on the path can
send. -/
def downgradeTests : List (String × Bool) :=
  let cfg : Conn.Config :=
    { user := "lanes", database := "lanes", password := some "pw", nonce := "abcdefghijklmnop" }
  let md5 := Backend.authMd5 ⟨#[1, 2, 3, 4]⟩
  [ ("postgres: with a password, AuthenticationOk before SCRAM closes the connection, unopened",
      let a := afterAuth cfg .authOk
      !a.contains .opened && a.contains (.close .signature)),
    ("postgres: with a password, MD5 and cleartext are refused by default, nothing sent",
      let m := afterAuth cfg md5
      let t := afterAuth { cfg with allowCleartext := true } .authCleartext
      !sends m && m.contains (.close .method) && !sends t && t.contains (.close .method)
        && !sends (afterAuth { cfg with allowMd5 := true } md5)),
    ("postgres: with requireScram off, trust and an allowed MD5 open as before",
      (afterAuth { cfg with requireScram := false } .authOk).contains .opened
        && sends (afterAuth { cfg with requireScram := false, allowMd5 := true } md5)),
    ("postgres: without a password, a server that trusts the user opens",
      (afterAuth { cfg with password := none } .authOk).contains .opened) ]

/-- A connection that asks for TLS: what it sends and does as the server answers. -/
def tlsTests : List (String × Bool) :=
  let cfg : Conn.Config :=
    { user := "lanes", database := "lanes", password := some "pw", nonce := "abcdefghijklmnop",
      encryption := .negotiated }
  let (c, first) := Conn.start cfg
  let answer (bytes : List UInt8) := Conn.step cfg c (.received ⟨bytes.toArray⟩)
  let (afterS, startTls) := answer [83]
  let secured (cfg : Conn.Config) (c : Conn) (endPoint : Option ByteArray) (alpn : ByteArray) :=
    Conn.step cfg c (.secured endPoint alpn)
  let hash : ByteArray := ⟨#[7, 7, 7]⟩
  let (afterTls, startup) := secured cfg afterS (some hash) .empty
  let offer (cfg : Conn.Config) (c : Conn) (mechanisms : List String) :=
    Conn.step cfg c (.received (Backend.authSasl mechanisms).encode)
  let both := ["SCRAM-SHA-256-PLUS", "SCRAM-SHA-256"]
  let initial (b : Scram.Binding) :=
    Conn.Action.send (Frontend.saslInitial b.mechanism (Scram.first b "" cfg.nonce).toUTF8).encode
  [ ("postgres tls: SSLRequest is the eight bytes of length 8 and code 80877103",
      Conn.sslRequest.data.toList == [0, 0, 0, 8, 4, 210, 22, 47]
        && first == [.send Conn.sslRequest] && c.phase == .sslRequest),
    ("postgres tls: an S starts the handshake, and the start-up is sent only once it is done",
      startTls == [.startTls] && afterS.phase == .handshake
        && startup == [.send (Conn.startup cfg).encode] && afterTls.phase == .startup
        && afterTls.endPoint == some hash),
    ("postgres tls: an N is refused, nothing sent",
      let (c', a) := answer [78]
      c'.phase == .closed && a == [.close .refusedTls]),
    ("postgres tls: bytes after the S, sent in the clear, are refused (CVE-2021-23222)",
      let (_, a) := answer [83, 82, 0, 0, 0, 8, 0, 0, 0, 0]
      a == [.close .protocol] && (answer [69, 0, 0, 0, 4]).2 == [.close .protocol]),
    ("postgres tls: a stop before TLS sends nothing; a failed handshake closes with its reason",
      (Conn.step cfg c .stop).2 == [.close .stopped]
        && (Conn.step cfg afterS (.insecure "bad")).2 == [.close (.tls "bad")]
        && (Conn.step cfg afterS (.submit 1 .commit)).2 == [.reply 1 (.refused .notReady)]),
    ("postgres tls: direct TLS starts with the handshake and needs the ALPN protocol postgresql",
      let d := { cfg with encryption := .direct }
      let (c, a) := Conn.start d
      a == [.startTls] && c.phase == .handshake
        && (secured d c none .empty).2 == [.close .alpn]
        && (secured d c none "h2".toUTF8).2 == [.close .alpn]
        && (secured d c none "postgresql".toUTF8).2 == [.send (Conn.startup d).encode]
        && (secured cfg afterS none "h2".toUTF8).2 == [.close .alpn]),
    ("postgres tls: SCRAM-SHA-256-PLUS is chosen when offered, bound to the certificate's hash",
      let (c', a) := offer cfg afterTls both
      a == [initial (.endPoint hash)] && c'.phase == .sasl (.endPoint hash)),
    ("postgres tls: a server that does not offer PLUS is told the client could bind (y)",
      (offer cfg afterTls ["SCRAM-SHA-256"]).2 == [initial .unoffered]),
    ("postgres tls: with channel binding required, a server without PLUS is refused",
      let r := { cfg with channelBinding := .require }
      (offer r afterTls ["SCRAM-SHA-256"]).2 == [.close .method]
        && (offer r afterTls both).2 == [initial (.endPoint hash)]
        && (offer r { afterTls with endPoint := none } both).2 == [.close .method]),
    ("postgres tls: with channel binding disabled, or a certificate with no hash, n is sent",
      (offer { cfg with channelBinding := .disable } afterTls both).2 == [initial .none]
        && (offer cfg { afterTls with endPoint := none } both).2 == [initial .none]),
    ("postgres tls: without TLS, PLUS is never chosen, and requiring it refuses",
      let plain := { cfg with encryption := .plain }
      let (c, _) := Conn.start plain
      (offer plain c both).2 == [initial .none]
        && (offer { plain with channelBinding := .require } c both).2 == [.close .method]),
    ("postgres tls: a connection is reusable only open, idle, and with nothing in flight",
      let ready : Conn := { phase := .ready }
      ready.reusable && !{ ready with status := .inTx }.reusable
        && !{ ready with queue := [{ id := 0, kind := .commit }] }.reusable
        && !({ phase := .closed } : Conn).reusable) ]

/-- The certificate's signature algorithm, and the hash RFC 5929 takes for it. -/
def endPointTests : List (String × Bool) :=
  let cert (oid : List UInt8) : ByteArray :=
    let tlv (tag : UInt8) (body : List UInt8) := tag :: body.length.toUInt8 :: body
    ⟨(tlv 0x30 (tlv 0x30 [2, 1, 0] ++ tlv 0x30 (tlv 6 oid ++ [5, 0]) ++ tlv 3 [0, 1])).toArray⟩
  let pkcs1 (n : UInt8) := Certificate.pkcs1 ++ [n]
  [ ("certificate: the hash of tls-server-end-point is the signature's, SHA-256 for MD5 and SHA-1",
      Certificate.hashOf (pkcs1 11) == some .sha256 && Certificate.hashOf (pkcs1 5) == some .sha256
        && Certificate.hashOf (pkcs1 4) == some .sha256 && Certificate.hashOf (pkcs1 12) == some .sha384
        && Certificate.hashOf (pkcs1 13) == some .sha512
        && Certificate.hashOf (Certificate.ecdsa ++ [3, 2]) == some .sha256
        && Certificate.hashOf (Certificate.ecdsa ++ [3, 3]) == some .sha384
        && Certificate.hashOf (Certificate.ecdsa ++ [3, 4]) == some .sha512
        && Certificate.hashOf (Certificate.ecdsa ++ [1]) == some .sha256
        && Certificate.hashOf (pkcs1 10) == none && Certificate.hashOf [0x2b, 0x65, 0x70] == none),
    ("certificate: the signature algorithm is read from the outer SEQUENCE",
      Certificate.signatureAlgorithm (cert (pkcs1 12)) == some (pkcs1 12)
        && Certificate.endPoint (cert (pkcs1 12)) == some (Sha512.hash384 (cert (pkcs1 12)))
        && Certificate.endPoint (cert (pkcs1 11)) == some (Sha256.hash (cert (pkcs1 11)))
        && Certificate.endPoint (cert [0x2b, 0x65, 0x70]) == none
        && Certificate.endPoint .empty == none
        && Certificate.endPoint ((cert (pkcs1 11)).extract 0 10) == none) ]

def psqlTests : IO (List (String × Bool)) := do
  let names := ["psql-trust", "psql-cleartext", "psql-md5", "psql-scram", "psql-scram-wrong",
    "lanes-trust", "lanes-md5", "lanes-scram", "lanes-scram-wrong"]
  let mut results := []
  for name in names do
    let writes ← recorded name
    results := results ++ [(s!"postgres: every message of {name} is read and written again as the same bytes",
      !writes.isEmpty && (decodeAll writes).isSome)]
  let md5 := (decodeAll (← recorded "psql-md5")).getD []
  let md5Right := match backends md5, frontends md5 with
    | .authMd5 salt :: _, _ :: .password sent :: _ => sent == md5Answer "lanes_md5" "md5-pw" salt
    | _, _ => false
  let scram := (decodeAll (← recorded "psql-scram")).getD []
  let nonceOf (data : ByteArray) := ((String.fromUTF8? data).getD "").drop 8 |>.toString
  let scramRight := match backends scram, frontends scram with
    | _ :: .authSaslContinue first :: .authSaslFinal final :: _, _ :: .saslInitial _ data :: .saslResponse sent :: _ =>
      match Scram.respond .none "" "scram-pw" (nonceOf data) ((String.fromUTF8? first).getD "") 4096 with
      | .ok (mine, signature) => mine.toUTF8 == sent && Scram.verify signature ((String.fromUTF8? final).getD "")
      | .error _ => false
    | _, _ => false
  let scramNonce := match frontends scram with
    | _ :: .saslInitial _ data :: _ => nonceOf data
    | _ => ""
  let trust := replay { user := "lanes_trust", database := "lanes_test" } (← recorded "psql-trust")
  let trustReplies' := (replies trust).filter fun r => (sqlstate r).isNone
  let errors := (replies trust).filterMap sqlstate
  let scramReplay := replay (scramConfig scramNonce) (← recorded "psql-scram")
  let wrong := (decodeAll (← recorded "psql-scram-wrong")).getD []
  let wrongNonce := match frontends wrong with
    | _ :: .saslInitial _ data :: _ => nonceOf data
    | _ => ""
  let wrongReplay := replay (scramConfig wrongNonce) (← recorded "psql-scram-wrong")
  let md5Replay := replay md5Config (← recorded "psql-md5")
  let cleartext ← recorded "psql-cleartext"
  let clearReplay (allow : Bool) := replay (clearConfig allow) cleartext
  let lanesNonce (name : String) : IO String := do
    let ms := (decodeAll (← recorded name)).getD []
    return match frontends ms with
      | _ :: .saslInitial _ data :: _ => nonceOf data
      | _ => ""
  let who := Request.statement { sql := "SELECT current_user" }
  let lanesTrust := replayExact { user := "lanes_trust", database := "lanes_test" } (← recorded "lanes-trust")
    [.statement { sql := "SELECT $1::text AS a, NULL::int AS b, 'é' AS c", params := [some "x"] },
     .statement { sql := "SELECT 1 / 0" }, .begin .readCommitted, .statement { sql := "SELECT 1 / 0" },
     .commit]
  let lanesScram := replayExact (scramConfig' (← lanesNonce "lanes-scram")) (← recorded "lanes-scram") [who]
  let lanesMd5 := replayExact md5Config (← recorded "lanes-md5") [who]
  let lanesWrong := replayExact { scramConfig' (← lanesNonce "lanes-scram-wrong") with password := some "wrong" }
    (← recorded "lanes-scram-wrong") []
  return results ++ [
    ("postgres: this client's recorded sessions replayed send exactly the bytes recorded",
      lanesTrust && lanesScram && lanesMd5 && lanesWrong),
    ("postgres: the MD5 answer is libpq's", md5Right),
    ("postgres: the SCRAM answer is libpq's, and the server's signature is verified", scramRight),
    ("postgres: psql's session replayed gives each reply, a failed transaction's COMMIT rolled back",
      trust.contains .opened && trustReplies' == trustReplies
        && errors == ["22012", "22012", "25P02", "42P01"]),
    ("postgres: replayed with SCRAM, the connection opens and reads the reply",
      scramReplay.contains .opened
        && replies scramReplay == [.rows { columns := ["who"], rows := [[text "lanes_scram"]], tag := "SELECT 1" }]),
    ("postgres: replayed with MD5, the connection opens",
      md5Replay.contains .opened
        && replies md5Replay == [.rows { columns := ["who"], rows := [[text "lanes_md5"]], tag := "SELECT 1" }]),
    ("postgres: a cleartext password is sent only when allowed",
      (clearReplay true).contains .opened && !(clearReplay false).contains .opened
        && (clearReplay false).contains (.close .method)),
    ("postgres: a wrong password is refused by the server, and the connection closes",
      !wrongReplay.contains .opened
        && wrongReplay.any fun | .close (.server fields) => fields.any (·.value == "28P01") | _ => false) ]

end Tests.Postgres
