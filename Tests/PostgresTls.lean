/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Tests.Tls
import Lanes.Services.Postgres

/-!
The PostgreSQL client over TLS. Against `openssl s_server`, where there is an `openssl` command,
with certificates made for the test: the certificate the handshake gives is the server's, and
its hash for channel binding is SHA-256 or SHA-384 as its signature says, as `openssl dgst`
computes it; direct TLS sends the start-up through TLS once the server chose ALPN `postgresql`,
and refuses a server that chose none; `verifyFull` refuses a certificate for another name, which
`require` takes.

Against a real PostgreSQL with TLS, when `LANES_POSTGRES_TLS=host:port` names one and
`LANES_POSTGRES_CERTS` the directory `scripts/postgres-test-server DIR PORT tls` made: SCRAM
bound to the certificate (`SCRAM-SHA-256-PLUS`) opens, over TLS as `pg_stat_ssl` says, to an
address and to `localhost` by name; a user
the server takes over TLS only is refused without it; through a relay that holds another
certificate from the same authority, a bound client is refused and an unbound one is not, as
libpq's `psql` is; and a pool of two to `localhost` serves six clients on at most two connections and
replaces one handed back broken with one that resolves the name again. CI runs no such server.
-/

namespace Tests.PostgresTls

open Lanes Lanes.Postgres Std Std.Async
open Tests.Tls (run authority leaf freePort listening hasOpenssl)

def connection (port : UInt16) (trust : Tls.Trust) (sslmode : SslMode := .verifyFull)
    (serverName : Option String := none) (direct : Bool := false) (user := "lanes")
    (password := "pw") (channelBinding : Conn.ChannelBinding := .prefer) (timeout_ms := 3000) :
    Client.Config :=
  { host := "127.0.0.1", port, sslmode, trust, serverName, direct, timeout_ms,
    conn := { user, database := "lanes_test", password := some password, channelBinding } }

/-- The certificate the server on `port` presents, as DER. -/
def peer (port : UInt16) (trust : Tls.Trust) : Async ByteArray := do
  let socket ← TCP.Socket.Client.mk
  try
    socket.connect (.v4 ⟨.ofParts 127 0 0 1, port⟩)
    let t ← Tls.Session.start trust "127.0.0.1"
    repeat
      let done ← t.handshake
      let out ← t.take
      unless out.isEmpty do socket.send out
      if done then break
      let some bytes ← socket.recv? 65536 | throw (.userError "closed in the handshake")
      t.feed bytes
    t.peer
  finally socket.close

def output (dir : System.FilePath) (cmd : String) (args : Array String) : IO ByteArray := do
  let child ← IO.Process.spawn { cmd, args, cwd := dir, stdout := .piped, stderr := .null, stdin := .null }
  let out ← child.stdout.readBinToEnd
  discard child.wait
  return out

/-- `openssl s_server` with the certificate `cert`, choosing ALPN `postgresql` if `alpn`; it
writes what it reads from its client, and keeps the connection while its input is open. -/
def sServer (dir : System.FilePath) (cert : String) (alpn : Bool) :
    Async (IO.Process.Child ⟨.piped, .piped, .null⟩ × UInt16) := do
  let port ← freePort
  let args := #["s_server", "-accept", toString port, "-cert", s!"{cert}.pem", "-key", s!"{cert}.key",
    "-quiet"] ++ (if alpn then #["-alpn", "postgresql"] else #[])
  let child ← IO.Process.spawn
    { cmd := "openssl", args, cwd := dir, stdin := .piped, stdout := .piped, stderr := .null }
  unless ← listening port do throw (.userError "openssl s_server did not start")
  return (child, port)

def closedWith (r : Except (Option Closing) Session) : Option Closing :=
  match r with
  | .error why => why
  | .ok _ => none

def isTls : Option Closing → Bool
  | some (.tls _) => true
  | _ => false

def contains (hay needle : ByteArray) : Bool :=
  (List.range (hay.size + 1 - needle.size)).any fun i => hay.extract i (i + needle.size) == needle

def offline : Async (List (String × Bool)) := do
  let dir : System.FilePath :=
    s!"{(← IO.getEnv "TMPDIR").getD "/tmp"}/lanes-pgtls-{← IO.monoNanosNow}"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / "ca.cnf") Tests.Tls.config
  authority dir "ca"
  leaf dir "good" "ca" "DNS:localhost,IP:127.0.0.1"
  -- the same, signed with SHA-384
  run dir #["req", "-new", "-key", "good.key", "-subj", "/CN=sha384", "-out", "good384.csr",
    "-config", "ca.cnf"]
  run dir #["x509", "-req", "-in", "good384.csr", "-CA", "ca.pem", "-CAkey", "ca.key", "-set_serial",
    "3", "-days", "2", "-sha384", "-extfile", "good.ext", "-out", "good384.pem"]
  run dir #["x509", "-in", "good.pem", "-outform", "DER", "-out", "good.der"]
  run dir #["x509", "-in", "good384.pem", "-outform", "DER", "-out", "good384.der"]
  IO.FS.writeFile (dir / "good384.key") (← IO.FS.readFile (dir / "good.key"))
  let trust := Tls.Trust.file (dir / "ca.pem")
  let children ← IO.mkRef ([] : List (IO.Process.Child ⟨.piped, .piped, .null⟩))
  let start (cert : String) (alpn : Bool) : Async UInt16 := do
    let (child, port) ← sServer dir cert alpn
    children.modify (child :: ·)
    return port
  try
    let der ← IO.FS.readBinFile (dir / "good.der")
    let der384 ← IO.FS.readBinFile (dir / "good384.der")
    let given ← peer (← start "good" false) trust
    let given384 ← peer (← start "good384" false) trust
    let sha256 ← output dir "openssl" #["dgst", "-sha256", "-binary", "good.der"]
    let sha384 ← output dir "openssl" #["dgst", "-sha384", "-binary", "good384.der"]
    let noAlpn ← start "good" false
    let refused ← connect (connection noAlpn trust (direct := true))
    let named ← connect (connection noAlpn trust (direct := true) (serverName := some "elsewhere.example"))
    let chained ← connect (connection noAlpn trust (direct := true) (sslmode := .verifyCa)
      (serverName := some "elsewhere.example"))
    let untrusted ← connect (connection noAlpn .system (direct := true))
    let (child, withAlpn) ← sServer dir "good" true
    let direct ← connect (connection withAlpn trust (direct := true) (timeout_ms := 1500))
    child.kill
    let heard ← child.stdout.readBinToEnd
    discard child.wait
    return [
      ("postgres tls: the handshake gives the server's certificate", given == der && given384 == der384),
      ("postgres tls: its hash for channel binding is SHA-256 or SHA-384, as its signature says",
        Certificate.endPoint given == some sha256 && Certificate.endPoint given384 == some sha384
          && sha256.size == 32 && sha384.size == 48),
      ("postgres tls: direct TLS to a server that chose no ALPN protocol is refused",
        closedWith refused == some .alpn),
      ("postgres tls: verifyFull refuses a certificate for another name; require takes it",
        isTls (closedWith named) && closedWith chained == some .alpn),
      ("postgres tls: a certificate from an authority not trusted is refused",
        isTls (closedWith untrusted)),
      ("postgres tls: direct TLS with ALPN postgresql sends the start-up through TLS",
        closedWith direct == none && direct matches .error _
          && contains heard "user".toUTF8 && contains heard "lanes_test".toUTF8) ]
  finally
    for child in ← children.get do
      child.kill
      discard child.wait
    IO.FS.removeDirAll dir

/-- The relay of `Tests/Postgres/relay.py` in front of `upstream`, with the certificate `cert`. -/
def relay (upstream : UInt16) (certs : String) :
    IO (IO.Process.Child ⟨.null, .piped, .null⟩ × UInt16) := do
  let child ← IO.Process.spawn
    { cmd := "python3", args := #["-I", "Tests/Postgres/relay.py", toString upstream,
        s!"{certs}/relay.pem", s!"{certs}/relay.key"], stdin := .null, stdout := .piped, stderr := .null }
  let line ← child.stdout.getLine
  let some port := line.trimAscii.toString.toNat? | throw (.userError s!"the relay said {line}")
  return (child, port.toUInt16)

/-- What `psql`, libpq's, makes of the server on `port` with `options`: whether it ran the query. -/
def psql (port : UInt16) (certs : String) (options : String) : IO Bool := do
  let out ← IO.Process.output
    { cmd := "psql", env := #[("PGPASSWORD", some "scram-pw")],
      args := #[s!"host=localhost port={port} dbname=lanes_test user=lanes_scram sslrootcert={certs}/ca.pem {options}",
        "-Atc", "SELECT 1"] }
  return out.exitCode == 0 && out.stdout.trimAscii.toString == "1"

def hasPsql : IO Bool := do
  try return (← IO.Process.output { cmd := "psql", args := #["--version"] }).exitCode == 0
  catch _ => return false

def query (s : Session) (sql : String) : Async (Option String) := do
  match ← s.exec (.statement { sql }) with
  | .rows { rows := [[v]], .. } => return v
  | _ => return none

def opensWith (cfg : Client.Config) (sql : String := "SELECT 1") : Async (Option String) := do
  match ← connect cfg with
  | .ok s =>
    let v ← query s sql
    s.close
    return v
  | .error _ => return none

def server : IO (Option (UInt16 × String)) := do
  let some spec ← IO.getEnv "LANES_POSTGRES_TLS" | return none
  let some certs ← IO.getEnv "LANES_POSTGRES_CERTS" | return none
  match spec.splitOn ":" with
  | ["127.0.0.1", port] => return port.toNat?.map fun p => (p.toUInt16, certs)
  | _ => return none

def pooled (port : UInt16) (trust : Tls.Trust) : Async (List (String × Bool)) := do
  let pool ← Pool.new { connection port trust (user := "lanes_scram") (password := "scram-pw") with
    host := "localhost" }
    { max := 2, waiting_max := 8 }
  let tasks ← (List.range 6).mapM fun _ => async do
    pool.withSession 5000 fun s => do
      discard <| query s "SELECT pg_sleep(0.05)::text"
      query s "SELECT pg_backend_pid()::text"
  let pids ← tasks.mapM await
  let served := pids.filterMap fun | .ok (some pid) => some pid | _ => none
  let distinct := served.eraseDups
  let first ← pool.checkout 5000
  let replaced ← match first with
    | .ok (conn, s) =>
      discard <| s.tell .broken
      pool.checkin conn s
      match ← pool.checkout 5000 with
      | .ok (conn', s') =>
        let v ← query s' "SELECT 1"
        pool.checkin conn' s'
        pure (conn' != conn && v == some "1")
      | .error _ => pure false
    | .error _ => pure false
  return [
    ("postgres pool: six clients on a pool of two are each served, on at most two connections",
      served.length == 6 && distinct.length ≤ 2),
    ("postgres pool: a connection handed back broken is replaced by a new one, to the name resolved again",
      replaced) ]

/-- A URI with `sslmode=verify-full` and `sslrootcert`, read by `Settings.read`, opens over TLS;
with the system's authorities, which do not hold the test's, it is refused; with
`sslrootcert` under `~/.postgresql/root.crt`, the default, it opens. -/
def fromSettings (port : UInt16) (certs : String) : Async (List (String × Bool)) := do
  let home : System.FilePath := s!"{(← IO.getEnv "TMPDIR").getD "/tmp"}/lanes-home-{← IO.monoNanosNow}"
  IO.FS.createDirAll (home / ".postgresql")
  IO.FS.writeFile (home / ".postgresql" / "root.crt") (← IO.FS.readFile s!"{certs}/ca.pem")
  let vars := [("HOME", home.toString), ("USER", "nobody")]
  let env : Env IO := { Env.io with var := fun name => pure (vars.lookup name) }
  let uri (query : String) :=
    s!"postgresql://lanes_scram:scram-pw@localhost:{port}/lanes_test?{query}"
  let open_ (conninfo : String) : Async (Option String) := do
    match ← (Settings.read env conninfo).run with
    | .ok s => opensWith (.ofSettings s) "SELECT ssl::text FROM pg_stat_ssl WHERE pid = pg_backend_pid()"
    | .error _ => return none
  let named ← open_ (uri s!"sslmode=verify-full&sslrootcert={certs}/ca.pem&channel_binding=require")
  let system ← open_ (uri "sslrootcert=system")
  let byDefault ← open_ (uri "sslmode=verify-full")
  IO.FS.removeDirAll home
  return [
    ("postgres tls live: a URI with verify-full and sslrootcert opens over TLS, bound",
      named == some "true"),
    ("postgres tls live: with the system's authorities the test's certificate is refused", system.isNone),
    ("postgres tls live: ~/.postgresql/root.crt is the authorities by default, as libpq's",
      byDefault == some "true") ]

def live : Async (List (String × Bool)) := do
  let openssl ← hasOpenssl
  let fromOpenssl ← if openssl then offline else
    IO.eprintln "postgres tls: skipped openssl s_server, there is no openssl command"
    pure []
  let some (port, certs) ← server
    | return fromOpenssl ++ [("postgres tls live: skipped, LANES_POSTGRES_TLS and LANES_POSTGRES_CERTS are not set", true)]
  let trust := Tls.Trust.file s!"{certs}/ca.pem"
  let scram := connection port trust (user := "lanes_scram") (password := "scram-pw")
  let byAddress ← opensWith { scram with conn.channelBinding := .require }
    "SELECT ssl::text FROM pg_stat_ssl WHERE pid = pg_backend_pid()"
  let byName ← opensWith { scram with serverName := some "localhost", conn.channelBinding := .require }
  let named ← opensWith { scram with host := "localhost", conn.channelBinding := .require }
    "SELECT ssl::text FROM pg_stat_ssl WHERE pid = pg_backend_pid()"
  let tlsOnly ← opensWith (connection port trust (user := "lanes_tls") (password := "tls-pw"))
  let tlsPlain ← connect { connection port trust (user := "lanes_tls") (password := "tls-pw") with sslmode := .disable }
  let wrongName ← connect { scram with serverName := some "elsewhere.example" }
  let (child, relayPort) ← relay port certs
  let relayed ← try connect { scram with port := relayPort } finally pure ()
  let relayedUnbound ← opensWith { scram with port := relayPort, conn.channelBinding := .disable }
  let libpq ← hasPsql
  let libpqDirect ← if libpq then psql port certs "sslmode=verify-full channel_binding=require" else pure true
  let libpqRelayed ← if libpq then psql relayPort certs "sslmode=verify-full channel_binding=require" else pure false
  let libpqRelayedUnbound ← if libpq then psql relayPort certs "sslmode=verify-full channel_binding=disable" else pure true
  child.kill
  discard child.wait
  let refusedByServer := match relayed with
    | .error (some (.server fields)) => fields.any (·.value == "SCRAM channel binding check failed")
    | _ => false
  let tlsPlainRefused := match tlsPlain with
    | .error (some (.server fields)) => fields.any (·.value == "28000")
    | _ => false
  return fromOpenssl ++ [
    ("postgres tls live: SCRAM-SHA-256-PLUS, verifyFull by address and by name, over TLS",
      byAddress == some "true" && byName == some "1"),
    ("postgres tls live: a host name resolved, and its certificate checked for the name, over TLS",
      named == some "true"),
    ("postgres tls live: a user taken over TLS only opens with it and is refused without",
      tlsOnly == some "1" && tlsPlainRefused),
    ("postgres tls live: verifyFull refuses the server's certificate for another name",
      isTls (closedWith wrongName)),
    ("postgres tls live: through a relay with another valid certificate, the server refuses the bound client",
      refusedByServer),
    ("postgres tls live: through the same relay, a client that does not bind is not refused",
      relayedUnbound == some "1"),
    ("postgres tls live: libpq agrees: it binds directly, is refused through the relay, and is not when it does not bind",
      libpqDirect && !libpqRelayed && libpqRelayedUnbound) ] ++ (← pooled port trust)
    ++ (← fromSettings port certs)

end Tests.PostgresTls
