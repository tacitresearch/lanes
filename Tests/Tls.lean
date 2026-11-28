/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
The HTTPS client against `openssl s_server`, with certificates made for the test by `openssl`: a
certificate authority of its own, which the client is told to trust, a certificate from it for
`localhost` and `127.0.0.1`, another from it for a name that is not the server's, and one from a
second authority the client does not trust. Each refusal is a test of `native/tls.c`: verifying
the chain, the name and the address, and sending the name (SNI). The test is skipped where there
is no `openssl` command. Against a public server it runs only when the network reaches one.
-/

namespace Tests.Tls

open Lanes Lanes.Http Std Std.Async

def run (dir : System.FilePath) (args : Array String) : IO Unit := do
  let out ← IO.Process.output { cmd := "openssl", args, cwd := dir }
  unless out.exitCode == 0 do throw (.userError s!"openssl {args}: {out.stderr}")

def config : String :=
  "[req]\ndistinguished_name = dn\n[dn]\n[ca]\nbasicConstraints = critical,CA:TRUE\n\
  keyUsage = critical,keyCertSign,cRLSign\n"

def key (dir : System.FilePath) (name : String) : IO Unit :=
  run dir #["ecparam", "-name", "prime256v1", "-genkey", "-noout", "-out", s!"{name}.key"]

/-- An authority `name.pem`, its key `name.key`. -/
def authority (dir : System.FilePath) (name : String) : IO Unit := do
  key dir name
  run dir #["req", "-x509", "-new", "-key", s!"{name}.key", "-out", s!"{name}.pem", "-days", "2",
    "-subj", s!"/CN=Lanes test {name}", "-config", "ca.cnf", "-extensions", "ca"]

/-- A server's certificate `name.pem` for the names in `san`, from `issuer`. -/
def leaf (dir : System.FilePath) (name issuer san : String) : IO Unit := do
  key dir name
  IO.FS.writeFile (dir / s!"{name}.ext") s!"subjectAltName={san}\nextendedKeyUsage=serverAuth\n"
  run dir #["req", "-new", "-key", s!"{name}.key", "-subj", s!"/CN={name}", "-out",
    s!"{name}.csr", "-config", "ca.cnf"]
  run dir #["x509", "-req", "-in", s!"{name}.csr", "-CA", s!"{issuer}.pem", "-CAkey",
    s!"{issuer}.key", "-set_serial", "2", "-days", "2", "-extfile", s!"{name}.ext", "-out",
    s!"{name}.pem"]

def freePort : IO UInt16 := do
  let server ← TCP.Socket.Server.mk
  server.bind (.v4 ⟨.ofParts 127 0 0 1, 0⟩)
  let port := (← server.getSockName).port
  server.close
  return port

def listening (port : UInt16) : Async Bool := do
  for _ in [0:100] do
    let socket ← TCP.Socket.Client.mk
    let up ← try socket.connect (.v4 ⟨.ofParts 127 0 0 1, port⟩); pure true catch _ => pure false
    socket.close
    if up then return true
    Async.sleep 50
  return false

/-- `openssl s_server` serving the files of `dir`, with the certificate `cert`; to a client that
names `localhost` in SNI, with `sni` instead when it is given. -/
def server (dir : System.FilePath) (cert : String) (sni : Option String := none) :
    Async (IO.Process.Child ⟨.null, .null, .null⟩ × UInt16) := do
  let port ← freePort
  let named := match sni with
    | some other => #["-servername", "localhost", "-cert2", s!"{other}.pem", "-key2", s!"{other}.key"]
    | none => #[]
  let args := #["s_server", "-accept", toString port, "-cert", s!"{cert}.pem", "-key",
    s!"{cert}.key", "-WWW", "-quiet"] ++ named
  let child ← IO.Process.spawn
    { cmd := "openssl", args, cwd := dir, stdin := .null, stdout := .null, stderr := .null }
  unless ← listening port do throw (.userError "openssl s_server did not start")
  return (child, port)

/-- Where each complete TLS record from `start` on ends: a record is a header of five bytes, the
last two its length, and that many bytes. -/
def recordEnds (bytes : ByteArray) : (fuel start : Nat) → List Nat
  | 0, _ => []
  | fuel + 1, start =>
    if start + 5 ≤ bytes.size then
      let next := start + 5 + bytes[start + 3]!.toNat * 256 + bytes[start + 4]!.toNat
      if next ≤ bytes.size then next :: recordEnds bytes fuel next else []
    else []

/-- In front of `upstream`: what the client sends is passed on, and what the server sends record
by record, except that a last record of 24 bytes, the size of TLS 1.3's `close_notify`, is held
back until another follows. When the server's side ends, or sends nothing more for 300 ms (it
waits for the client to close), the connection is closed after the record held back, which is
dropped if `cut`: the end an attacker who cuts the connection makes. -/
def relay (upstream : UInt16) (cut : Bool) : Async (TCP.Socket.Server × UInt16) := do
  let server ← TCP.Socket.Server.mk
  server.bind (.v4 ⟨.ofParts 127 0 0 1, 0⟩)
  server.listen 16
  let port := (← server.getSockName).port
  background do
    try
      repeat
        let client ← server.accept
        background do
          let up ← TCP.Socket.Client.mk
          try
            up.connect (.v4 ⟨.ofParts 127 0 0 1, upstream⟩)
            background do
              try
                repeat
                  let some bytes ← client.recv? 65536 | break
                  up.send bytes
              catch _ => pure ()
            let mut held := ByteArray.empty
            repeat
              let arrived := try up.recv? 65536 catch _ => pure none
              let quiet := (fun _ => none) <$> Async.sleep 300
              let some bytes ← if held.isEmpty then arrived else Async.race arrived quiet | break
              held := held ++ bytes
              let ends := 0 :: recordEnds held held.size 0
              let upTo := match ends.reverse with
                | last :: before :: _ => if last - before == 24 then before else last
                | _ => 0
              if 0 < upTo then client.send (held.extract 0 upTo)
              held := held.extract upTo held.size
            unless cut || held.isEmpty do client.send held
          catch _ => pure ()
          up.close
          client.close
    catch _ => pure ()
  return (server, port)

def fetch (host : String) (port : UInt16) (trust : Tls.Trust) : Async (Option Response) :=
  Client.exchange { host, port, scheme := .https, request := { method := .get, path := ["hello"] } }
    { timeout_ms := 5000, trust }

def says (answer : Option Response) (text : String) : Bool :=
  answer.any fun r => r.status == 200 && String.fromUTF8? r.body == some text

def offline : Async (List (String × Bool)) := do
  let dir : System.FilePath :=
    s!"{(← IO.getEnv "TMPDIR").getD "/tmp"}/lanes-tls-{← IO.monoNanosNow}"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / "ca.cnf") config
  IO.FS.writeFile (dir / "hello") "hello over tls\n"
  authority dir "ca"
  authority dir "rogue"
  leaf dir "good" "ca" "DNS:localhost,IP:127.0.0.1"
  leaf dir "elsewhere" "ca" "DNS:elsewhere.example"
  leaf dir "forged" "rogue" "DNS:localhost,IP:127.0.0.1"
  let trust := Tls.Trust.file (dir / "ca.pem")
  let children ← IO.mkRef ([] : List (IO.Process.Child ⟨.null, .null, .null⟩))
  let start (cert : String) (sni : Option String := none) : Async UInt16 := do
    let (child, port) ← server dir cert sni
    children.modify (child :: ·)
    return port
  let relays ← IO.mkRef ([] : List TCP.Socket.Server)
  let startRelay (upstream : UInt16) (cut : Bool) : Async UInt16 := do
    let (server, port) ← relay upstream cut
    relays.modify (server :: ·)
    return port
  try
    let goodPort ← start "good"
    let namedPort ← start "elsewhere" (sni := some "good")
    let otherPort ← start "elsewhere"
    let forgedPort ← start "forged"
    let byName ← fetch "localhost" goodPort trust
    let byAddress ← fetch "127.0.0.1" goodPort trust
    let bySni ← fetch "localhost" namedPort trust
    let addressNotNamed ← fetch "127.0.0.1" namedPort trust
    let wrongName ← fetch "localhost" otherPort trust
    let untrusted ← fetch "localhost" forgedPort trust
    let notSystem ← fetch "localhost" goodPort .system
    let missing ← fetch "localhost" goodPort (.file (dir / "none.pem"))
    let relayed ← fetch "localhost" (← startRelay goodPort false) trust
    let truncated ← fetch "localhost" (← startRelay goodPort true) trust
    return [
      ("tls: a server whose certificate is for its name is answered, over TLS",
        says byName "hello over tls\n"),
      ("tls: a server whose certificate is for its address is answered",
        says byAddress "hello over tls\n"),
      ("tls: the name is sent (SNI), and the server picks its certificate by it",
        says bySni "hello over tls\n"),
      ("tls: a certificate for another name is refused", wrongName.isNone),
      ("tls: a certificate not for the address called is refused", addressNotNamed.isNone),
      ("tls: a certificate from an authority not trusted is refused", untrusted.isNone),
      ("tls: the test's authority is not in the system's trust store", notSystem.isNone),
      ("tls: a trust store that is not there trusts nothing", missing.isNone),
      ("tls: an answer framed by the end of the connection is taken once the server says it closes",
        says relayed "hello over tls\n"),
      ("tls: an answer framed by the end of the connection, cut before the server says it closes, \
        is no answer", truncated.isNone) ]
  finally
    for server in ← relays.get do server.close
    for child in ← children.get do
      child.kill
      discard child.wait
    IO.FS.removeDirAll dir

/-- A public server, when the network reaches it directly; else nothing is asserted. -/
def online (host : String := "example.com") : Async (List (String × Bool)) := do
  let reached : Async Bool := do
    let found ← DNS.getAddrInfo host "" (some .ipv4)
    let some (Std.Net.IPAddr.v4 addr) := found[0]? | return false
    let socket ← TCP.Socket.Client.mk
    let up ← try socket.connect (.v4 ⟨addr, 443⟩); pure true catch _ => pure false
    socket.close
    return up
  let patience := (fun _ => false) <$> Async.sleep 3000
  unless ← (try Async.race reached patience catch _ => pure false) do
    IO.eprintln s!"tls: skipped the call to {host}, which the network does not reach"
    return []
  let some call := Client.Call.at s!"https://{host}" { method := .get, path := [] }
    | return [("tls: an https origin is a call", false)]
  let answer ← Client.exchangeExplained call { timeout_ms := 10000 }
  if let .error why := answer then IO.eprintln s!"tls: {host}: {why}"
  return [(s!"tls: {host} is answered over TLS, checked against the system's trust store",
    match answer with | .ok response => response.status == 200 | .error _ => false)]

def hasOpenssl : IO Bool := do
  try return (← IO.Process.output { cmd := "openssl", args := #["version"] }).exitCode == 0
  catch _ => return false

def live : Async (List (String × Bool)) := do
  unless ← hasOpenssl do
    IO.eprintln "tls: skipped the local servers, there is no openssl command"
    return ← online
  return (← offline) ++ (← online)

def origin (url : String) : Option (Client.Scheme × String × UInt16) :=
  (Client.Call.at url { method := .get, path := [] }).map fun c => (c.scheme, c.host, c.port)

def tests : List (String × Bool) :=
  [ ("tls: an https origin is called on 443, an http one on 80, unless a port is given",
      origin "https://api.example.com" == some (.https, "api.example.com", 443)
        && origin "https://api.example.com/" == some (.https, "api.example.com", 443)
        && origin "http://10.0.0.1" == some (.http, "10.0.0.1", 80)
        && origin "HTTPS://s3.amazonaws.com:8443" == some (.https, "s3.amazonaws.com", 8443)
        && origin "http://a:/" == some (.http, "a", 80)),
    ("tls: what is not an origin of http or https is no call",
      [ "ftp://a", "https://", "https://u@a", "https://a/x", "https://a?q", "https://a#f",
        "https://a:0", "https://a:65536", "https://[::1]", "https://a%2e", "a", "/x",
        "https://a b" ].all (origin · == none)) ]

end Tests.Tls
