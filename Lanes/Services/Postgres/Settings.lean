/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Lib.Net.Ip
public import Lanes.Services.Postgres.Conn
public import Lanes.Services.Postgres.ConnInfo

/-!
Where a client of PostgreSQL connects, and how, decided purely (rule 3.9).

The TLS a host gets unless the application asks otherwise is `SslMode.defaultFor`: none to this
machine, where no one on a network reads the bytes, and full verification of the certificate
elsewhere, with channel binding where the server offers it (`Conn.ChannelBinding.prefer`). This
machine is `127.0.0.0/8`, `::1` and `localhost`, which the client reaches at `127.0.0.1` without
asking DNS (`Address.of`), so that a name cannot turn TLS off.

`Settings.read` takes each option as libpq does: from the connection string the application
gives (`ConnInfo.parse`), else from the service it or `PGSERVICE` names (`ServiceFile.find`, in
`PGSERVICEFILE` or `~/.pg_service.conf`, then `PGSYSCONFDIR/pg_service.conf`), else from libpq's
environment variable, else from a deploy's (`LANES_DB_*`), else libpq's default; through `Env`,
which the IO gives (`Postgres.Client.fromEnv`) and a test fakes. A password file is libpq's
(`PassFile.find`), and is refused when others may read it (`PassFile.ownerOnly`), where libpq
warns and skips it.
-/

@[expose] public section

namespace Lanes.Postgres

/-- Whether the connection is encrypted, and what the server's certificate must be. There is no
`prefer`, which gives TLS up when the server refuses it. -/
inductive SslMode where
  | disable
  /-- TLS, the certificate chained to `trust`, for any name: libpq's `verify-ca`, and its
  `require`, which libpq checks so when it has authorities to check against. -/
  | verifyCa
  /-- TLS, the certificate chained to `trust` and for `serverName`. -/
  | verifyFull
  deriving DecidableEq, Repr, Hashable

/-- A host as the client reaches it: an IP address, or a name, resolved at each connect. -/
inductive Address where
  | ip (a : Ip.Addr)
  | name (name : String)
  deriving DecidableEq, Repr

namespace Address

def localhost : Ip.Addr := .v4 ⟨127 * 2 ^ 24 + 1, by decide⟩

/-- An address as `Ip.parse` reads it, and `localhost` as `127.0.0.1`, which RFC 6761 lets a
client decide without asking DNS. -/
def of (host : String) : Address :=
  match Ip.parse host with
  | some a => .ip a
  | none =>
    if host.toLower == "localhost" || host.toLower == "localhost." then .ip localhost
    else .name host

/-- Which of the addresses DNS gives a name, in its order, a connection goes to: the first IPv4
one, or the first IPv6 one when the name has none. `isV4` says which is which. -/
def preferred {α : Type} (isV4 : α → Bool) (found : List α) : Option α :=
  found.find? isV4 <|> found.head?

theorem preferred_spec {α : Type} {isV4 : α → Bool} {found : List α} {a : α}
    (h : preferred isV4 found = some a) :
    a ∈ found ∧ (isV4 a = true ∨ ∀ b ∈ found, isV4 b = false) := by
  unfold preferred at h
  cases hf : found.find? isV4 with
  | some b =>
    rw [hf] at h
    cases h
    exact ⟨List.mem_of_find?_eq_some hf, .inl (List.find?_some hf)⟩
  | none =>
    rw [hf] at h
    refine ⟨List.mem_of_head? h, .inr fun b hb => ?_⟩
    simpa using List.find?_eq_none.mp hf b hb

theorem preferred_isSome {α : Type} (isV4 : α → Bool) {found : List α} (h : found ≠ []) :
    (preferred isV4 found).isSome := by
  cases found with
  | nil => exact absurd rfl h
  | cons a rest => cases hf : (a :: rest).find? isV4 <;> simp [preferred, hf]

/-- An address on this machine (`Ip.Addr.isLoopback`). A name never is. -/
def loopback : Address → Bool
  | .ip a => a.isLoopback
  | .name _ => false

end Address

/-- No TLS to this machine, full verification elsewhere. -/
def SslMode.defaultFor (host : String) : SslMode :=
  if (Address.of host).loopback then .disable else .verifyFull

theorem SslMode.defaultFor_loopback {host : String} (h : (Address.of host).loopback) :
    SslMode.defaultFor host = .disable := by
  simp [SslMode.defaultFor, h]

theorem SslMode.defaultFor_remote {host : String} (h : (Address.of host).loopback = false) :
    SslMode.defaultFor host = .verifyFull := by
  simp [SslMode.defaultFor, h]

/-- The default goes without TLS only to an address on this machine. -/
theorem SslMode.defaultFor_disable {host : String} (h : SslMode.defaultFor host = .disable) :
    (Address.of host).loopback := by
  cases hl : (Address.of host).loopback
  · simp [SslMode.defaultFor, hl] at h
  · rfl

theorem Address.name_remote (n : String) : (Address.name n).loopback = false := rfl

/-- With several hosts: none only when every one is on this machine. -/
def SslMode.defaultForAll (hosts : List String) : SslMode :=
  if hosts.all fun h => (Address.of h).loopback then .disable else .verifyFull

theorem SslMode.defaultForAll_disable {hosts : List String} (h : SslMode.defaultForAll hosts = .disable) :
    ∀ host ∈ hosts, (Address.of host).loopback := by
  unfold SslMode.defaultForAll at h
  split at h
  · rename_i hall
    simpa using hall
  · cases h

theorem SslMode.defaultForAll_single (host : String) :
    SslMode.defaultForAll [host] = SslMode.defaultFor host := by
  simp [SslMode.defaultForAll, SslMode.defaultFor]

/-- libpq's `sslmode`. `require` checks the chain, as libpq's does when it has authorities to
check it against; `allow` and `prefer` are refused, since they give TLS up. -/
def SslMode.ofLibpq : String → Except String SslMode
  | "disable" => .ok .disable
  | "require" | "verify-ca" => .ok .verifyCa
  | "verify-full" => .ok .verifyFull
  | s@"allow" | s@"prefer" =>
    .error s!"sslmode {s} gives TLS up when the server refuses it: leave PGSSLMODE unset, or use disable, require, verify-ca or verify-full"
  | s => .error s!"sslmode {s} is not one of disable, require, verify-ca or verify-full"

/-- libpq's `channel_binding`. -/
def channelBindingOfLibpq : String → Except String Conn.ChannelBinding
  | "disable" => .ok .disable
  | "prefer" => .ok .prefer
  | "require" => .ok .require
  | s => .error s!"channel_binding {s} is not one of disable, prefer or require"

/-- Which server of several a connection takes: libpq's `target_session_attrs`. -/
inductive TargetSessionAttrs where
  | any
  | readWrite
  | readOnly
  | primary
  | standby
  /-- A standby if any host is one, else any. -/
  | preferStandby
  deriving DecidableEq, Repr, Hashable

def TargetSessionAttrs.ofLibpq : String → Except String TargetSessionAttrs
  | "any" => .ok .any
  | "read-write" => .ok .readWrite
  | "read-only" => .ok .readOnly
  | "primary" => .ok .primary
  | "standby" => .ok .standby
  | "prefer-standby" => .ok .preferStandby
  | s => .error s!"target_session_attrs {s} is not one of any, read-write, read-only, primary, standby or prefer-standby"

/-- What a server says of itself once connected: whether it is a standby, in recovery, and whether
its sessions are read-only by default, which a standby's always are. -/
structure ServerState where
  standby : Bool
  readOnly : Bool
  deriving DecidableEq, Repr

/-- The query that asks it, as libpq asks a server older than 14. -/
def ServerState.query : String :=
  "SELECT pg_catalog.pg_is_in_recovery(), pg_catalog.current_setting('transaction_read_only')"

def ServerState.ofReply : Reply → Option ServerState
  | .rows { rows := [[some standby, some readOnly]], .. } =>
    some { standby := standby == "t", readOnly := readOnly == "on" }
  | _ => none

def TargetSessionAttrs.accepts : TargetSessionAttrs → ServerState → Bool
  | .any, _ => true
  | .readWrite, s => !s.readOnly
  | .readOnly, s => s.readOnly
  | .primary, s => !s.standby
  | .standby, s => s.standby
  | .preferStandby, s => s.standby

/-- What each pass over the hosts asks for: `prefer-standby` asks for a standby, then takes any,
as libpq does. -/
def TargetSessionAttrs.passes : TargetSessionAttrs → List TargetSessionAttrs
  | .preferStandby => [.standby, .any]
  | a => [a]

theorem TargetSessionAttrs.accepts_readWrite {s : ServerState}
    (h : TargetSessionAttrs.readWrite.accepts s) : s.readOnly = false := by
  simpa [TargetSessionAttrs.accepts] using h

theorem TargetSessionAttrs.accepts_primary {s : ServerState}
    (h : TargetSessionAttrs.primary.accepts s) : s.standby = false := by
  simpa [TargetSessionAttrs.accepts] using h

/-- Only the last pass of any attributes takes any server. -/
theorem TargetSessionAttrs.passes_last (a : TargetSessionAttrs) :
    ∃ last, a.passes.getLast? = some last ∧ (∀ s, a.accepts s → last.accepts s) := by
  cases a <;> exact ⟨_, rfl, fun s h => by simp_all [TargetSessionAttrs.accepts]⟩

namespace PassFile

/-- A line split at its first four `:` that no `\` escapes, each part with its escapes taken
off: the fields of libpq's password file, the password last, which may hold `:`. -/
def split (line : List Char) : List String :=
  go line [] []
where
  go : List Char → List Char → List String → List String
    | [], field, done => done ++ [String.ofList field.reverse]
    | '\\' :: c :: rest, field, done => go rest (c :: field) done
    | ':' :: rest, field, done =>
      if done.length < 4 then go rest [] (done ++ [String.ofList field.reverse])
      else go rest (':' :: field) done
    | c :: rest, field, done => go rest (c :: field) done

def fits (pattern value : String) : Bool := pattern == "*" || pattern == value

/-- The password of the first line of a password file, `host:port:database:user:password`, that
fits the connection; `*` fits anything. Lines that start with `#` are comments. -/
def find (contents host : String) (port : UInt16) (database user : String) : Option String :=
  (contents.splitOn "\n").findSome? fun line =>
    let line := if line.endsWith "\r" then (line.dropEnd 1).toString else line
    if line.startsWith "#" then none
    else match split line.toList with
      | [h, p, d, u, password] =>
        if fits h host && fits p (toString port) && fits d database && fits u user then
          some password
        else none
      | _ => none

/-- `st_mode`'s bits: what kind of file, and who may read it. -/
def kind : UInt32 := 0o170000
def regular : UInt32 := 0o100000
def groupOrOthers : UInt32 := 0o077

/-- A password file libpq reads: a plain file that no one but its owner may read, write or run
(`chmod 600`). -/
def ownerOnly (mode : UInt32) : Bool :=
  mode &&& kind == regular && mode &&& groupOrOthers == 0

theorem ownerOnly_bits {mode : UInt32} (h : ownerOnly mode) : mode &&& groupOrOthers = 0 := by
  simp only [ownerOnly, Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

end PassFile

/-- What a client reads from outside it: a variable, a file's contents, a file's mode (`st_mode`)
if the file is there. -/
structure Env (m : Type → Type) where
  var : String → m (Option String)
  file : String → m (Option String)
  mode : String → m (Option UInt32)

/-- A host after the first, tried in order, as libpq tries a list. -/
structure Target where
  host : String
  port : UInt16
  password : Option String
  deriving DecidableEq, Repr

/-- Where and how to connect, as the environment says. -/
structure Settings where
  host : String
  port : UInt16
  user : String
  database : String
  password : Option String
  sslmode : SslMode
  /-- The authorities the server's certificate must chain to, a PEM file; `none` for the
  system's. -/
  rootCert : Option String
  channelBinding : Conn.ChannelBinding
  moreHosts : List Target := []
  applicationName : Option String := none
  /-- Options for the server's session, as `postgres` takes them on its command line. -/
  options : Option String := none
  connectTimeout_ms : Option Nat := none
  targetSessionAttrs : TargetSessionAttrs := .any
  /-- PostgreSQL 17's direct TLS (`sslnegotiation=direct`). -/
  direct : Bool := false
  deriving DecidableEq, Repr

namespace Settings

/-- Where a deploy installs the authorities of its database's certificate, such as RDS's. -/
def deployCa : String := "/etc/lanes/db-ca.pem"

/-- Where libpq looks for the system's service file without `PGSYSCONFDIR`: Debian's and
Ubuntu's packages put it here. -/
def sysconfdir : String := "/etc/postgresql-common"

/-- The variables each option is read from, libpq's first, then a deploy's. -/
def envNames : String → List String
  | "host" => ["PGHOST", "LANES_DB_HOST"]
  | "port" => ["PGPORT", "LANES_DB_PORT"]
  | "dbname" => ["PGDATABASE", "LANES_DB_NAME"]
  | "user" => ["PGUSER", "LANES_DB_USER"]
  | "password" => ["PGPASSWORD"]
  | "passfile" => ["PGPASSFILE"]
  | "sslmode" => ["PGSSLMODE"]
  | "sslrootcert" => ["PGSSLROOTCERT", "LANES_DB_CA"]
  | "sslnegotiation" => ["PGSSLNEGOTIATION"]
  | "channel_binding" => ["PGCHANNELBINDING"]
  | "application_name" => ["PGAPPNAME"]
  | "connect_timeout" => ["PGCONNECT_TIMEOUT"]
  | "options" => ["PGOPTIONS"]
  | "target_session_attrs" => ["PGTARGETSESSIONATTRS"]
  | _ => []

/-- The options the client supports. -/
def supported : List String :=
  ["host", "port", "dbname", "user", "password", "passfile", "sslmode", "sslrootcert",
   "sslnegotiation", "channel_binding", "application_name", "fallback_application_name",
   "connect_timeout", "options", "target_session_attrs", "service"]

/-- Options the client leaves to the system, or whose value is what it does anyway, taken and
not used: TCP keepalives, `gssencmode` short of `require`, `sslsni=1`, `client_encoding` UTF-8. -/
def harmless : String × String → Bool
  | (k, v) =>
    ["keepalives", "keepalives_idle", "keepalives_interval", "keepalives_count",
      "tcp_user_timeout"].contains k
    || (k == "gssencmode" && v != "require") || (k == "sslsni" && v == "1")
    || (k == "client_encoding" && ["utf8", "utf-8", "unicode"].contains v.toLower)

/-- Options libpq knows that the client does not support, refused with their names. -/
def unsupported (o : Options) : Except String Unit :=
  match o.find? fun p => !supported.contains p.1 && !harmless p with
  | some (k, _) => .error s!"the client does not support {k}"
  | none => .ok ()

variable {m : Type → Type} [Monad m]

/-- The first of these variables that is set and not empty. -/
def first (env : Env m) : List String → m (Option String)
  | [] => pure none
  | name :: rest => do
    match ← env.var name with
    | some v => if v.isEmpty then first env rest else pure (some v)
    | none => first env rest

def lift {α : Type} (e : Except String α) : ExceptT String m α := ExceptT.mk (pure e)

def present (env : Env m) (path : String) : m Bool := return (← env.mode path).isSome

/-- The group of `name` in the service file at `path`, if the file is there and has it. -/
def serviceIn (env : Env m) (path name : String) : ExceptT String m (Option Options) := do
  let some contents ← ExceptT.lift (env.file path) | return none
  match ServiceFile.find contents name with
  | .ok found => return found
  | .error e => throw s!"the service file {path}: {e}"

/-- The options of the service the connection string or `PGSERVICE` names: from
`PGSERVICEFILE`, or `~/.pg_service.conf`, then from `PGSYSCONFDIR/pg_service.conf`. A service
named and in neither is an error. -/
def serviceOf (env : Env m) (stated : Options) : ExceptT String m Options := do
  let named ← match (stated.get "service").filter (!·.isEmpty) with
    | some n => pure (some n)
    | none => ExceptT.lift (first env ["PGSERVICE"])
  let some name := named | return []
  let user ← match ← ExceptT.lift (first env ["PGSERVICEFILE"]) with
    | some path => pure (some path)
    | none => pure ((← ExceptT.lift (first env ["HOME"])).map (· ++ "/.pg_service.conf"))
  if let some path := user then
    if let some o ← serviceIn env path name then return o
  let dir := (← ExceptT.lift (first env ["PGSYSCONFDIR"])).getD sysconfdir
  if let some o ← serviceIn env s!"{dir}/pg_service.conf" name then return o
  throw s!"no service {name} in a service file"

/-- Where options are given, before the environment. -/
structure Given where
  string : Options
  service : Options

/-- An option from the connection string, else the service, else its variables. An empty value
is unset. -/
def get (env : Env m) (g : Given) (keyword : String) : m (Option String) := do
  if let some v := (g.string.get keyword).filter (!·.isEmpty) then return some v
  if let some v := (g.service.get keyword).filter (!·.isEmpty) then return some v
  first env (envNames keyword)

def portOf (s : String) : Except String UInt16 :=
  match s.toNat? with
  | some n => if 0 < n ∧ n < 65536 then .ok n.toUInt16 else .error s!"port {s} is not from 1 to 65535"
  | none => .error s!"port {s} is not a number"

def hostOf (host : String) : Except String String :=
  if host.isEmpty then .ok "localhost"
  else if host.startsWith "/" then
    .error s!"host {host} is a directory of Unix sockets: the client connects over TCP only"
  else .ok host

/-- The hosts and their ports: one port for every host, or one each, as libpq pairs them. -/
def hostsOf (host port : Option String) : Except String (List (String × UInt16)) := do
  let hosts ← ((host.getD "").splitOn ",").mapM hostOf
  let ports ← ((port.getD "").splitOn ",").mapM fun p => if p.isEmpty then pure 5432 else portOf p
  if ports.length == 1 then return hosts.map (·, ports.headD 5432)
  if ports.length == hosts.length then return hosts.zip ports
  throw s!"{ports.length} ports for {hosts.length} hosts"

/-- libpq's `connect_timeout`, in seconds: none, or `0` or less, waits as long as the client's
own deadline (`Client.Config.timeout_ms`), and `1` is `2`, as libpq takes it. -/
def timeoutOf (s : String) : Except String (Option Nat) :=
  let t := s.trimAscii.toString
  let (negative, digits) :=
    if t.startsWith "-" then (true, (t.drop 1).toString)
    else if t.startsWith "+" then (false, (t.drop 1).toString) else (false, t)
  match digits.toNat? with
  | some n => .ok (if negative || n == 0 then none else some (max n 2 * 1000))
  | none => .error s!"connect_timeout {s} is not a number of seconds"

/-- The file at `path`, read if it is a password file only its owner may read. A file named
and not there is an error, `~/.pgpass` not there is not. -/
def passFile (env : Env m) (path : String) (named : Bool) : ExceptT String m (Option String) := do
  let some mode ← ExceptT.lift (env.mode path)
    | if named then throw s!"the password file {path} cannot be read" else return none
  unless PassFile.ownerOnly mode do
    throw s!"the password file {path} must be a plain file only its owner may read: chmod 600 it, as libpq asks"
  let some contents ← ExceptT.lift (env.file path) | throw s!"the password file {path} cannot be read"
  return some contents

/-- Each host's password: the option `password` (or `PGPASSWORD`), else the line of the
password file `passfile` (or `PGPASSFILE`) names, else the file of the password alone that
`LANES_DB_PASSWORD_FILE` names, else the line of `~/.pgpass` if it is there. -/
def passwordsOf (env : Env m) (g : Given) (hosts : List (String × UInt16)) (database user : String) :
    ExceptT String m (List (Option String)) := do
  let lines (contents : String) := hosts.map fun (h, p) => PassFile.find contents h p database user
  if let some p ← ExceptT.lift (get env g "password") then return hosts.map fun _ => some p
  if let some path ← ExceptT.lift (get env g "passfile") then
    return lines ((← passFile env path true).getD "")
  if let some path ← ExceptT.lift (first env ["LANES_DB_PASSWORD_FILE"]) then
    let some contents ← ExceptT.lift (env.file path) | throw s!"the password file {path} cannot be read"
    return hosts.map fun _ => some contents.trimAscii.toString
  let some home ← ExceptT.lift (first env ["HOME"]) | return hosts.map fun _ => none
  match ← passFile env s!"{home}/.pgpass" false with
  | some contents => return lines contents
  | none => return hosts.map fun _ => none

/-- `sslrootcert` (`system` for the system's authorities), else `~/.postgresql/root.crt` if it
is there, as libpq looks for it, else the deploy's bundle if it is there, else the system's. -/
def rootCertOf (env : Env m) (g : Given) : m (Option String) := do
  match ← get env g "sslrootcert" with
  | some "system" => return none
  | some path => return some path
  | none =>
    if let some home ← first env ["HOME"] then
      let path := s!"{home}/.postgresql/root.crt"
      if ← present env path then return some path
    if ← present env deployCa then return some deployCa
    return none

/-- TLS as `sslmode` says, else full verification when `sslrootcert` is `system`, as libpq 16
asks, else `SslMode.defaultForAll` the hosts. With the system's authorities any weaker mode is
refused, as libpq refuses it: anyone with a certificate from any public authority could answer. -/
def sslmodeOf (stated rootCert : Option String) (hosts : List String) : Except String SslMode := do
  let mode ← match stated with
    | some s => SslMode.ofLibpq s
    | none => pure (if rootCert == some "system" then .verifyFull else SslMode.defaultForAll hosts)
  if rootCert == some "system" && mode != .verifyFull then
    throw "sslrootcert=system needs sslmode verify-full"
  return mode

def directOf : Option String → Except String Bool
  | none | some "postgres" => .ok false
  | some "direct" => .ok true
  | some s => .error s!"sslnegotiation {s} is not one of postgres or direct"

def option {α : Type} (env : Env m) (g : Given) (keyword : String) (default : α)
    (parse : String → Except String α) : ExceptT String m α := do
  match ← ExceptT.lift (get env g keyword) with
  | some s => lift (parse s)
  | none => pure default

/-- The settings of the connection string `conninfo`, a URI or `keyword=value` pairs, then of
the service, then of libpq's variables, then of a deploy's, then the defaults: `localhost`, port
5432, the user `USER`, the database named as the user, TLS as `SslMode.defaultForAll` the hosts. -/
def read (env : Env m) (conninfo : String := "") : ExceptT String m Settings := do
  let string ← lift (ConnInfo.parse conninfo)
  lift (unsupported string)
  let service ← serviceOf env string
  lift (unsupported service)
  let g : Given := { string, service }
  let get := fun k => ExceptT.lift (get env g k)
  let hosts ← lift (hostsOf (← get "host") (← get "port"))
  let user ← match ← get "user" with
    | some u => pure (some u)
    | none => ExceptT.lift (first env ["USER"])
  let some user := user | throw "no user: set PGUSER"
  let database := (← get "dbname").getD user
  let sslmode ← lift (sslmodeOf (← get "sslmode") (← get "sslrootcert") (hosts.map (·.1)))
  let direct ← lift (directOf (← get "sslnegotiation"))
  if direct && sslmode == .disable then throw "sslnegotiation=direct needs TLS: sslmode is disable"
  let channelBinding ← option env g "channel_binding" .prefer channelBindingOfLibpq
  let targetSessionAttrs ← option env g "target_session_attrs" .any TargetSessionAttrs.ofLibpq
  let connectTimeout_ms ← option env g "connect_timeout" none timeoutOf
  let applicationName ← match ← get "application_name" with
    | some a => pure (some a)
    | none => get "fallback_application_name"
  let rootCert ← ExceptT.lift (rootCertOf env g)
  let passwords ← passwordsOf env g hosts database user
  let targets := (hosts.zip passwords).map fun ((host, port), password) =>
    ({ host, port, password } : Target)
  let first :: moreHosts := targets | throw "no host"
  return { host := first.host, port := first.port, user, database, password := first.password,
           sslmode, rootCert, channelBinding, moreHosts, applicationName,
           options := ← get "options", connectTimeout_ms, targetSessionAttrs, direct }

end Settings

end Lanes.Postgres
