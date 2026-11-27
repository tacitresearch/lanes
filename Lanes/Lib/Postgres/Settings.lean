/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Lib.Postgres.Conn

/-!
Where a client of PostgreSQL connects, and how, decided purely (rule 3.9).

The TLS a host gets unless the application asks otherwise is `SslMode.defaultFor`: none to this
machine, where no one on a network reads the bytes, and full verification of the certificate
elsewhere, with channel binding where the server offers it (`Conn.ChannelBinding.prefer`). This
machine is `127.0.0.0/8`, `::1` and `localhost`, which the client reaches at `127.0.0.1` without
asking DNS (`Address.of`), so that a name cannot turn TLS off.

`Settings.read` reads libpq's environment variables, then a deploy's (`docs/DEPLOY.md`), then
libpq's defaults, through `Env`, which the IO gives (`Postgres.Client.fromEnv`) and a test fakes.
A password file is libpq's (`PassFile.find`).
-/

@[expose] public section

namespace Lanes.Postgres

/-- Whether the connection is encrypted, and what the server's certificate must be. There is no
`prefer`, which gives TLS up when the server refuses it. -/
inductive SslMode where
  | disable
  /-- TLS, the certificate chained to `trust`, for any name: libpq's `verify-ca`. -/
  | require
  /-- TLS, the certificate chained to `trust` and for `serverName`. -/
  | verifyFull
  deriving DecidableEq, Repr, Hashable

/-- A host as the client reaches it: an IPv4 address, an IPv6 address, or a name, resolved at
each connect. -/
inductive Address where
  | v4 (a b c d : UInt8)
  | v6 (literal : String)
  | name (name : String)
  deriving DecidableEq, Repr

namespace Address

/-- A decimal number from 0 to 255, written without a leading zero. -/
def octet (s : String) : Option UInt8 :=
  match s.toList with
  | [] => none
  | '0' :: _ :: _ => none
  | cs => if cs.all Char.isDigit then (s.toNat?.filter (· < 256)).map Nat.toUInt8 else none

def ofName (host : String) : Address :=
  if host.contains ':' then .v6 host
  else if host.toLower == "localhost" || host.toLower == "localhost." then .v4 127 0 0 1
  else .name host

/-- `localhost` is `127.0.0.1`, as RFC 6761 lets a client decide without asking DNS. -/
def of (host : String) : Address :=
  match host.splitOn "." with
  | [a, b, c, d] =>
    match octet a, octet b, octet c, octet d with
    | some a, some b, some c, some d => .v4 a b c d
    | _, _, _, _ => ofName host
  | _ => ofName host

/-- An address on this machine: `127.0.0.0/8` or `::1`. A name never is. -/
def loopback : Address → Bool
  | .v4 a _ _ _ => a == 127
  | .v6 literal => literal == "::1"
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

/-- libpq's `sslmode`. `require` checks the chain, as libpq's does when it has authorities to
check it against; `allow` and `prefer` are refused, since they give TLS up. -/
def SslMode.ofLibpq : String → Except String SslMode
  | "disable" => .ok .disable
  | "require" | "verify-ca" => .ok .require
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

end PassFile

/-- What a client reads from outside it: a variable, a file's contents, whether a file is there. -/
structure Env (m : Type → Type) where
  var : String → m (Option String)
  file : String → m (Option String)
  present : String → m Bool

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
  deriving DecidableEq, Repr

namespace Settings

/-- Where `infra/app/app-instance.sh` installs RDS's authorities. -/
def deployCa : String := "/etc/lanes/db-ca.pem"

variable {m : Type → Type} [Monad m]

/-- The first of these variables that is set and not empty. -/
def first (env : Env m) : List String → m (Option String)
  | [] => pure none
  | name :: rest => do
    match ← env.var name with
    | some v => if v.isEmpty then first env rest else pure (some v)
    | none => first env rest

def get (env : Env m) (names : List String) : ExceptT String m (Option String) :=
  ExceptT.lift (first env names)

def portOf (s : String) : Except String UInt16 :=
  match s.toNat? with
  | some n => if 0 < n ∧ n < 65536 then .ok n.toUInt16 else .error s!"port {s} is not from 1 to 65535"
  | none => .error s!"port {s} is not a number"

def hostOf (env : Env m) : ExceptT String m String := do
  let host := (← get env ["PGHOST", "LANES_DB_HOST"]).getD "localhost"
  if host.startsWith "/" then
    throw s!"host {host} is a directory of Unix sockets: the client connects over TCP only"
  if host.contains ',' then throw s!"host {host} names several hosts: the client takes one"
  return host

/-- `PGPASSWORD`, else the password file `PGPASSFILE` names, else the file of the password alone
that `LANES_DB_PASSWORD_FILE` names, else `~/.pgpass` if it is there. A file named and not read
is an error. -/
def passwordOf (env : Env m) (host : String) (port : UInt16) (database user : String) :
    ExceptT String m (Option String) := do
  if let some p ← get env ["PGPASSWORD"] then return some p
  if let some path ← get env ["PGPASSFILE"] then
    let some contents ← env.file path | throw s!"the password file {path} cannot be read"
    return PassFile.find contents host port database user
  if let some path ← get env ["LANES_DB_PASSWORD_FILE"] then
    let some contents ← env.file path | throw s!"the password file {path} cannot be read"
    return some contents.trimAscii.toString
  let some home ← get env ["HOME"] | return none
  let some contents ← env.file s!"{home}/.pgpass" | return none
  return PassFile.find contents host port database user

/-- `PGSSLROOTCERT` (`system` for the system's authorities), else `LANES_DB_CA`, else the
deploy's bundle if it is there, else the system's. -/
def rootCertOf (env : Env m) : m (Option String) := do
  match ← first env ["PGSSLROOTCERT"] with
  | some "system" => return none
  | some path => return some path
  | none =>
    if let some path ← first env ["LANES_DB_CA"] then return some path
    if ← env.present deployCa then return some deployCa
    return none

/-- The settings of libpq's variables, else a deploy's, else the defaults: `localhost`, port
5432, the user `USER`, the database named as the user, TLS as `SslMode.defaultFor` the host. -/
def read (env : Env m) : ExceptT String m Settings := do
  let host ← hostOf env
  let port ← match ← get env ["PGPORT", "LANES_DB_PORT"] with
    | some p => ExceptT.mk (pure (portOf p))
    | none => pure 5432
  let some user ← get env ["PGUSER", "LANES_DB_USER", "USER"] | throw "no user: set PGUSER"
  let database := (← get env ["PGDATABASE", "LANES_DB_NAME"]).getD user
  let sslmode ← match ← get env ["PGSSLMODE"] with
    | some s => ExceptT.mk (pure (SslMode.ofLibpq s))
    | none => pure (SslMode.defaultFor host)
  let channelBinding ← match ← get env ["PGCHANNELBINDING"] with
    | some s => ExceptT.mk (pure (channelBindingOfLibpq s))
    | none => pure .prefer
  let rootCert ← ExceptT.lift (rootCertOf env)
  let password ← passwordOf env host port database user
  return { host, port, user, database, password, sslmode, rootCert, channelBinding }

end Settings

end Lanes.Postgres
