/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Lib.Postgres.IO.Client

/-!
Where the PostgreSQL client connects, and how, from its host and its environment
(`Lanes/Lib/Postgres/Settings.lean`): no TLS to this machine and full verification elsewhere
unless asked otherwise; libpq's variables before a deploy's; a password file read as libpq reads
it; and what the client cannot do refused with a reason.
-/

namespace Tests.PostgresSettings

open Lanes Lanes.Postgres

def env (vars : List (String × String)) (files : List (String × String) := []) : Env Id where
  var name := vars.lookup name
  file path := files.lookup path
  present path := files.any (·.1 == path)

def read (vars : List (String × String)) (files : List (String × String) := []) :
    Option Settings :=
  (Settings.read (env vars files)).run.toOption

def failed : Option Settings → Bool
  | none => true
  | some _ => false

def defaultTests : List (String × Bool) :=
  let local_ := ["127.0.0.1", "127.3.2.1", "::1", "0:0:0:0:0:0:0:1", "::ffff:127.0.0.1",
    "localhost", "LocalHost", "localhost."]
  let remote := ["10.0.0.5", "db.example.com", "lanes.abc.eu-west-1.rds.amazonaws.com",
    "localhost.example.com", "127.0.0.1.nip.io", "0127.0.0.1", "127.0.0.256", "127.1", "::2",
    "128.0.0.1", "::ffff:10.0.0.1", ""]
  let conn : Conn.Config := { user := "lanes", database := "lanes" }
  [ ("postgres settings: no TLS by default to this machine: 127.0.0.0/8, ::1, localhost",
      local_.all fun h => SslMode.defaultFor h == .disable),
    ("postgres settings: TLS with full verification by default to any other host",
      remote.all fun h => SslMode.defaultFor h == .verifyFull),
    ("postgres settings: localhost is reached at 127.0.0.1 without DNS; a name is resolved",
      Address.of "localhost" == Address.of "127.0.0.1" && Address.of "LOCALHOST." == Address.of "127.0.0.1"
        && Address.of "10.0.0.5" == .ip (.v4 ⟨10 * 2 ^ 24 + 5, by decide⟩)
        && Address.of "db.example.com" == .name "db.example.com"
        && Address.of "::1" == .ip (.v6 ⟨1, by decide⟩)),
    ("postgres settings: a name goes to its first IPv4 address, or its first IPv6 one if it has none",
      let v4 (s : String) := s.contains '.'
      Address.preferred v4 ["::1", "10.0.0.5", "10.0.0.6"] == some "10.0.0.5"
        && Address.preferred v4 ["2001:db8::1", "2001:db8::2"] == some "2001:db8::1"
        && Address.preferred v4 [] == none),
    ("postgres settings: a client's configuration takes the default for its host, and channel binding where offered",
      ({ host := "127.0.0.1", conn } : Client.Config).sslmode == .disable
        && ({ host := "db.example.com", conn } : Client.Config).sslmode == .verifyFull
        && ({ host := "db.example.com", conn } : Client.Config).conn.channelBinding == .prefer),
    ("postgres settings: an explicit sslmode is kept",
      ({ host := "127.0.0.1", conn, sslmode := .verifyFull } : Client.Config).sslmode == .verifyFull
        && ({ host := "db.example.com", conn, sslmode := .disable } : Client.Config).sslmode == .disable) ]

def deploy : List (String × String) :=
  [("LANES_DB_HOST", "lanes.abc.eu-west-1.rds.amazonaws.com"), ("LANES_DB_PORT", "5432"),
   ("LANES_DB_NAME", "lanes"), ("LANES_DB_USER", "lanes"), ("LANES_DB_CA", "/etc/lanes/db-ca.pem"),
   ("LANES_DB_PASSWORD_FILE", "/run/lanes-app/db-password"), ("USER", "lanes"),
   ("HOME", "/home/lanes")]

def readTests : List (String × Bool) :=
  let secret := [("/run/lanes-app/db-password", "s3cret\n")]
  let pgpass := "# comment\nother:*:*:*:no\n*:5432:lanes\\:x:*:pa:ss\\\\w\nlocalhost:*:*:me:mine\r\n"
  [ ("postgres settings: with nothing set, the user's database on localhost:5432, without TLS",
      read [("USER", "me")] == some
        { host := "localhost", port := 5432, user := "me", database := "me", password := none,
          sslmode := .disable, rootCert := none, channelBinding := .prefer }),
    ("postgres settings: a deploy's variables give its endpoint by name, its password file, its authorities and full verification",
      read deploy secret == some
        { host := "lanes.abc.eu-west-1.rds.amazonaws.com", port := 5432, user := "lanes",
          database := "lanes", password := some "s3cret", sslmode := .verifyFull,
          rootCert := some "/etc/lanes/db-ca.pem", channelBinding := .prefer }),
    ("postgres settings: the deploy's bundle is used when it is there, and the system's authorities otherwise",
      ((read [("USER", "me"), ("PGHOST", "db.example.com")] [("/etc/lanes/db-ca.pem", "")]).map
        (·.rootCert) == some (some "/etc/lanes/db-ca.pem"))
      && ((read [("USER", "me"), ("PGHOST", "db.example.com")]).map (·.rootCert) == some none)
      && ((read [("USER", "me"), ("PGSSLROOTCERT", "system")] [("/etc/lanes/db-ca.pem", "")]).map
        (·.rootCert) == some none)),
    ("postgres settings: libpq's variables come before the deploy's, and an empty one is unset",
      (read (("PGHOST", "other.example") :: ("PGUSER", "") :: ("PGPASSWORD", "pw") :: deploy) secret).map
        (fun s => (s.host, s.user, s.password)) == some ("other.example", "lanes", some "pw")),
    ("postgres settings: PGSSLMODE overrides the default; verify-ca and require check the chain",
      ((read [("USER", "me"), ("PGSSLMODE", "verify-full")]).map (·.sslmode) == some .verifyFull)
        && ((read [("USER", "me"), ("PGHOST", "db.example"), ("PGSSLMODE", "disable")]).map (·.sslmode) == some .disable)
        && ((read [("USER", "me"), ("PGSSLMODE", "verify-ca")]).map (·.sslmode) == some .require)
        && ((read [("USER", "me"), ("PGSSLMODE", "require")]).map (·.sslmode) == some .require)
        && ((read [("USER", "me"), ("PGCHANNELBINDING", "require")]).map (·.channelBinding) == some .require)),
    ("postgres settings: what the client cannot do is refused: prefer, allow, a socket, several hosts, a bad port, no user",
      failed (read [("USER", "me"), ("PGSSLMODE", "prefer")])
        && failed (read [("USER", "me"), ("PGSSLMODE", "allow")])
        && failed (read [("USER", "me"), ("PGSSLMODE", "verify")])
        && failed (read [("USER", "me"), ("PGCHANNELBINDING", "yes")])
        && failed (read [("USER", "me"), ("PGHOST", "/var/run/postgresql")])
        && failed (read [("USER", "me"), ("PGHOST", "a.example,b.example")])
        && failed (read [("USER", "me"), ("PGPORT", "0")])
        && failed (read [("USER", "me"), ("PGPORT", "65536")])
        && failed (read [("USER", "me"), ("PGPORT", "x")])
        && failed (read [])),
    ("postgres settings: a password file is read as libpq reads it: escapes, *, comments, the first line that fits",
      PassFile.split "a\\:b:5432:*:u:p:w".toList == ["a:b", "5432", "*", "u", "p:w"]
        && PassFile.find pgpass "db" 5432 "lanes:x" "anyone" == some "pa:ss\\w"
        && PassFile.find pgpass "localhost" 6000 "d" "me" == some "mine"
        && PassFile.find pgpass "db" 6000 "d" "me" == none
        && ((read [("USER", "me"), ("PGPASSFILE", "/p")] [("/p", pgpass)]).map (·.password) == some (some "mine"))
        && ((read [("USER", "me"), ("HOME", "/h")] [("/h/.pgpass", pgpass)]).map (·.password) == some (some "mine"))),
    ("postgres settings: PGPASSWORD comes first; a password file named and missing is refused, ~/.pgpass missing is not",
      ((read [("USER", "me"), ("PGPASSWORD", "pw"), ("PGPASSFILE", "/p")]).map (·.password) == some (some "pw"))
        && failed (read [("USER", "me"), ("PGPASSFILE", "/p")])
        && failed (read [("USER", "me"), ("LANES_DB_PASSWORD_FILE", "/p")])
        && ((read [("USER", "me"), ("HOME", "/h")]).map (·.password) == some none)),
    ("postgres settings: the configuration the settings give",
      match read deploy secret with
      | some s =>
        let cfg := Client.Config.ofSettings s
        cfg.host == s.host && cfg.port == 5432 && cfg.sslmode == .verifyFull
          && cfg.trust == .file "/etc/lanes/db-ca.pem" && cfg.serverName == none
          && cfg.conn.user == "lanes" && cfg.conn.database == "lanes"
          && cfg.conn.password == some "s3cret" && cfg.conn.channelBinding == .prefer
          && cfg.conn.requireScram
      | none => false) ]

def tests : List (String × Bool) := defaultTests ++ readTests

end Tests.PostgresSettings
