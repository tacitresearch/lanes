/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Services.Postgres.IO.Client

/-!
Where the PostgreSQL client connects, and how, from its host and its environment
(`Lanes/Services/Postgres/Settings.lean`): no TLS to this machine and full verification elsewhere
unless asked otherwise; libpq's variables before a deploy's; a password file read as libpq reads
it; and what the client cannot do refused with a reason.
-/

namespace Tests.PostgresSettings

open Lanes Lanes.Postgres

/-- Files are plain and only their owner's unless `modes` says otherwise. -/
def env (vars : List (String × String)) (files : List (String × String) := [])
    (modes : List (String × UInt32) := []) : Env Id where
  var name := vars.lookup name
  file path := files.lookup path
  mode path := (modes.lookup path).orElse fun _ =>
    if files.any (·.1 == path) then some 0o100600 else none

def read (vars : List (String × String)) (files : List (String × String) := [])
    (conninfo : String := "") (modes : List (String × UInt32) := []) : Option Settings :=
  (Settings.read (env vars files modes) conninfo).run.toOption

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
        && ((read [("USER", "me"), ("PGSSLMODE", "verify-ca")]).map (·.sslmode) == some .verifyCa)
        && ((read [("USER", "me"), ("PGSSLMODE", "require")]).map (·.sslmode) == some .verifyCa)
        && ((read [("USER", "me"), ("PGCHANNELBINDING", "require")]).map (·.channelBinding) == some .require)),
    ("postgres settings: what the client cannot do is refused: prefer, allow, a socket, a bad port, no user",
      failed (read [("USER", "me"), ("PGSSLMODE", "prefer")])
        && failed (read [("USER", "me"), ("PGSSLMODE", "allow")])
        && failed (read [("USER", "me"), ("PGSSLMODE", "verify")])
        && failed (read [("USER", "me"), ("PGCHANNELBINDING", "yes")])
        && failed (read [("USER", "me"), ("PGHOST", "/var/run/postgresql")])
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

/-- Connection strings and URIs, as libpq reads them; `Tests/Oracle/Libpq.lean` compares them
with libpq on generated ones. -/
def connInfoTests : List (String × Bool) :=
  let parse (s : String) := (ConnInfo.parse s).toOption.map Options.settled
  [ ("postgres conninfo: keyword=value pairs, quoted, escaped, spaced, the last of a keyword winning",
      parse "host=db port = 5433 dbname='my db' password='it\\'s' user=a\\ b host=other"
        == some [("dbname", "my db"), ("host", "other"), ("password", "it's"), ("port", "5433"),
                 ("user", "a b")]
        && parse "" == some [] && parse "  application_name=  " == some [("application_name", "")]
        && parse "host='x'port=1" == some [("host", "x"), ("port", "1")]),
    ("postgres conninfo: no =, an unknown keyword, an open quote are refused",
      (parse "host").isNone && (parse "host db").isNone && (parse "hots=db").isNone
        && (parse "host='db").isNone && (parse "=x").isNone),
    ("postgres conninfo: a URI's user, password, hosts, ports, database and query, percent-decoded",
      parse "postgresql://me:p%40ss@db.example:5433,[::1],other:6000/my%20db?sslmode=verify-full&application_name=a+b"
        == some [("application_name", "a+b"), ("dbname", "my db"), ("host", "db.example,::1,other"),
                 ("password", "p@ss"), ("port", "5433,,6000"), ("sslmode", "verify-full"),
                 ("user", "me")]
        && parse "postgres://" == some [] && parse "postgresql:///db" == some [("dbname", "db")]
        && parse "postgresql://h?ssl=true" == some [("host", "h"), ("sslmode", "require")]
        && parse "postgresql://h?dbname=a&" == some [("dbname", "a"), ("host", "h")]),
    ("postgres conninfo: a URI with a bad escape, %00, a bad query, an unknown parameter or an open [ is refused",
      (parse "postgresql://h/%zz").isNone && (parse "postgresql://h/a%00").isNone
        && (parse "postgresql://h?a").isNone && (parse "postgresql://h?sslmode=a=b").isNone
        && (parse "postgresql://h?hots=x").isNone && (parse "postgresql://[::1").isNone
        && (parse "postgresql://[]").isNone && (parse "postgresql://[::1]x").isNone
        && (parse "postgresql://h?&").isNone),
    ("postgres conninfo: as libpq 18, a space inside a URI's part is refused and one at its ends dropped; requiressl is sslmode",
      (parse "postgresql://h/my db").isNone && (parse "postgresql://a b").isNone
        && parse "postgresql:// h /d " == some [("dbname", "d"), ("host", "h")]
        && parse "requiressl=1" == some [("sslmode", "require")]
        && parse "requiressl=0" == some [("sslmode", "prefer")]) ]

def serviceFile : String :=
  "# services\n[other]\nhost=wrong\n\n  [app]  \n host=db.example \nport=6432\napplication_name=a=b\n"
    ++ "# a comment\nport=7000\n[next]\nhost=no\n"

def serviceTests : List (String × Bool) :=
  let find (s : String) := (ServiceFile.find serviceFile s).toOption
  let home := [("USER", "me"), ("HOME", "/h")]
  [ ("postgres service file: the group's options, trimmed, the first of each, up to the next group",
      find "app" == some (some [("host", "db.example"), ("port", "6432"), ("application_name", "a=b")])
        && find "none" == some none && find "ap" == some none
        && (ServiceFile.find "[app] trailing\nport=1" "app").toOption == some (some [("port", "1")])),
    ("postgres service file: a line with no =, an unknown keyword, a nested service, a spaced keyword are refused",
      ((ServiceFile.find "[app]\nhost" "app").toOption).isNone
        && ((ServiceFile.find "[app]\nhots=x" "app").toOption).isNone
        && ((ServiceFile.find "[app]\nservice=x" "app").toOption).isNone
        && ((ServiceFile.find "[app]\nhost =x" "app").toOption).isNone
        && ((ServiceFile.find "[other]\nhots=x\n[app]\nhost=a" "app").toOption).isSome),
    ("postgres service: PGSERVICE from ~/.pg_service.conf, then PGSYSCONFDIR's; it beats the variables, the string beats it",
      ((read (("PGSERVICE", "app") :: ("PGHOST", "env.example") :: home) [("/h/.pg_service.conf", serviceFile)]).map
          fun s => (s.host, s.port, s.applicationName)) == some ("db.example", 6432, some "a=b")
        && ((read (("PGSYSCONFDIR", "/etc/pg") :: home) [("/etc/pg/pg_service.conf", serviceFile)]
            "service=app host=given").map (·.host)) == some "given"
        && ((read [("USER", "me"), ("PGSERVICEFILE", "/s")] [("/s", "[x]\nport=1"),
            ("/etc/postgresql-common/pg_service.conf", "[app]\nport=2")] "service=app").map (·.port)) == some 2),
    ("postgres service: one named and in no file, or a file with an error, is refused",
      failed (read (("PGSERVICE", "none") :: home) [("/h/.pg_service.conf", serviceFile)])
        && failed (read (("PGSERVICE", "app") :: home) [("/h/.pg_service.conf", "[app]\nbad")])) ]

def optionTests : List (String × Bool) :=
  let me := [("USER", "me")]
  [ ("postgres options: application_name, its fallback, options and connect_timeout reach the configuration",
      match read me [] "application_name=web options='-c search_path=app' connect_timeout=1" with
      | some s =>
        let cfg := Client.Config.ofSettings s
        cfg.conn.parameters == [("application_name", "web"), ("options", "-c search_path=app")]
          && cfg.connectTimeout_ms == some 2000
      | none => false),
    ("postgres options: PGAPPNAME and PGCONNECT_TIMEOUT; fallback_application_name only without one; 0 is the client's own deadline",
      ((read (("PGAPPNAME", "env") :: me) [] "fallback_application_name=fb").map (·.applicationName)) == some (some "env")
        && ((read me [] "fallback_application_name=fb").map (·.applicationName)) == some (some "fb")
        && ((read (("PGCONNECT_TIMEOUT", " 15 ") :: me)).map (·.connectTimeout_ms)) == some (some 15000)
        && ((read me [] "connect_timeout=0").map (·.connectTimeout_ms)) == some none
        && failed (read me [] "connect_timeout=soon")),
    ("postgres options: several hosts, one port for all or one each, each with its line of the password file",
      let pass := [("/p", "a:5432:*:*:pa\nb:6000:*:*:pb\n")]
      match read (("PGPASSFILE", "/p") :: me) pass "host=a,b port=5432,6000 target_session_attrs=read-write" with
      | some s => s.host == "a" && s.password == some "pa" && s.targetSessionAttrs == .readWrite
          && s.moreHosts == [{ host := "b", port := 6000, password := some "pb" }]
          && s.sslmode == .verifyFull
      | none => false),
    ("postgres options: hosts all on this machine go without TLS by default; ports that do not pair are refused",
      ((read me [] "host=localhost,127.0.0.2 port=5432").map (·.sslmode)) == some .disable
        && failed (read me [] "host=a,b,c port=1,2")
        && failed (read me [] "target_session_attrs=leader")),
    ("postgres options: sslrootcert=system means verify-full, and a weaker mode with it is refused",
      ((read me [] "host=localhost sslrootcert=system").map (fun s => (s.sslmode, s.rootCert))) == some (.verifyFull, none)
        && failed (read me [] "sslrootcert=system sslmode=require")),
    ("postgres options: ~/.postgresql/root.crt before the deploy's bundle; sslnegotiation=direct needs TLS",
      ((read [("USER", "me"), ("HOME", "/h")] [("/h/.postgresql/root.crt", ""), ("/etc/lanes/db-ca.pem", "")]).map
          (·.rootCert)) == some (some "/h/.postgresql/root.crt")
        && ((read me [] "host=db.example sslnegotiation=direct").map (·.direct)) == some true
        && failed (read me [] "host=localhost sslnegotiation=direct")
        && failed (read me [] "sslnegotiation=fast")),
    ("postgres options: what the client does not support is refused by name; TCP keepalives and gssencmode=disable are taken",
      failed (read me [] "sslcert=/c") && failed (read me [] "hostaddr=10.0.0.1")
        && failed (read me [] "gssencmode=require")
        && (read me [] "keepalives=1 keepalives_idle=30 gssencmode=disable sslsni=1 client_encoding=UTF8").isSome),
    ("postgres options: a password file others may read, or not a plain file, is refused, as libpq refuses it",
      let pgpass := [("/h/.pgpass", "*:*:*:*:pw")]
      ((read [("USER", "me"), ("HOME", "/h")] pgpass).map (·.password)) == some (some "pw")
        && failed (read [("USER", "me"), ("HOME", "/h")] pgpass "" [("/h/.pgpass", 0o100640)])
        && failed (read [("USER", "me"), ("HOME", "/h")] pgpass "" [("/h/.pgpass", 0o100604)])
        && failed (read [("USER", "me"), ("PGPASSFILE", "/p")] [("/p", "")] "" [("/p", 0o040700)])
        && PassFile.ownerOnly 0o100600 && PassFile.ownerOnly 0o100400 && !PassFile.ownerOnly 0o100660),
    ("postgres options: a URI gives the settings, its query the options",
      match read me [] "postgresql://app:secret@db.example:6543/shop?application_name=web&sslmode=verify-ca" with
      | some s => s.host == "db.example" && s.port == 6543 && s.user == "app" && s.database == "shop"
          && s.password == some "secret" && s.sslmode == .verifyCa && s.applicationName == some "web"
      | none => false) ]

def tests : List (String × Bool) :=
  defaultTests ++ readTests ++ connInfoTests ++ serviceTests ++ optionTests

end Tests.PostgresSettings
