/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Oracle.Basic
import Lanes.Services.Postgres.ConnInfo

/-!
`Postgres.ConnInfo.parse` and `Postgres.ServiceFile.find` against libpq 16, the system's
`libpq.so.5` (`oracles/libpq/main.py`). A `conninfo` case is a connection string, `keyword=value`
pairs or a URI, built of pieces that reach each rule of libpq's readers (spaces, quotes, `\`,
`=`, percent escapes, IPv6 brackets, several hosts, a query) and then often changed by a
character; the answer is every keyword set and its value. A `service` case is a service file and
a name; the answer is what the group gives of the keywords libpq's connection shows.
-/

namespace Tests.Oracle.Libpq

open Lanes Lanes.Postgres

def obj (o : Options) : Json := Json.mkObj (o.settled.map fun (k, v) => (k, .str v))

/-- The keywords the service cases set and compare: `host` takes only names of this machine,
since libpq starts to connect. -/
def serviceKeys : List String :=
  ["host", "application_name", "fallback_application_name", "options", "password"]

def answer (c : Case) : Answer :=
  match c.op, String.fromUTF8? c.input with
  | "conninfo", some s => (ConnInfo.parse s).toOption.map obj
  | "service", some s => do
    let j ← (Json.parse s).toOption
    let file ← (j.getObjValAs? String "file").toOption
    let name ← (j.getObjValAs? String "service").toOption
    let some o ← (ServiceFile.find file name).toOption | none
    return obj (o.filter fun (k, v) => serviceKeys.contains k && !(k == "options" && v.isEmpty))
  | _, _ => none

namespace Gen

open Tests.Oracle.Gen

def keywords : List String :=
  ["host", "port", "dbname", "user", "password", "application_name", "sslmode", "options",
   "connect_timeout", "service", "hots", "", "ssl", "target_session_attrs", "sslrootcert"]

def valueChars : List Char := "ab1 '\\=&?%/:@,[]#é\t".toList

def plainChars : List Char := "abz09-_.".toList

def word : Gen String := do
  match ← below 4 with
  | 0 => pick ["db", "localhost", "5432", "verify-full", "-c x=1", "", "a b", "it's"]
  | 1 => Tests.Oracle.Gen.text plainChars 6
  | _ => Tests.Oracle.Gen.text valueChars 6

/-- A value as a string of pairs writes it: plain, with `\` before spaces and quotes, or quoted. -/
def written (v : String) : Gen String := do
  let escaped := String.join (v.toList.map fun c =>
    if c == '\\' || c == '\'' then "\\" ++ c.toString else c.toString)
  match ← below 3 with
  | 0 => return "'" ++ escaped ++ "'"
  | 1 => return String.join (v.toList.map fun c =>
      if c == ' ' || c == '\\' then "\\" ++ c.toString else c.toString)
  | _ => return v

def space : Gen String := pick ["", " ", "  ", "\t", "\n"]

def pairs : Gen String := do
  let n ← below 4
  let ps ← list n do
    return (← space) ++ (← pick keywords) ++ (← space) ++ "=" ++ (← space) ++ (← written (← word))
  return " ".intercalate ps ++ (← space)

def escape (s : String) : Gen String := do
  let chars ← s.toList.mapM fun c => do
    if (← chance 20) then return "%" ++ Bytes.hex c.toString.toUTF8 else return c.toString
  return String.join chars

def uriChars : List Char := "ab1:@/?,[]%=&.é".toList

def hostPart : Gen String := do
  let host ← match ← below 5 with
    | 0 => pick ["[::1]", "[2001:db8::1]", "[]", "[::1"]
    | 1 => pure ""
    | _ => do escape (← pick ["db.example", "localhost", "10.0.0.5", "h,x", "a b"])
  let port ← if ← chance 40 then (":" ++ ·) <$> pick ["5432", "", "x", "65536"] else pure ""
  return host ++ port

def uri : Gen String := do
  let scheme ← pick ["postgresql://", "postgres://"]
  let user ← if ← chance 50 then do
      let u ← escape (← pick ["me", "a:b", "", "x%y"])
      let p ← if ← chance 50 then (":" ++ ·) <$> (escape (← pick ["pw", "p@ss", "", "a:b"])) else pure ""
      pure (u ++ p ++ "@")
    else pure ""
  let hosts ← list ((← below 3) + 1) hostPart
  let db ← if ← chance 60 then ("/" ++ ·) <$> (escape (← pick ["shop", "", "my db", "a/b"])) else pure ""
  let query ← if ← chance 50 then do
      let ps ← list ((← below 3) + 1) do
        let k ← pick ["sslmode", "application_name", "ssl", "dbname", "hots", "", "host"]
        let v ← escape (← pick ["require", "true", "web", "", "a=b", "x&y"])
        if ← chance 10 then pure k else pure (k ++ "=" ++ v)
      pure ("?" ++ "&".intercalate ps ++ (if ← chance 20 then "&" else ""))
    else pure ""
  return scheme ++ user ++ ",".intercalate hosts ++ db ++ query

def conninfo : Gen String := do
  let s ← if ← chance 50 then pairs else uri
  if ← chance 40 then mutate (if s.startsWith "postgres" then uriChars else valueChars) s else return s

def headers : List String :=
  ["[app]", "[app] trailing", "  [app]  ", "[ap]", "[app", "[other]", "[]", "[apps]"]

def serviceLine : Gen String := do
  match ← below 10 with
  | 0 => pick ["", "# comment", "   ", "#[app]"]
  | 1 | 2 => pick headers
  | 3 => pick ["hots=x", "service=other", "noequals", "=x", "host =localhost", "port=5432"]
  | _ => do
    let k ← pick ["host", "application_name", "fallback_application_name", "options", "password"]
    let v ← if k == "host" then pick ["localhost", "127.0.0.1"] else Tests.Oracle.Gen.text valueChars 6
    return (← pick ["", " ", "\t"]) ++ k ++ "=" ++ v ++ (← pick ["", " ", "\r"])

def service : Gen String := do
  let lines ← list (← below 8) serviceLine
  let file := "\n".intercalate lines ++ (if ← chance 50 then "\n" else "")
  let name ← pick ["app", "app", "other", "ap"]
  return Json.compress (Json.mkObj [("file", .str file), ("service", .str name)])

end Gen

def edges : List Case :=
  (["host=db port=5432", "host = db", "host='a b' user=me\\ x", "host='open", "hots=x", "=x",
    "a='x'host=y", "postgresql://", "postgres://me:pw@db:5432,[::1]:6000/shop?sslmode=require",
    "postgresql://h?ssl=true", "postgresql://h/%00", "postgresql://h/%zz", "postgresql://[::1",
    "postgresql://h?a=b=c", "postgresql://h?&", "postgresql://h?dbname=x&", "postgresql:///db",
    "postgresql://a@b@c/d", "postgresql://h?sslnegotiation=direct", "sslnegotiation=direct"].map
    (text · "conninfo"))
  ++ ([("[app]\nhost=localhost\napplication_name=a=b\n", "app"), ("[app]\nhots=x", "app"),
       ("[app]\nservice=x", "app"), ("[other]\nhost=localhost", "app"),
       ("[app] x\n options=-c a=1 \n[next]\npassword=no", "app"), ("[app]\noptions=\n", "app")].map
    fun (file, name) => text (Json.compress (Json.mkObj [("file", .str file), ("service", .str name)])) "service")

def notUtf8 : Json := .str "not UTF-8"

/-- Whether a URI escapes a byte of 128 or more, which alone is not UTF-8. -/
def escapesHigh (s : String) : Bool :=
  let rec go : List Char → Bool
    | '%' :: h :: _ :: rest => "89abcdefABCDEF".toList.contains h || go rest
    | _ :: rest => go rest
    | [] => false
  s.startsWith "postgres" && go s.toList

def known (c : Case) (go : Answer) : Option String :=
  let input := (String.fromUTF8? c.input).getD ""
  if answer c == none && (go == some notUtf8 || (go.isSome && escapesHigh input)) then
    some "libpq keeps percent-decoded bytes that are not UTF-8, which a Lean string cannot hold"
  else if (input.splitOn "sslnegotiation").length > 1 && go == none then
    some "sslnegotiation is PostgreSQL 17's; the reference is libpq 16"
  else none

def package : Package where
  name := "libpq"
  reference := .python "libpq"
  edges := edges
  case := do
    if ← Tests.Oracle.Gen.chance 75 then return text (← Gen.conninfo) "conninfo"
    else return text (← Gen.service) "service"
  answer := answer
  known := known
  shrinks := false

end Tests.Oracle.Libpq
