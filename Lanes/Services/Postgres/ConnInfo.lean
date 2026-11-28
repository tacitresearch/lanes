/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Lib.Net.Percent

/-!
libpq's connection strings and its service file, read as libpq 18 reads them: a string of
`keyword=value` pairs, a value quoted with `'` or not and `\` taking the next character as it is
(`ConnInfo.keywords`); a URI, `postgresql://user:password@host:port,host:port/dbname?k=v`, its
parts percent-decoded (`ConnInfo.uri`); and the group of one service in a service file
(`ServiceFile.find`). Each gives the options in order, a later one winning (`Options.get`).

A keyword libpq does not know is refused here, as libpq refuses it, and one it knows but the
client does not support is refused by `Settings.read`, with its name. libpq's answers to the same
strings and files are the oracle (`Tests/Oracle/Libpq.lean`, `oracles/libpq/main.py`).
-/

@[expose] public section

namespace Lanes.Postgres

/-- Options as `(keyword, value)`, in the order given. -/
abbrev Options := List (String × String)

/-- The value given last for `keyword`. -/
def Options.get (o : Options) (keyword : String) : Option String :=
  o.reverse.lookup keyword

/-- Each keyword once, with the value given last, in order of keyword. -/
def Options.settled (o : Options) : Options :=
  let keys := (o.map (·.1)).eraseDups
  ((keys.filterMap fun k => (o.get k).map (k, ·)).toArray.qsort (·.1 < ·.1)).toList

namespace ConnInfo

/-- libpq 18's keywords. -/
def libpqKeywords : List String :=
  ["service", "user", "password", "passfile", "channel_binding",
   "connect_timeout", "dbname", "host", "hostaddr", "port", "client_encoding", "options",
   "application_name", "fallback_application_name", "keepalives", "keepalives_idle",
   "keepalives_interval", "keepalives_count", "tcp_user_timeout", "sslmode", "sslnegotiation",
   "sslcompression", "sslcert", "sslkey", "sslcertmode", "sslpassword", "sslrootcert", "sslcrl",
   "sslcrldir", "sslsni", "sslkeylogfile", "requirepeer", "require_auth",
   "ssl_min_protocol_version", "ssl_max_protocol_version", "min_protocol_version",
   "max_protocol_version", "gssencmode", "krbsrvname", "gsslib", "gssdelegation",
   "replication", "target_session_attrs", "load_balance_hosts", "scram_client_key",
   "scram_server_key", "oauth_issuer", "oauth_client_id", "oauth_client_secret", "oauth_scope"]

def known (keyword : String) : Bool := libpqKeywords.contains keyword

/-- C's `isspace`. -/
def isSpace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0b' || c == '\x0c'

/-- `requiressl`, which libpq still takes: `sslmode=require` for a value that starts with `1`,
`sslmode=prefer` (which `Settings.read` refuses) otherwise. -/
def store (o : Options) (keyword value : String) : Except String Options :=
  if keyword == "requiressl" then
    .ok (o ++ [("sslmode", if value.startsWith "1" then "require" else "prefer")])
  else if known keyword then .ok (o ++ [(keyword, value)])
  else .error s!"{keyword} is not an option libpq knows"

/-- Where the reading of a string of pairs is. -/
inductive At where
  | between
  | name (acc : List Char)
  /-- After the name and a space, before `=`. -/
  | afterName (name : String)
  | beforeValue (name : String)
  | plain (name : String) (acc : List Char) (escaped : Bool)
  | quoted (name : String) (acc : List Char) (escaped : Bool)

def word (acc : List Char) : String := String.ofList acc.reverse

def next (o : Options) : At → Char → Except String (Options × At)
  | .between, c =>
    if isSpace c then .ok (o, .between) else if c == '=' then .ok (o, .beforeValue "")
    else .ok (o, .name [c])
  | .name acc, c =>
    if c == '=' then .ok (o, .beforeValue (word acc))
    else if isSpace c then .ok (o, .afterName (word acc)) else .ok (o, .name (c :: acc))
  | .afterName n, c =>
    if isSpace c then .ok (o, .afterName n) else if c == '=' then .ok (o, .beforeValue n)
    else .error s!"no = after {n}"
  | .beforeValue n, c =>
    if isSpace c then .ok (o, .beforeValue n) else if c == '\'' then .ok (o, .quoted n [] false)
    else if c == '\\' then .ok (o, .plain n [] true) else .ok (o, .plain n [c] false)
  | .plain n acc escaped, c =>
    if escaped then .ok (o, .plain n (c :: acc) false)
    else if isSpace c then do return (← store o n (word acc), .between)
    else if c == '\\' then .ok (o, .plain n acc true) else .ok (o, .plain n (c :: acc) false)
  | .quoted n acc escaped, c =>
    if escaped then .ok (o, .quoted n (c :: acc) false)
    else if c == '\\' then .ok (o, .quoted n acc true)
    else if c == '\'' then do return (← store o n (word acc), .between)
    else .ok (o, .quoted n (c :: acc) false)

def finish (o : Options) : At → Except String Options
  | .between => .ok o
  | .name acc => .error s!"no = after {word acc}"
  | .afterName n => .error s!"no = after {n}"
  | .beforeValue n => store o n ""
  | .plain n acc _ => store o n (word acc)
  | .quoted n _ _ => .error s!"the quoted value of {n} does not end"

/-- A string of `keyword=value` pairs, as libpq's `conninfo_parse` reads it. -/
def keywords (s : String) : Except String Options := do
  let (o, at_) ← s.toList.foldlM (fun (o, at_) c => next o at_ c) ([], At.between)
  finish o at_

/-- A part of a URI, percent-decoded as libpq decodes it: a space refused (libpq 18 asks for
`%20`), `%` and two hex digits, `%00` refused, `+` left as it is; and UTF-8. -/
def decode (s : String) : Except String String :=
  let cs := ((s.toList.dropWhile (· == ' ')).reverse.dropWhile (· == ' ')).reverse
  if cs.contains ' ' then .error s!"{s} has a space: write it %20" else
  match Http.percentDecodeBytes false cs with
  | none => .error s!"{s} is not percent-encoded"
  | some bytes =>
    if bytes.contains 0 then .error s!"{s} decodes to a NUL"
    else match String.fromUTF8? ⟨bytes.toArray⟩ with
      | some t => .ok t
      | none => .error s!"{s} does not decode to UTF-8"

def storeDecoded (o : Options) (keyword raw : String) : Except String Options :=
  if raw.isEmpty then .ok o else do store o keyword (← decode raw)

def split (stop : Char → Bool) (cs : List Char) : List Char × List Char :=
  (cs.takeWhile (!stop ·), cs.dropWhile (!stop ·))

/-- The hosts and ports of a URI's authority: each joined by `,`, and what follows them. -/
def hosts (fuel : Nat) (cs : List Char) (hostAcc portAcc : List Char) :
    Except String (List Char × List Char × List Char) :=
  match fuel with
  | 0 => .error "too many hosts"
  | fuel + 1 => do
    let (host, rest) ← match cs with
      | '[' :: inner =>
        let (h, rest) := split (· == ']') inner
        match rest with
        | [] => .error "an IPv6 address with no ]"
        | _ :: after =>
          if h.isEmpty then .error "an empty IPv6 address"
          else match after with
            | [] => .ok (h, after)
            | c :: _ =>
              if c == ':' || c == '/' || c == '?' || c == ',' then .ok (h, after)
              else .error s!"{c} after an IPv6 address"
      | _ => .ok (split (fun c => c == ':' || c == '/' || c == '?' || c == ',') cs)
    let (port, rest) := match rest with
      | ':' :: after => split (fun c => c == '/' || c == '?' || c == ',') after
      | _ => ([], rest)
    match rest with
    | ',' :: after => hosts fuel after (hostAcc ++ host ++ [',']) (portAcc ++ port ++ [','])
    | _ => .ok (hostAcc ++ host, portAcc ++ port, rest)

/-- The query of a URI: `keyword=value` pairs between `&`, decoded; `ssl=true` is
`sslmode=require`, as libpq takes it from JDBC. -/
def query (o : Options) (q : String) : Except String Options := do
  let parts := q.splitOn "&"
  let parts := if parts.getLast? == some "" then parts.dropLast else parts
  parts.foldlM (init := o) fun o part =>
    match part.splitOn "=" with
    | [k, v] => do
      let k ← decode k
      let v ← decode v
      if k == "ssl" && v == "true" then store o "sslmode" "require" else store o k v
    | [_] => .error s!"no = in {part}"
    | _ => .error s!"more than one = in {part}"

/-- A URI after its scheme, as libpq's `conninfo_uri_parse_options` reads it. -/
def authority (cs : List Char) : Except String Options := do
  let (before, at_) := split (fun c => c == '@' || c == '/') cs
  let (o, cs) ← match at_ with
    | '@' :: after => do
      let (user, password) := split (· == ':') before
      let o ← storeDecoded [] "user" (String.ofList user)
      let o ← match password with
        | _ :: p => storeDecoded o "password" (String.ofList p)
        | [] => pure o
      pure (o, after)
    | _ => pure ([], cs)
  let (host, port, rest) ← hosts (cs.length + 1) cs [] []
  let o ← storeDecoded o "host" (String.ofList host)
  let o ← storeDecoded o "port" (String.ofList port)
  let (o, rest) ← match rest with
    | '/' :: after =>
      let (db, rest) := split (· == '?') after
      pure (← storeDecoded o "dbname" (String.ofList db), rest)
    | _ => pure (o, rest)
  match rest with
  | '?' :: q => query o (String.ofList q)
  | _ => pure o

def schemes : List String := ["postgresql://", "postgres://"]

/-- A URI, `postgresql://` or `postgres://`, as libpq reads it. -/
def uri (s : String) : Option (Except String Options) :=
  schemes.findSome? fun scheme =>
    if s.startsWith scheme then some (authority (s.toList.drop scheme.length)) else none

/-- A connection string: a URI, or `keyword=value` pairs. -/
def parse (s : String) : Except String Options :=
  (uri s).getD (keywords s)

end ConnInfo

namespace ServiceFile

/-- A line without the spaces at its ends, as libpq trims it. -/
def trim (line : String) : String :=
  String.ofList ((line.toList.dropWhile ConnInfo.isSpace).reverse.dropWhile ConnInfo.isSpace).reverse

/-- Whether a trimmed line opens the group of `service`: `[`, the name, `]`, and anything after,
as libpq compares it. -/
def opens (service line : String) : Bool :=
  (service.toList ++ [']']).isPrefixOf (line.toList.drop 1)

/-- Where the reading of a service file is: before the group of the service, in it with what it
gave, or past it. -/
inductive At where
  | before
  | inside (o : Options)
  | done (o : Options)

def line (service : String) (n : Nat) (at_ : At) (raw : String) : Except String At :=
  let l := trim raw
  if l.isEmpty || l.startsWith "#" then .ok at_
  else match at_ with
    | .done o => .ok (.done o)
    | .before => .ok (if l.startsWith "[" && opens service l then .inside [] else .before)
    | .inside o =>
      if l.startsWith "[" then .ok (.done o)
      else match l.splitOn "=" with
        | key :: value =>
          if value.isEmpty then .error s!"line {n} has no ="
          else if key == "service" then .error s!"line {n} names a service inside a service"
          else if !ConnInfo.known key then .error s!"line {n}: {key} is not an option libpq knows"
          else if (o.get key).isSome then .ok (.inside o)
          else .ok (.inside (o ++ [(key, "=".intercalate value)]))
        | [] => .error s!"line {n} has no ="

/-- The options of `service` in a service file, the first of each keyword, as libpq's
`parseServiceFile` reads them: `none` when the file has no group of that name. -/
def find (contents service : String) : Except String (Option Options) := do
  let (_, at_) ← (contents.splitOn "\n").foldlM
    (fun (n, at_) raw => do return (n + 1, ← line service n at_ raw)) (1, At.before)
  return match at_ with
    | .before => none
    | .inside o | .done o => some o

end ServiceFile

end Lanes.Postgres
