/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Oracle.Basic

/-! `Lanes.Url` against RFC 3986's examples and against Go's `net/url`. -/

namespace Tests.Oracle.Url

open Lanes Lanes.Url

def decodedHex (s : String) : String :=
  Bytes.hex ⟨((Http.percentDecodeBytes false s.toList).getD []).toArray⟩

def hostText : Host → String
  | .ip (.v6 n) => "ip6:" ++ Ip.print (.v6 n)
  | .ip (.v4 n) => "name:" ++ Bytes.hex (Ip.print (.v4 n)).toUTF8
  | .name s => "name:" ++ decodedHex s

def userFields (userinfo : String) : List (String × Json) :=
  match cut ':' userinfo.toList with
  | (user, some password) =>
    [("user", .str (decodedHex (String.ofList user))), ("password", .str (decodedHex (String.ofList password)))]
  | (user, none) => [("user", .str (decodedHex (String.ofList user)))]

def authorityFields (a : Authority) : List (String × Json) :=
  (a.userinfo.map userFields).getD [] ++ [("host", .str (hostText a.host))]
    ++ ((a.port.filter (· ≠ "")).map fun p => [("port", .str p)]).getD []

def urlJson (u : Url) : Json :=
  Json.mkObj <| [("string", .str u.print), ("path", .str u.path)]
    ++ (u.scheme.map fun s => [("scheme", .str s)]).getD []
    ++ (u.authority.map authorityFields).getD []
    ++ (u.query.map fun q => [("query", .str q)]).getD []
    ++ ((u.fragment.filter (· ≠ "")).map fun f => [("fragment", .str f)]).getD []

def grouped (ps : List (String × String)) : Json :=
  let keys := ps.foldl (fun ks (k, _) => if ks.contains k then ks else ks ++ [k]) []
  Json.mkObj (keys.map fun k => (k, .arr (ps.filter (·.1 == k) |>.map (.str ·.2)).toArray))

def pairsOf (s : String) : List (String × String) :=
  let rec go : List String → List (String × String)
    | k :: v :: rest => (k, v) :: go rest
    | _ => []
  go (s.splitOn "\x00")

def sortedByKey (ps : List (String × String)) : List (String × String) :=
  ps.mergeSort fun a b => decide (a.1 ≤ b.1)

def answer (c : Case) : Answer :=
  match c.op, String.fromUTF8? c.input with
  | "parse", some s => (parse s).map urlJson
  | "resolve", some s =>
    match s.splitOn " " with
    | [b, r] => do
      let b ← (parse b).filter (·.scheme.isSome)
      return urlJson (resolve b (← parse r))
    | _ => none
  | "query", some s => (decodeQuery s).map grouped
  | "query-encode", some s => some (.str (encodeQuery (sortedByKey (pairsOf s))))
  | _, _ => none

def rfcExamples : List (String × String) := resolveExamples

/-- RFC 3986 §5.4's examples, by evaluation in the kernel. -/
theorem resolve_examples :
    resolveExamples.all (fun (r, t) => resolveText "http://a/b/c/d;p?q" r == some t) = true := by
  decide

def tests : List (String × Bool) :=
  [ ("url: RFC 3986 §5.4 examples resolve", rfcExamples.all fun (r, t) =>
      resolveText "http://a/b/c/d;p?q" r == some t),
    ("url: components", (parse "HTTP://u:p@[2001:DB8::1]:8080/a/b?c=d#e").map urlJson ==
      some (Json.mkObj [("string", .str "http://u:p@[2001:db8::1]:8080/a/b?c=d#e"),
        ("scheme", .str "http"), ("user", .str "75"), ("password", .str "70"),
        ("host", .str "ip6:2001:db8::1"), ("port", .str "8080"), ("path", .str "/a/b"),
        ("query", .str "c=d"), ("fragment", .str "e")])),
    ("url: refused: spaces, a colon in a relative first segment, bad escapes, bad ports, zones",
      ["a b", "a:b c", "1a:b", "http://a b/", "%", "%4", "%zz", "http://a:b/",
        "http://[::1%25eth0]/", "http://[v1.x]/", "http://[1.2.3.4]/", "http://a@b@c/", "a/b[c]",
        "http://a/#b#c", ":a"].all fun s => (parse s).isNone),
    ("url: normalization (§6.2.2)", ((parse "HTTP://Ex%2dample.COM/%7e/a/./b/../%2e%2E/c%3a?%7E#%41").map
      fun u => u.normalize.print) == some "http://ex-ample.com/~/c%3A?~#A"),
    ("url: queries", decodeQuery "a=1&b=x+y%20z&a=2&&c" ==
        some [("a", "1"), ("b", "x y z"), ("a", "2"), ("c", "")]
      && encodeQuery [("a b", "c&d=e"), ("é", "~")] == "a+b=c%26d%3De&%C3%A9=~"
      && (decodeQuery "a=1;b=2").isNone && (decodeQuery "a=%zz").isNone) ]

def alphabet : List Char :=
  ":/?#[]@!$&'()*+,;=%-._~09azAZ ".toList ++ ['é', '\x7f', '"', '<', '\\', '^', '{', '|']

def schemes : List String := ["http", "https", "HTTP", "ftp", "g", "mailto", "x+y-z.w", "1a", ""]

def segments : List String :=
  ["a", "b", "..", ".", "", "g;x=1", "%2e", "%2E%2e", "%2F", "c:d", "@", "~x", "%7e", "%C3%A9", "é"]

def textGen (alpha : List Char) (n : Nat) : Gen String := Gen.text alpha n

def pctText (n : Nat) : Gen String := do
  let parts ← Gen.list (← Gen.below (n + 1)) do
    match ← Gen.below 6 with
    | 0 => Gen.pick ["%41", "%7e", "%2F", "%25", "%C3%A9", "%3a", "%20"]
    | _ => return String.ofList [← Gen.pick "abcXYZ019-._~!$&'()*+,;=:@/?".toList]
  return String.join parts

def hostGen : Gen String := do
  match ← Gen.below 10 with
  | 0 => return ".".intercalate ((← Gen.list 4 (Gen.below 256)).map toString)
  | 1 => return "[" ++ (← Gen.pick ["::1", "2001:DB8::1", "::ffff:1.2.3.4", "fe80::1%25eth0", "v1.x",
      "1:2:3:4:5:6:7:8", "::", "1.2.3.4", "foo"]) ++ "]"
  | 2 => Gen.pick ["localhost", "Example.COM", "%C3%A9", "%41", "a%2db", "", "01.2.3.4", "1.2.3"]
  | _ => textGen "abcxyzABC019-._~!$&'()*+,;=".toList 8

def pathGen : Gen String := do
  let segs ← Gen.list (← Gen.below 5) (Gen.pick segments)
  let lead ← Gen.chance 60
  return (if lead then "/" else "") ++ "/".intercalate segs

def authorityGen : Gen String := do
  let user ← if ← Gen.chance 20 then pure ((← pctText 4) ++ "@") else pure ""
  let port ← if ← Gen.chance 25 then pure (":" ++ (← textGen "0123456789".toList 5)) else pure ""
  return "//" ++ user ++ (← hostGen) ++ port

def urlGen : Gen String := do
  let scheme ← if ← Gen.chance 70 then pure ((← Gen.pick schemes) ++ ":") else pure ("")
  let authority ← if ← Gen.chance 60 then authorityGen else pure ""
  let path ← pathGen
  let path := if authority ≠ "" && !path.isEmpty && !path.startsWith "/" then "/" ++ path else path
  let query ← if ← Gen.chance 30 then pure ("?" ++ (← pctText 6)) else pure ("")
  let fragment ← if ← Gen.chance 20 then pure ("#" ++ (← pctText 6)) else pure ("")
  return scheme ++ authority ++ path ++ query ++ fragment

def baseGen : Gen String := do
  let s ← urlGen
  if (parse s).any (·.scheme.isSome) || (← Gen.chance 5) then return s
  return "http:" ++ s

def urlText : Gen String := do
  let s ← urlGen
  match ← Gen.below 10 with
  | 0 | 1 | 2 => Gen.mutate alphabet s
  | 3 => Gen.text alphabet 16
  | _ => return s

def refGen : Gen String := do
  match ← Gen.below 4 with
  | 0 => Gen.pick (rfcExamples.map (·.1))
  | 1 => do
    let p ← pathGen
    let q ← if ← Gen.chance 30 then pure ("?" ++ (← pctText 3)) else pure ("")
    let f ← if ← Gen.chance 20 then pure ("#" ++ (← pctText 3)) else pure ("")
    return (if (← Gen.chance 20) && !p.startsWith "/" then "./" else "") ++ p ++ q ++ f
  | _ => do
    let s ← urlGen
    if ← Gen.chance 20 then Gen.mutate (alphabet.filter (· ≠ ' ')) s else return s

def queryText : Gen String := do
  let pairs ← Gen.list (← Gen.below 5) do
    let k ← pctText 3
    let v ← pctText 3
    match ← Gen.below 5 with
    | 0 => return k
    | _ => return k ++ "=" ++ v
  let s := "&".intercalate pairs
  if ← Gen.chance 20 then Gen.mutate (alphabet ++ ['+']) s else return s

def plainText : Gen String :=
  Gen.text ("ab é&=+%;~ /?#".toList) 5

def case : Gen Case := do
  match ← Gen.below 10 with
  | 0 | 1 => return text s!"{← baseGen} {← refGen}" "resolve"
  | 2 => return text (← queryText) "query"
  | 3 => do
    let pairs ← Gen.list (← Gen.below 4) do return s!"{← plainText}\x00{← plainText}"
    return text ("\x00".intercalate pairs) "query-encode"
  | _ => return text (← urlText) "parse"

def rfcChar (c : Char) : Bool :=
  isUnreserved c || isSubDelim c || ":/?#[]@%".contains c

def encodeChar (c : Char) : List Char :=
  String.toList (String.join (c.toString.toUTF8.data.toList.map fun b =>
    "%" ++ String.ofList [Http.hexDigit (b.toNat / 16), Http.hexDigit (b.toNat % 16)]))

/-- Every character that is not allowed outside an IP literal, and every `%` that starts no
percent-encoding, percent-encoded. -/
def encodeOther : List Char → List Char
  | '%' :: h :: l :: rest =>
    if isHex h && isHex l then '%' :: h :: l :: encodeOther rest else encodeChar '%' ++ encodeOther (h :: l :: rest)
  | '%' :: rest => encodeChar '%' ++ encodeOther rest
  | c :: rest => (if rfcChar c && c != '[' && c != ']' then [c] else encodeChar c) ++ encodeOther rest
  | [] => []

/-- The input with every character RFC 3986 does not allow where it stands percent-encoded:
outside the brackets of an IP literal, those of `:/?#[]@` that are not delimiters there. -/
def encodeName (cs : List Char) : List Char :=
  cs.flatMap fun c => if isNameChar c || c == '%' then [c] else encodeChar c

def lastCut (c : Char) (cs : List Char) : List Char × Option (List Char) :=
  match cut c cs.reverse with
  | (after, some before) => (before.reverse, some after.reverse)
  | (all, none) => (all.reverse, none)

/-- The input with every character RFC 3986 does not allow where it stands percent-encoded,
reading the authority as Go does: userinfo up to the last `@`, a port after the last `:`. -/
def rfcSpelling (s : String) : String :=
  let (cs, fragment) := cut '#' s.toList
  let (cs, query) := cut '?' cs
  let query := (query.map ('?' :: encodeOther ·)).getD []
  let fragment := (fragment.map fun f => '#' :: (encodeOther f).flatMap fun c =>
    if c == '#' then encodeChar c else [c]).getD []
  String.ofList (spellingBefore cs).toList ++ String.ofList query ++ String.ofList fragment

where spellingBefore (cs : List Char) : String :=
  let (scheme, hier) := match schemeEnd cs with
    | some (sc, r) => (sc ++ [':'], r)
    | none => ([], cs)
  match hier with
  | '/' :: '/' :: post =>
    let (auth, rest) := breakSlash post
    let (user, host) := match lastCut '@' auth with
      | (u, some h) => (encodeOther u |>.flatMap (fun c => if c == '@' then encodeChar c else [c]), h)
      | (h, none) => ([], h)
    let user := if user.isEmpty && (lastCut '@' auth).2.isNone then [] else user ++ ['@']
    let host := match host with
      | '[' :: inner => match cut ']' inner with
        | (inside, some after) => '[' :: encodeOther inside ++ ']' :: encodeOther after
        | (inside, none) => encodeOther ('[' :: inside)
      | _ => match lastCut ':' host with
        | (name, some port) => encodeName name ++ ':' :: port
        | (name, none) => encodeName name
    String.ofList (encodeOther scheme ++ ['/', '/'] ++ user ++ host ++ encodeOther rest)
  | _ => String.ofList (encodeOther cs)

def withoutString : Answer → Answer
  | some (.obj fields) => some (.obj (fields.filter (·.1 != "string")))
  | a => a

def parsed (c : Case) : Option Url := String.fromUTF8? c.input >>= parse

def halves (c : Case) : Option (String × String) := do
  match (← String.fromUTF8? c.input).splitOn " " with
  | [b, r] => return (b, r)
  | _ => none

def refs (c : Case) : Option (Url × Option Url) := do
  let (b, r) ← halves c
  return (← parse b, parse r)

/-- The result of resolving a case, if both ours and Go's read it. -/
def resolved (c : Case) : Option Url := do
  let (b, r) ← refs c
  return resolve b (← r)

def goAcceptsMore (c : Case) (go : Answer) : Bool :=
  let fixed (s : String) := rfcSpelling s != s && (parse (rfcSpelling s)).isSome
  let fits (s : String) := (parse s).isSome || fixed s
  go.isSome && (answer c).isNone
    && match c.op with
      | "parse" => (String.fromUTF8? c.input).any fixed
      | "resolve" => (halves c).any fun (b, r) => fits b && fits r && (fixed b || fixed r)
      | _ => false

def asciiEscape : List Char → Bool
  | '%' :: d :: rest => ("01234567".contains d && !(d == '2' && rest.head? == some '5')) || asciiEscape rest
  | _ :: rest => asciiEscape rest
  | [] => false

def asciiEscapeIn (u : Url) : Bool :=
  match u.authority with
  | some { host := .name h, .. } => asciiEscape h.toList
  | _ => false

def asciiEscapeInHost (c : Case) (go : Answer) : Bool :=
  go.isNone && (answer c).isSome
    && match c.op with
      | "parse" => (parsed c).any asciiEscapeIn
      | "resolve" => (refs c).any fun (b, r) => asciiEscapeIn b || r.any asciiEscapeIn
      | _ => false

def hostField (go : Answer) (p : String → Bool) : Bool :=
  match go with
  | some (.obj fields) => fields.any fun (k, v) => k == "host" && match v with
    | .str h => p h
    | _ => false
  | _ => false

/-- What is between the brackets of an authority's IP literal. -/
def literal (s : String) : Option (List Char) :=
  let cs := (cut '#' s.toList).1
  let hier := match schemeEnd cs with
    | some (_, r) => r
    | none => cs
  match hier with
  | '/' :: '/' :: post =>
    match (lastCut '@' (breakSlash (cut '?' post).1).1) with
    | (_, some ('[' :: inner)) | ('[' :: inner, none) => (lastCut ']' inner).1
    | _ => none
  | _ => none

def refusedLiteral (c : Case) (go : Answer) (p : List Char → Bool) : Bool :=
  go.isSome && (answer c).isNone
    && match c.op with
      | "parse" => (String.fromUTF8? c.input).any fun s => (literal s).any p
      | "resolve" => (halves c).any fun (b, r) => (literal b).any p || (literal r).any p
      | _ => false

def unchecked (c : Case) (go : Answer) : Bool :=
  refusedLiteral c go fun inside => !inside.contains '%' && (Ip.parse6 inside).isNone

def zone (c : Case) (go : Answer) : Bool :=
  refusedLiteral c go (·.contains '%')

def relativeBase (c : Case) (go : Answer) : Bool :=
  c.op == "resolve" && go.isSome && (answer c).isNone && (refs c).any (·.1.scheme.isNone)

def notText (c : Case) (go : Answer) : Bool :=
  go.isSome && (answer c).isNone && (String.fromUTF8? c.input).isNone

def emptyAuthority : Authority := { host := .name "" }

def isEmptyAuthority (a : Authority) : Bool :=
  a.userinfo.isNone && a.host == .name "" && a.port.isNone

/-- What Go's `URL` cannot hold, dropped from ours. -/
def losses (u : Url) : Url × List String :=
  let (u, r1) := if u.fragment == some "" then ({ u with fragment := none }, ["Go drops an empty fragment"])
    else (u, [])
  let (u, r2) := if u.path.isEmpty && u.authority.any isEmptyAuthority then
      ({ u with authority := none }, ["Go drops an empty authority when the path is empty"])
    else (u, [])
  (u, r1 ++ r2)

/-- Reasons a value's text may differ in Go where its components agree. -/
def spellings (u : Url) : List String :=
  match u.authority with
  | some a =>
    (if a.host matches .ip (.v6 _) then ["Go writes an IP literal as written; ours as RFC 5952 does"] else [])
      ++ (if a.userinfo.isSome || (match a.host with | .name h => h.contains '%' | _ => false) then
        ["Go writes a userinfo and a host re-encoded from their bytes"] else [])
  | none => []

def tripleSlash : String := "Go reads /// without a scheme as a path"

def tripled (text : String) (u : Url) : List (Url × List String) :=
  [(u, [])] ++ if text.startsWith "///" && u.scheme.isNone then
    [({ u with authority := none, path := "//" ++ u.path }, [tripleSlash])]
  else []

/-- Ours, and ours read as Go reads what RFC 3986 and Go read differently. -/
def candidates (c : Case) : List (Url × List String) :=
  match c.op with
  | "parse" => match String.fromUTF8? c.input, parsed c with
    | some s, some u => tripled s u
    | _, _ => []
  | "resolve" => match halves c, refs c with
    | some (_, rText), some (b, some r) =>
      let bases : List (Url × List String) := [(b, [])] ++ if b.scheme.isSome && b.authority.isNone && b.path.toList.head? != some '/'
        then [({ b with path := "/" }, ["Go resolves against a base with no authority and a rootless path as if its path were /"])]
        else []
      let refs : List (Url × List String) := (tripled rText r).flatMap fun ((r', rr) : Url × List String) =>
        [(r', rr)] ++ if r'.scheme.isNone && r'.authority.any isEmptyAuthority then
          [({ r' with authority := none }, rr ++ ["Go reads an empty authority in a reference as none"])]
        else []
      (bases.flatMap fun ((b', rb) : Url × List String) => refs.flatMap fun ((r', rr) : Url × List String) =>
        let t := resolve b' r'
        let opaqueRef : List (Url × List String) := if r'.scheme.isSome && r'.authority.isNone && r'.path.toList.head? != some '/'
          then [({ t with path := r'.path }, ["Go does not remove dot segments from an opaque reference"])]
          else []
        let empty := r'.scheme.isNone && r'.authority.isNone && r'.path.isEmpty
        let opaqueBase := b'.authority.isNone && b'.path.toList.head? != some '/'
        let path := if empty && !opaqueBase && t.path != removeDots t.path then
            ({ t with path := removeDots t.path }, ["Go removes the base's dot segments for a reference with an empty path"])
          else (t, [])
        let query := if empty && r'.query.isNone && path.1.query == some "" then
            ({ path.1 with query := none }, path.2 ++ ["Go drops the base's empty query"])
          else path
        let fragment :=
          if empty && r'.query.isNone && r'.fragment.all (· == "") && b'.fragment.any (· != "") then
            ({ query.1 with fragment := b'.fragment }, query.2 ++ ["Go keeps the base's fragment for an empty reference; RFC 3986 §5.2.2 the reference's"])
          else query
        let goEmpty : List (Url × List String) := if fragment.2.isEmpty then [] else [fragment]
        let firsts : List (Url × List String) := [(t, [])] ++ opaqueRef ++ goEmpty
        let doubled : List (Url × List String) := firsts.filterMap fun (u, r) =>
          if u.path.startsWith "//" then
            some ({ u with path := u.path.drop 1 |>.toString }, r ++ ["Go writes a resolved path that starts with // with one /"])
          else none
        (firsts ++ doubled).flatMap fun ((t', ro) : Url × List String) =>
          let noAuthority : List (Url × List String) := if b.authority.isNone && t'.authority.isNone
            then [({ t' with authority := some emptyAuthority }, ["Go writes an empty authority where the base has none"])]
            else []
          ([(t', [])] ++ noAuthority).map fun ((t'', re) : Url × List String) => (t'', rb ++ rr ++ ro ++ re))
    | _, _ => []
  | _ => []

/-- Go writes a path that decodes to `*` as `*` (go.dev/issue/11202). -/
def star (go : Answer) (u : Url) : Option Url :=
  if Http.percentDecode u.path == some "*" && u.path != "*"
      && go.any (·.getObjValD "path" == .str "*") then some { u with path := "*" }
  else none

def explained (go : Answer) (u : Url) (reasons : List String) : Option String :=
  match star go u with
  | some u' => explained' go u' (reasons ++ ["Go writes a path that decodes to * as *"])
  | none => explained' go u reasons
where explained' (go : Answer) (u : Url) (reasons : List String) : Option String :=
    let (v, lost) := losses u
    let reasons := reasons ++ lost
    if go == some (urlJson v) && !reasons.isEmpty then some ("; ".intercalate reasons)
    else if withoutString go == withoutString (some (urlJson u)) then
      if (go.any (·.getObjValD "string" == .str v.print) || reasons.contains tripleSlash) && !reasons.isEmpty then
        some ("; ".intercalate reasons)
      else if !(spellings u).isEmpty then some ("; ".intercalate (reasons ++ spellings u))
      else none
    else none

/-- Go decodes a query to bytes; ours to text. -/
def queryBytes (c : Case) (go : Answer) : Bool :=
  c.op == "query" && go.isSome && (answer c).isNone
    && (String.fromUTF8? c.input).any fun q =>
      ((q.toList.splitOn '&').filter (· ≠ [])).all fun pair =>
        !pair.contains ';' && (Http.percentDecodeBytes true pair).isSome
      && ((q.toList.splitOn '&').any fun pair =>
        (Http.percentDecodeBytes true pair).any fun bs => (String.fromUTF8? ⟨bs.toArray⟩).isNone)

/-- Go writes a path that starts with `//` after no authority as it is, which then reads as an
empty authority; ours writes `/.//`. -/
def slashesWithoutAuthority (c : Case) (go : Answer) : Bool :=
  (match c.op with
    | "parse" => parsed c
    | "resolve" => resolved c
    | _ => none).any fun (t : Url) => [t, { t with path := (t.path.drop 1).toString }].any fun t =>
    t.authority.isNone && t.path.startsWith "//"
      && match urlJson t with
        | .obj fields => go == some (Json.mkObj (("host", .str "name:")
            :: ("string", .str (String.ofList ((t.scheme.map (String.toList · ++ [':'])).getD [] ++ t.path.toList
              ++ (t.query.map ('?' :: String.toList ·)).getD []
              ++ ((t.fragment.filter (· != "")).map ('#' :: String.toList ·)).getD [])))
            :: (fields.toList.filter (·.1 != "string"))))
        | _ => false

def known (c : Case) (go : Answer) : Option String :=
  if slashesWithoutAuthority c go then
    some "Go writes a path that starts with // after no authority as an authority (and may drop a /)"
  else if queryBytes c go then some "Go decodes a query to bytes that need not be UTF-8; ours to text"
  else if zone c go then some "Go reads a zone (RFC 6874) in an IP literal; ours refuses one, as Lanes.Ip does"
  else if notText c go then some "Go reads bytes that are not UTF-8; RFC 3986 percent-encodes them"
  else if unchecked c go then some "Go does not check the address in an IP literal's brackets"
  else if relativeBase c go then
    some "RFC 3986 §5.1 resolves against an absolute base only; Go against any"
  else if goAcceptsMore c go then some "Go accepts characters RFC 3986 does not allow where they stand"
  else if asciiEscapeInHost c go then
    some "Go refuses a percent-encoded ASCII byte in a host; RFC 3986 §3.2.2 allows it"
  else (candidates c).findSome? fun (u, reasons) => explained go u reasons

def package : Package where
  name := "url"
  edges := (rfcExamples.map fun (r, _) => text s!"http://a/b/c/d;p?q {r}" "resolve")
    ++ ["http://a/b/c/d;p?q", "HTTP://u:p@[2001:DB8::1]:8080/a/b?c=d#e", "mailto:a@b", "//a",
      "a:b", "http://a:/", "http://[::1%25eth0]/", "http://a@b@c/", "http://%41/", "a#"].map
      (text · "parse")
  case := case
  answer := answer
  known := known

end Tests.Oracle.Url
