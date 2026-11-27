/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Lib.Net.Ip
public import Lanes.Web.Http.Basic

/-!
URI references as RFC 3986 writes them: a scheme, an authority (userinfo, host, port), a path, a
query and a fragment, each kept as written, percent-encoded. A host is an IP address
(`Lanes.Ip`) or a registered name. `parse` reads the grammar of §3 and §4.1, `print` writes a
value back (`parse_print`), `resolve` is §5.2.2 with `removeDots` the algorithm of §5.2.4, and
`normalize` is §6.2.2 (`normalize_normalize`).

Where RFC 3986 and the WHATWG URL Standard disagree we are RFC 3986, with two exceptions that
browsers make: an IP literal is IPv6 (no IPvFuture), and it has no zone (RFC 6874), as in
`Lanes.Ip`. The scheme is case-insensitive (§3.1) and kept in lowercase.
-/

@[expose] public section

namespace Lanes

namespace Url

def isAlpha (c : Char) : Bool := ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')

def isDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

def isHex (c : Char) : Bool := isDigit c || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

def isUnreserved (c : Char) : Bool := isAlpha c || isDigit c || c == '-' || c == '.' || c == '_' || c == '~'

def isSubDelim (c : Char) : Bool :=
  c == '!' || c == '$' || c == '&' || c == '\'' || c == '(' || c == ')' || c == '*' || c == '+'
    || c == ',' || c == ';' || c == '='

def isPchar (c : Char) : Bool := isUnreserved c || isSubDelim c || c == ':' || c == '@'

def isPathChar (c : Char) : Bool := isPchar c || c == '/'

/-- What a query and a fragment may hold besides percent-encodings. -/
def isQueryChar (c : Char) : Bool := isPchar c || c == '/' || c == '?'

def isUserChar (c : Char) : Bool := isUnreserved c || isSubDelim c || c == ':'

def isNameChar (c : Char) : Bool := isUnreserved c || isSubDelim c

def isSchemeChar (c : Char) : Bool := isAlpha c || isDigit c || c == '+' || c == '-' || c == '.'

/-- Characters that `allowed` admits, and percent-encodings `%HH`. -/
def encoded (allowed : Char → Bool) : List Char → Bool
  | '%' :: h :: l :: rest => isHex h && isHex l && encoded allowed rest
  | '%' :: _ => false
  | c :: rest => allowed c && encoded allowed rest
  | [] => true

def lowerChar (c : Char) : Char := if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c

def lower (cs : List Char) : List Char := cs.map lowerChar

/-- A scheme as `Url` keeps it: a letter, then letters, digits, `+`, `-` and `.`, in lowercase. -/
def schemeOk : List Char → Bool
  | c :: rest => isAlpha c && (c :: rest).all isSchemeChar && lower (c :: rest) == c :: rest
  | [] => false

end Url

inductive Url.Host where
  | ip (a : Ip.Addr)
  /-- A registered name as written, percent-encoded; not an IPv4 address. -/
  | name (text : String)
  deriving DecidableEq, Repr

structure Url.Authority where
  userinfo : Option String := none
  host : Url.Host
  /-- Digits, possibly none (`http://a:/`). -/
  port : Option String := none
  deriving DecidableEq, Repr

/-- A URI reference (RFC 3986 §4.1): absolute when it has a scheme. -/
structure Url where
  scheme : Option String := none
  authority : Option Url.Authority := none
  path : String := ""
  query : Option String := none
  fragment : Option String := none
  deriving DecidableEq, Repr

namespace Url

/-! ### Printing and parsing -/

def Host.chars : Host → List Char
  | .ip (.v4 n) => Ip.print4 n.val
  | .ip (.v6 n) => '[' :: Ip.print6 n.val ++ [']']
  | .name s => s.toList

def Authority.chars (a : Authority) : List Char :=
  (a.userinfo.map (·.toList ++ ['@'])).getD [] ++ a.host.chars
    ++ (a.port.map (':' :: ·.toList)).getD []

/-- The path as written: after no authority, one that starts with `//` (which resolution can
produce) is written `/.//`, as the WHATWG standard writes it, so that it is not read as one. -/
def pathChars (u : Url) : List Char :=
  if u.authority.isNone && u.path.toList.take 2 == ['/', '/'] then '/' :: '.' :: u.path.toList
  else u.path.toList

def chars (u : Url) : List Char :=
  (u.scheme.map (·.toList ++ [':'])).getD [] ++ (u.authority.map ('/' :: '/' :: ·.chars)).getD []
    ++ u.pathChars ++ (u.query.map ('?' :: ·.toList)).getD []
    ++ (u.fragment.map ('#' :: ·.toList)).getD []

def print (u : Url) : String := String.ofList u.chars

/-- What comes before the first `c`, and what follows it if `c` occurs. -/
def cut (c : Char) : List Char → List Char × Option (List Char)
  | [] => ([], none)
  | x :: xs => if x = c then ([], some xs) else (x :: (cut c xs).1, (cut c xs).2)

/-- The text before the first `/`, and the rest from it. -/
def breakSlash : List Char → List Char × List Char
  | [] => ([], [])
  | '/' :: rest => ([], '/' :: rest)
  | c :: rest => (c :: (breakSlash rest).1, (breakSlash rest).2)

/-- The scheme and what follows its colon, if a colon comes before any `/`. -/
def schemeEnd : List Char → Option (List Char × List Char)
  | [] => none
  | ':' :: rest => some ([], rest)
  | '/' :: _ => none
  | c :: rest => (schemeEnd rest).map fun (s, r) => (c :: s, r)

def parseHost : List Char → Option (Host × Option (List Char))
  | '[' :: rest =>
    match cut ']' rest with
    | (inside, some []) => (Ip.parse6 inside).map fun a => (.ip (.v6 a), none)
    | (inside, some (':' :: port)) => (Ip.parse6 inside).map fun a => (.ip (.v6 a), some port)
    | _ => none
  | cs =>
    let host := match Ip.parse4 (cut ':' cs).1 with
      | some a => Host.ip (.v4 a)
      | none => .name (String.ofList (cut ':' cs).1)
    some (host, (cut ':' cs).2)

def parseAuthority (cs : List Char) : Option Authority :=
  let (userinfo, hostPort) := match cut '@' cs with
    | (u, some hp) => (some u, hp)
    | (h, none) => (none, h)
  (parseHost hostPort).map fun (host, port) =>
    { userinfo := userinfo.map String.ofList, host, port := port.map String.ofList }

/-- The split of §3 and Appendix B, before the components are checked. -/
def parseRaw (cs : List Char) : Option Url :=
  let (beforeFragment, fragment) := cut '#' cs
  let (beforeQuery, query) := cut '?' beforeFragment
  let (scheme, hier) := match schemeEnd beforeQuery with
    | some (s, r) => (some s, r)
    | none => (none, beforeQuery)
  let rest : Option (Option Authority × List Char) := match hier with
    | '/' :: '/' :: r => (parseAuthority (breakSlash r).1).map fun a => (some a, (breakSlash r).2)
    | _ => some (none, hier)
  rest.map fun (authority, path) =>
    { scheme := scheme.map (String.ofList ∘ lower), authority, path := String.ofList path,
      query := query.map String.ofList, fragment := fragment.map String.ofList }

def Host.valid : Host → Bool
  | .ip _ => true
  | .name s => encoded isNameChar s.toList && (Ip.parse4 s.toList).isNone

def Authority.valid (a : Authority) : Bool :=
  a.userinfo.all (encoded isUserChar ·.toList) && a.host.valid && a.port.all (·.toList.all isDigit)

/-- The path's form for where it stands (§3.3): after an authority it is empty or starts with
`/`; without one it does not start with `//`; in a relative reference its first segment has no
colon. -/
def pathFits (u : Url) : Bool :=
  match u.authority with
  | some _ => u.path.toList.head?.all (· == '/')
  | none => u.path.toList.take 2 != ['/', '/']
      && (u.scheme.isSome || !(breakSlash u.path.toList).1.contains ':')

/-- The values `parse` returns, and `print` writes so that they read back. -/
def valid (u : Url) : Bool :=
  u.scheme.all (schemeOk ·.toList) && u.authority.all Authority.valid
    && encoded isPathChar u.path.toList && u.query.all (encoded isQueryChar ·.toList)
    && u.fragment.all (encoded isQueryChar ·.toList) && u.pathFits

def parse (s : String) : Option Url := (parseRaw s.toList).filter valid

/-! ### Removing dot segments (§5.2.4) -/

/-- Where `dots` is: at the start of the input, just after a `/`, or inside a segment (whose
characters so far are kept reversed, and which began after a `/` or at the start). -/
inductive Dots where
  | start
  | slash
  | seg (slash : Bool) (acc : List Char)

/-- RFC 3986 §5.2.4, one character at a time. The output buffer is a stack of pieces, the last
first: `(true, s)` is `/s`, and `(false, s)` is a first segment `s` with no `/` before it. -/
def dots : Dots → List Char → List (Bool × List Char) → List (Bool × List Char)
  | .start, '.' :: '.' :: '/' :: rest, out => dots .start rest out
  | .start, '.' :: '/' :: rest, out => dots .start rest out
  | .start, ['.'], out => out
  | .start, ['.', '.'], out => out
  | .start, [], out => out
  | .start, '/' :: rest, out => dots .slash rest out
  | .start, '.' :: '.' :: c :: rest, out => dots (.seg false [c, '.', '.']) rest out
  | .start, '.' :: c :: rest, out => dots (.seg false [c, '.']) rest out
  | .start, c :: rest, out => dots (.seg false [c]) rest out
  | .slash, '.' :: '/' :: rest, out => dots .slash rest out
  | .slash, ['.'], out => (true, []) :: out
  | .slash, '.' :: '.' :: '/' :: rest, out => dots .slash rest out.tail
  | .slash, ['.', '.'], out => (true, []) :: out.tail
  | .slash, [], out => (true, []) :: out
  | .slash, '/' :: rest, out => dots .slash rest ((true, []) :: out)
  | .slash, '.' :: '.' :: c :: rest, out => dots (.seg true [c, '.', '.']) rest out
  | .slash, '.' :: c :: rest, out => dots (.seg true [c, '.']) rest out
  | .slash, c :: rest, out => dots (.seg true [c]) rest out
  | .seg b acc, '/' :: rest, out => dots .slash rest ((b, acc.reverse) :: out)
  | .seg b acc, c :: rest, out => dots (.seg b (c :: acc)) rest out
  | .seg b acc, [], out => (b, acc.reverse) :: out

def piece : Bool × List Char → List Char
  | (true, s) => '/' :: s
  | (false, s) => s

def join (out : List (Bool × List Char)) : List Char := (out.reverse.map piece).flatten

def removeDotsChars (p : List Char) : List Char := join (dots .start p [])

def removeDots (p : String) : String := String.ofList (removeDotsChars p.toList)

/-! ### Resolution (§5.2.2) -/

/-- The path up to and including its last `/`. -/
def directory (p : List Char) : List Char := (p.reverse.dropWhile (· ≠ '/')).reverse

/-- §5.2.3. -/
def merge (base : Url) (path : String) : String :=
  if base.authority.isSome && base.path.isEmpty then "/" ++ path
  else String.ofList (directory base.path.toList ++ path.toList)

/-- The reference `r` resolved against `base` (§5.2.2, strict: a reference with a scheme is
absolute even when the scheme is the base's). -/
def resolve (base r : Url) : Url :=
  if r.scheme.isSome then { r with path := removeDots r.path }
  else if r.authority.isSome then { r with scheme := base.scheme, path := removeDots r.path }
  else if r.path.isEmpty then { base with query := r.query.or base.query, fragment := r.fragment }
  else if r.path.toList.head? = some '/' then
    { base with path := removeDots r.path, query := r.query, fragment := r.fragment }
  else { base with path := removeDots (merge base r.path), query := r.query, fragment := r.fragment }

/-- RFC 3986 §5.4: references and their targets, against the base `http://a/b/c/d;p?q`. -/
def resolveExamples : List (String × String) :=
  [("g:h", "g:h"), ("g", "http://a/b/c/g"), ("./g", "http://a/b/c/g"), ("g/", "http://a/b/c/g/"),
    ("/g", "http://a/g"), ("//g", "http://g"), ("?y", "http://a/b/c/d;p?y"),
    ("g?y", "http://a/b/c/g?y"), ("#s", "http://a/b/c/d;p?q#s"), ("g#s", "http://a/b/c/g#s"),
    ("g?y#s", "http://a/b/c/g?y#s"), (";x", "http://a/b/c/;x"), ("g;x", "http://a/b/c/g;x"),
    ("g;x?y#s", "http://a/b/c/g;x?y#s"), ("", "http://a/b/c/d;p?q"), (".", "http://a/b/c/"),
    ("./", "http://a/b/c/"), ("..", "http://a/b/"), ("../", "http://a/b/"),
    ("../g", "http://a/b/g"), ("../..", "http://a/"), ("../../", "http://a/"),
    ("../../g", "http://a/g"),
    ("../../../g", "http://a/g"), ("../../../../g", "http://a/g"), ("/./g", "http://a/g"),
    ("/../g", "http://a/g"), ("g.", "http://a/b/c/g."), (".g", "http://a/b/c/.g"),
    ("g..", "http://a/b/c/g.."), ("..g", "http://a/b/c/..g"), ("./../g", "http://a/b/g"),
    ("./g/.", "http://a/b/c/g/"), ("g/./h", "http://a/b/c/g/h"), ("g/../h", "http://a/b/c/h"),
    ("g;x=1/./y", "http://a/b/c/g;x=1/y"), ("g;x=1/../y", "http://a/b/c/y"),
    ("g?y/./x", "http://a/b/c/g?y/./x"), ("g?y/../x", "http://a/b/c/g?y/../x"),
    ("g#s/./x", "http://a/b/c/g#s/./x"), ("g#s/../x", "http://a/b/c/g#s/../x"),
    ("http:g", "http:g")]

/-- `r` resolved against `base`, both read with `parse`, printed; `none` unless `base` is
absolute (§5.1). -/
def resolveText (base r : String) : Option String :=
  ((parse base).filter (·.scheme.isSome)).bind fun b => (parse r).map fun r => (resolve b r).print

/-! ### Normalization (§6.2.2) -/

def hexValue (c : Char) : Nat := (Http.hexValue? c).getD 0

def upperHex (c : Char) : Char := if 'a' ≤ c && c ≤ 'f' then Char.ofNat (c.toNat - 32) else c

/-- Percent-encodings of unreserved characters decoded, the others' hex digits in uppercase
(§6.2.2.1, §6.2.2.2); a `%` that starts no encoding is encoded as `%25`. -/
def pct : List Char → List Char
  | '%' :: h :: l :: rest =>
    if isHex h && isHex l then
      if isUnreserved (Char.ofNat (hexValue h * 16 + hexValue l)) then
        Char.ofNat (hexValue h * 16 + hexValue l) :: pct rest
      else '%' :: upperHex h :: upperHex l :: pct rest
    else '%' :: '2' :: '5' :: pct (h :: l :: rest)
  | '%' :: rest => '%' :: '2' :: '5' :: pct rest
  | c :: rest => c :: pct rest
  | [] => []

/-- Letters in lowercase, except the hex digits of percent-encodings. -/
def lowerName : List Char → List Char
  | '%' :: h :: l :: rest => '%' :: h :: l :: lowerName rest
  | c :: rest => lowerChar c :: lowerName rest
  | [] => []

def Host.normalize : Host → Host
  | .ip a => .ip a
  | .name s => .name (String.ofList (lowerName (pct s.toList)))

def Authority.normalize (a : Authority) : Authority :=
  { a with userinfo := a.userinfo.map (String.ofList ∘ pct ∘ String.toList), host := a.host.normalize }

/-- A path whose dot segments mean nothing yet: a relative reference's relative path, which
resolution merges with its base's before it removes them. -/
def relativePath (u : Url) : Bool :=
  u.scheme.isNone && u.authority.isNone && u.path.toList.head? != some '/'

def normalizePath (u : Url) (p : List Char) : List Char :=
  if u.relativePath then pct p else removeDotsChars (pct p)

def normalize (u : Url) : Url where
  scheme := u.scheme.map (String.ofList ∘ lower ∘ String.toList)
  authority := u.authority.map Authority.normalize
  path := String.ofList (normalizePath u u.path.toList)
  query := u.query.map (String.ofList ∘ pct ∘ String.toList)
  fragment := u.fragment.map (String.ofList ∘ pct ∘ String.toList)

/-! ### Queries -/

/-- `application/x-www-form-urlencoded` as Go's `QueryEscape` writes it: unreserved bytes as they
are, a space as `+`, every other byte percent-encoded. -/
def queryEscape (s : String) : String :=
  String.ofList (s.toUTF8.data.toList.flatMap fun b =>
    if b == 32 then ['+'] else Http.percentEncodeByte b)

def encodeQuery (params : List (String × String)) : String :=
  "&".intercalate (params.map fun (k, v) => queryEscape k ++ "=" ++ queryEscape v)

/-- A query as `key=value` pairs separated by `&`, `+` read as a space; `none` if an escape is
malformed, a key or value is not UTF-8, or a pair has a `;` (which Go and the WHATWG standard
no longer read as a separator). An empty pair is skipped, a pair without `=` has value `""`. -/
def decodeQuery (q : String) : Option (List (String × String)) :=
  ((q.toList.splitOn '&').filter (· ≠ [])).mapM fun pair =>
    if pair.contains ';' then none
    else
      let (k, v) := match cut '=' pair with
        | (k, some v) => (k, v)
        | (k, none) => (k, [])
      do return (← Http.percentDecode (String.ofList k) true, ← Http.percentDecode (String.ofList v) true)

end Url

end Lanes
