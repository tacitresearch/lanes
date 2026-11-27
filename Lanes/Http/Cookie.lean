/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Http.Wire

/-!
Cookies (RFC 6265) as data: reading the `Cookie` header of a request, and a `Set-Cookie` header
built from a `Cookie` whose every attribute is named. A cookie whose name or value the header
cannot carry is not set, so a value made from user data cannot add an attribute.

Also the check of where a request comes from that a form takes besides its token: a browser
names the origin of a cross-site `POST`.
-/

@[expose] public section

namespace Lanes.Http

inductive SameSite where
  | strict | lax | none
  deriving DecidableEq, Repr

def SameSite.name : SameSite → String
  | .strict => "Strict"
  | .lax => "Lax"
  | .none => "None"

/-- The defaults are the safe ones: not readable by scripts, sent only over HTTPS, and not sent
with a request another site starts, except a top-level `GET`. -/
structure Cookie where
  name : String
  value : String
  path : String := "/"
  maxAge_s : Option Nat := none
  httpOnly : Bool := true
  secure : Bool := true
  sameSite : SameSite := .lax
  deriving DecidableEq, Repr

/-- The characters RFC 6265 lets a cookie's value hold: visible ASCII but `"`, `,`, `;` and `\`. -/
def cookieOctet (c : Char) : Bool :=
  visible c && c != '"' && c != ',' && c != ';' && c != '\\'

namespace Cookie

def valid (c : Cookie) : Bool :=
  token c.name && c.value.toList.all cookieOctet && c.path.toList.all cookieOctet

/-- What `header` gives after the name and value, in order. -/
def attributes (c : Cookie) : List String :=
  ["Path=" ++ c.path] ++ (c.maxAge_s.map fun s => "Max-Age=" ++ toString s).toList
    ++ (if c.httpOnly then ["HttpOnly"] else []) ++ (if c.secure then ["Secure"] else [])
    ++ ["SameSite=" ++ c.sameSite.name]

def header (c : Cookie) : String :=
  "; ".intercalate ((c.name ++ "=" ++ c.value) :: c.attributes)

/-- The same cookie, expired: a browser that has it drops it. -/
def expired (c : Cookie) : Cookie :=
  { c with value := "", maxAge_s := some 0 }

end Cookie

/-- `chars` without the whitespace around them. -/
def trimBlank (chars : List Char) : List Char :=
  ((chars.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace).reverse

/-- A piece of a `Cookie` header, trimmed and split at its first `=`; `none` without `=` or with
an empty name. -/
def parseCookie (part : List Char) : Option (String × String) :=
  match (trimBlank part).splitOn '=' with
  | name :: value :: rest =>
    if name.isEmpty then none
    else some (String.ofList name, String.ofList (['='].intercalate (value :: rest)))
  | _ => none

/-- The pairs of one `Cookie` header, `a=1; b=2`. -/
def parseCookies (header : String) : List (String × String) :=
  (header.toList.splitOn ';').filterMap parseCookie

namespace Request

def cookies (r : Request) : List (String × String) :=
  (r.headers.filter (·.1 == "cookie")).flatMap (parseCookies ·.2)

def cookie? (r : Request) (name : String) : Option String :=
  (r.cookies.find? (·.1 == name)).map (·.2)

/-- Whether a request may change something on behalf of whoever the cookies name: its `Origin`,
when it has one, is `origin`, and `Sec-Fetch-Site`, when the browser sends it, does not say
another site made it. A request from a program that sends neither is let through; the form token
is what stops a page elsewhere. -/
def sameOrigin (r : Request) (origin : String) : Bool :=
  (r.header? "origin").all (· == origin)
    && (r.header? "sec-fetch-site").all fun site => site == "same-origin" || site == "none"

/-- Whether the body is within `limit` bytes. The server has already refused a body over its
own limit; a route that takes less says so here. -/
def bodyWithin (r : Request) (limit : Nat) : Bool :=
  r.body.size ≤ limit

end Request

namespace Response

/-- Adds the cookie if `Cookie.valid` holds of it, and leaves the response as it was if not. -/
def setCookie (r : Response) (c : Cookie) : Response :=
  if c.valid then r.withHeader "set-cookie" c.header else r

def clearCookie (r : Response) (c : Cookie) : Response :=
  r.setCookie c.expired

/-- For pages that show one user's records: no cache keeps them. -/
def noStore (r : Response) : Response :=
  r.withHeader "cache-control" "no-store"

end Response

end Lanes.Http
