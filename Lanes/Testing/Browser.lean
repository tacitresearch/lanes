/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Testing.Http

/-!
A browser a test scripts: it keeps the cookies a site sets, by name and path, until the site
clears them, and sends them back where their path covers the request; a form is sent encoded,
with the `Origin` of the browser's site, as a browser sends it. It runs no script and follows no
redirect: the test reads the `Location` and decides. A browser for the same site after a restart
is `b.at port`, which shares the cookies.
-/

@[expose] public section

namespace Lanes.Testing

open Lanes.Http Std Std.Async

/-- A cookie the browser keeps. -/
structure Kept where
  name : String
  value : String
  path : String := "/"
  deriving DecidableEq, Repr

structure Browser where
  host : String := "127.0.0.1"
  port : UInt16
  /-- The origin of the site, sent with a form. -/
  origin : String
  cookies : IO.Ref (List Kept)
  timeout_ms : Nat := 15000

def Browser.new (port : UInt16) (origin : String := s!"http://127.0.0.1:{port}") : IO Browser :=
  return { port, origin, cookies := ← IO.mkRef [] }

/-- The same browser, for the site on another port: a server started again. -/
def Browser.at (b : Browser) (port : UInt16) : Browser := { b with port }

/-- What a `Set-Cookie` header keeps: the name, the value and the path; `none` when it clears. -/
def Kept.parse (header : String) : Option (Kept × Bool) := do
  let parts := (header.splitOn ";").map (·.trimAscii.toString)
  let first ← parts.head?
  let name := (first.takeWhile (· != '=')).toString
  if name.isEmpty || name.length == first.length then none
  let value := (first.drop (name.length + 1)).toString
  let attr (key : String) := parts.findSome? fun p =>
    if p.toLower.startsWith (key.toLower ++ "=") then some (p.drop (key.length + 1)).toString else none
  let path := (attr "Path").getD "/"
  let cleared := value.isEmpty || attr "Max-Age" == some "0"
  return ({ name, value, path }, cleared)

/-- Whether a cookie of `path` goes with a request for `segments`. -/
def Kept.covers (c : Kept) (segments : List String) : Bool :=
  let target := "/" ++ "/".intercalate segments
  c.path == "/" || target == c.path || target.startsWith (c.path ++ "/")

def Browser.cookie (b : Browser) (name : String) : IO (Option String) :=
  return ((← b.cookies.get).find? (·.name == name)).map (·.value)

/-- Keeps a cookie as if the site had set it, replacing one of that name and path. -/
def Browser.keep (b : Browser) (c : Kept) : IO Unit :=
  b.cookies.modify fun cs => cs.filter (fun k => k.name != c.name || k.path != c.path) ++ [c]

def Browser.forget (b : Browser) (name : String) : IO Unit :=
  b.cookies.modify (·.filter (·.name != name))

def Browser.record (b : Browser) (r : Response) : IO Unit := do
  for (n, v) in r.headers do
    if n == "set-cookie" then
      if let some (c, cleared) := Kept.parse v then
        if cleared then b.cookies.modify (·.filter fun k => k.name != c.name || k.path != c.path)
        else b.keep c

/-- A request to the site, with the cookies whose path covers it, and the cookies its answer
sets kept. A form is sent encoded, from the browser's origin, with any method but `GET`. -/
def Browser.call (b : Browser) (method : Method) (path : List String)
    (form : List (String × String) := []) (query : List (String × String) := [])
    (headers : List (String × String) := []) : Async (Option Response) := do
  let sent := (← b.cookies.get).filter (·.covers path)
  let cookie := "; ".intercalate (sent.map fun c => s!"{c.name}={c.value}")
  let headers := headers ++ (if sent.isEmpty then [] else [("cookie", cookie)])
    ++ (if method == .get then []
        else [("content-type", "application/x-www-form-urlencoded"), ("origin", b.origin)])
  let body := if method == .get then .empty else (encodeForm form).toUTF8
  let r ← try
      Client.exchange { host := b.host, port := b.port, request := { method, path, query, headers, body } }
        { timeout_ms := b.timeout_ms }
    catch _ => pure none
  if let some r := r then b.record r
  return r

def Browser.get (b : Browser) (path : List String) (query : List (String × String) := [])
    (headers : List (String × String) := []) : Async (Option Response) :=
  b.call .get path (query := query) (headers := headers)

def Browser.post (b : Browser) (path : List String) (form : List (String × String) := [])
    (headers : List (String × String) := []) : Async (Option Response) :=
  b.call .post path form (headers := headers)

/-- Posts a form with the hidden `token` field the page carries, as its form would. -/
def Browser.submit (b : Browser) (page : Option Response) (path : List String)
    (form : List (String × String) := []) (token : String := "csrf") : Async (Option Response) :=
  b.post path ((token, (field page token).getD "") :: form)

end Lanes.Testing
