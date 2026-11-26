/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-! Cookies, signed tokens, password digests, failed attempts and sessions. -/

namespace Tests.Auth

open Lanes Lanes.Auth Lanes.Http

def key : Hmac.Key := .of "a key for tests".toUTF8

def other : Hmac.Key := .of "another key".toUTF8

def withCookie (header : String) : Request :=
  { method := .get, path := [], headers := [("cookie", header)] }

def cookieTests : List (String × Bool) :=
  let r := withCookie "theme=dark; session=abc.def=; empty="
  [ ("cookie: pairs of a header are read, a value keeps its =",
      r.cookie? "session" == some "abc.def=" && r.cookie? "theme" == some "dark"
        && r.cookie? "empty" == some "" && r.cookie? "missing" == none),
    ("cookie: every Cookie header is read",
      Request.cookie? { method := .get, path := [], headers := [("cookie", "a=1"), ("cookie", "b=2")] }
        "b" == some "2"),
    ("cookie: Set-Cookie names every attribute",
      (Response.empty.setCookie { name := "session", value := "v", maxAge_s := some 60 }).headers
        == [("set-cookie", "session=v; Path=/; Max-Age=60; HttpOnly; Secure; SameSite=Lax")]),
    ("cookie: a value that would add an attribute is not set",
      (Response.empty.setCookie { name := "session", value := "v; Domain=evil" }).headers == []),
    ("cookie: a name that is not a token is not set",
      (Response.empty.setCookie { name := "a b", value := "v" }).headers == []),
    ("cookie: clearing sends an empty value that expires at once",
      (Response.empty.clearCookie { name := "session", value := "v", secure := false }).headers
        == [("set-cookie", "session=; Path=/; Max-Age=0; HttpOnly; SameSite=Lax")]),
    ("origin: a request from another site is refused, one from here or a program passes",
      let post (headers : List (String × String)) : Request :=
        { method := .post, path := [], headers }
      !(post [("origin", "https://evil.example")]).sameOrigin "http://127.0.0.1:8080"
        && !(post [("sec-fetch-site", "cross-site")]).sameOrigin "http://127.0.0.1:8080"
        && (post [("origin", "http://127.0.0.1:8080"), ("sec-fetch-site", "same-origin")]).sameOrigin
          "http://127.0.0.1:8080"
        && (post []).sameOrigin "http://127.0.0.1:8080") ]

def tokenTests : List (String × Bool) :=
  let token := sign key "session" "7.alice"
  let flipped := String.ofList (token.toList.set 3 (if token.toList[3]? == some '0' then '1' else '0'))
  [ ("token: a signed payload verifies", verify key "session" token == some "7.alice"),
    ("token: a changed payload does not", verify key "session" (token ++ "x") == none),
    ("token: a changed tag does not", verify key "session" flipped == none),
    ("token: another key's token does not", verify other "session" token == none),
    ("token: a token for another purpose does not", verify key "form" token == none),
    ("token: a payload without a tag does not", verify key "session" "7.alice" == none),
    ("token: a form token is checked, and another session's is refused",
      checkForm key token (formToken key token)
        && !checkForm key token (formToken key (sign key "session" "8.alice"))
        && !checkForm key token "") ]

def password : Password := { cost := { ops := 1, mem_kib := 64 }, pepper := "pepper".toUTF8 }

def loginTests : List (String × Bool) :=
  let alice := password.digest "alice" "correct horse"
  let started := (({} : Sessions).start 2 1).1
  let (twice, _) := started.start 2 2
  let (thrice, closed) := twice.start 2 3
  [ ("password: a digest depends on the password and on the user",
      alice == password.digest "alice" "correct horse"
        && alice != password.digest "alice" "correct horsf"
        && alice != password.digest "bob" "correct horse"),
    ("password: and on the deployment's pepper",
      alice != ({ password with pepper := "other".toUTF8 }).digest "alice" "correct horse"),
    ("password: a digest is 32 bytes, and reads back from its hex",
      alice.bytes.size == 32 && Digest.ofHex? alice.hex == some alice
        && Digest.ofHex? "zz" == none),
    ("attempts: the limit-th failure locks, and success does not unlock",
      let a := ((({} : Attempts).fail 3).fail 3)
      !a.locked && (a.fail 3).locked && (a.fail 3).succeed.locked && ((a.fail 3).fail 3).failures == 3),
    ("sessions: a third session closes the oldest of two",
      thrice.ids == [3, 2] && closed == [1] && thrice.live 2 && !thrice.live 1),
    ("sessions: a closed session is not live", !(thrice.close 3).live 3) ]

def tests : List (String × Bool) :=
  cookieTests ++ tokenTests ++ loginTests

end Tests.Auth
