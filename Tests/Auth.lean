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
    ("cookie: a Domain is named after the Path, and one that would add an attribute is not set",
      (Response.empty.setCookie { name := "grant", value := "v", domain := some "example.com" }).headers
        == [("set-cookie", "grant=v; Path=/; Domain=example.com; HttpOnly; Secure; SameSite=Lax")]
        && (Response.empty.setCookie
          { name := "grant", value := "v", domain := some "example.com; Max-Age=9" }).headers == []),
    ("cookie: a __Host- cookie with a Domain, which a browser would drop, is not set",
      (Response.empty.setCookie
        { name := hostCookie "session" true, value := "v", domain := some "example.com" }).headers
        == []),
    ("cookie: a name that is not a token is not set",
      (Response.empty.setCookie { name := "a b", value := "v" }).headers == []),
    ("cookie: a Secure cookie is named __Host-, one over plain HTTP is not",
      hostCookie "session" true == "__Host-session" && hostCookie "session" false == "session"
        && (Response.empty.setCookie { name := hostCookie "session" true, value := "v" }).headers
          == [("set-cookie", "__Host-session=v; Path=/; HttpOnly; Secure; SameSite=Lax")]),
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

def keys : Keys := { current := ⟨1, key⟩ }

def otherKeys : Keys := { current := ⟨1, other⟩ }

def tokenTests : List (String × Bool) :=
  let token := sign keys "session" 2000 "7.alice"
  let flip (t : String) (i : Nat) :=
    String.ofList (t.toList.set i (if t.toList[i]? == some '0' then '1' else '0'))
  let rotated := keys.rotate ⟨2, other⟩
  [ ("token: a signed payload verifies before its expiry", verify keys "session" 1999 token == some "7.alice"),
    ("token: it reads v1, the key's id, the expiry, the tag and the payload",
      (token.splitOn ".").take 3 == ["v1", "1", "2000"] && (token.splitOn ".")[3]!.length == 64
        && token.endsWith ".7.alice"),
    ("token: an expired token does not, at its expiry or after",
      verify keys "session" 2000 token == none && verify keys "session" 3000 token == none),
    ("token: a changed expiry does not", verify keys "session" 0 (token.replace ".2000." ".9000.") == none),
    ("token: a changed payload does not", verify keys "session" 0 (token ++ "x") == none),
    ("token: a changed tag does not", verify keys "session" 0 (flip token 15) == none),
    ("token: another key's token does not", verify otherKeys "session" 0 token == none),
    ("token: a token naming a key id the keys do not have does not",
      verify keys "session" 0 (token.replace "v1.1." "v1.2.") == none),
    ("token: another version does not", verify keys "session" 0 (token.replace "v1." "v2.") == none),
    ("token: a token for another purpose does not", verify keys "form" 0 token == none),
    ("token: a payload without a tag does not", verify keys "session" 0 "7.alice" == none),
    ("token: after a rotation, a token of the old key verifies and new ones are of the new key",
      verify rotated "session" 0 token == some "7.alice"
        && (sign rotated "session" 2000 "7.alice").startsWith "v1.2.2000."
        && verify rotated "session" 0 (sign rotated "session" 2000 "7.alice") == some "7.alice"
        && verify keys "session" 0 (sign rotated "session" 2000 "7.alice") == none),
    ("token: once the old key is dropped, its tokens do not verify",
      verify { current := ⟨2, other⟩ } "session" 0 token == none),
    ("token: a form token is checked, and another session's is refused",
      checkForm keys token (formToken keys token)
        && (formToken keys token).startsWith "v1.1."
        && !checkForm keys token (formToken keys (sign keys "session" 2000 "8.alice"))
        && !checkForm keys token ""),
    ("token: a form token of the old key passes after a rotation, and none after the key is dropped",
      checkForm rotated token (formToken keys token)
        && !checkForm { current := ⟨2, other⟩ } token (formToken keys token)) ]

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
    ("sessions: a closed session is not live", !(thrice.close 3).live 3),
    ("sessions: with an idle lifetime, a session lets in until it has been idle that long",
      let life : Lifetime := { idle_s := some 60 }
      let s := (({} : Sessions).start 4 1 1000 life).1
      s.accepts life 1 1059 && !s.accepts life 1 1060 && !s.accepts life 2 1000
        && (s.touch life 1 1050).accepts life 1 1100 && !(s.touch life 1 1060).accepts life 1 1060),
    ("sessions: an absolute lifetime ends a session however recently it was used",
      let life : Lifetime := { idle_s := some 60, absolute_s := some 100 }
      let s := (((({} : Sessions).start 4 1 1000 life).1.touch life 1 1050).touch life 1 1090)
      s.accepts life 1 1099 && !s.accepts life 1 1100),
    ("sessions: a session over is swept by the next write, and a clock stepped back does not revive it",
      let life : Lifetime := { idle_s := some 60 }
      let s := (({} : Sessions).start 4 1 1000 life).1
      let (later, closed) := s.start 4 2 1100 life
      later.ids == [2] && closed == [1] && !later.accepts life 1 1000
        && !((s.sweep life 1100).1.accepts life 1 1000)
        && ((s.sweep life 1100).1.accepts life 2 1000 == false)),
    ("sessions: without a lifetime, none is ever over",
      let s := (({} : Sessions).start 4 1 1000).1
      s.accepts {} 1 (1000 + 10 ^ 9) && (s.sweep {} (10 ^ 9)).2.isEmpty),
    ("password: a digest prints as its first eight hex digits only, and hashes as its bytes",
      reprStr alice == "<digest " ++ String.ofList (alice.hex.toList.take 8) ++ ">"
        && hash alice == hash (password.digest "alice" "correct horse")) ]

def salt16 (b : UInt8) : {s : ByteArray // s.size = 16} :=
  ⟨⟨(List.replicate 16 b).toArray⟩, by simp [ByteArray.size]⟩

def hashTests : List (String × Bool) :=
  let stored := Stored.phc (password.hash (salt16 7).1 (salt16 7).2 "correct horse")
  let raised : Password := { password with cost := { ops := 2, mem_kib := 64 } }
  let repeppered : Password := { password with pepper := "another pepper".toUTF8 }
  let legacy := Stored.raw (password.digest "alice" "correct horse")
  [ ("password: a hash verifies its password, and no other",
      password.verify "alice" "correct horse" stored == .ok
        && password.verify "alice" "correct horsf" stored == .wrong),
    ("password: it is a PHC string of its cost and salt, which reads back",
      stored.text.startsWith "$argon2id$v=19$m=64,t=1,p=1$BwcHBwcHBwcHBwcHBwcHBw$"
        && Stored.read? stored.text == some stored),
    ("password: after the cost is raised, it still verifies, and asks to be hashed again",
      raised.verify "alice" "correct horse" stored == .rehash
        && raised.verify "alice" "wrong" stored == .wrong),
    ("password: the pepper does not change a hash's verdict",
      repeppered.verify "alice" "correct horse" stored == .ok),
    ("password: a digest stored before verifies under its cost and pepper, and asks to be hashed again",
      password.verify "alice" "correct horse" legacy == .rehash
        && password.verify "alice" "correct horsf" legacy == .wrong
        && password.verify "bob" "correct horse" legacy == .wrong
        && repeppered.verify "alice" "correct horse" legacy == .wrong),
    ("password: a digest reads back as a digest, and a PHC string as a hash",
      Stored.read? legacy.text == some legacy && legacy.text.length == 64
        && (match Stored.read? stored.text with | some (.phc _) => true | _ => false)),
    ("password: a stored value that is neither does not read",
      Stored.read? "$argon2i$v=19$m=64,t=1,p=1$BwcHBwcHBwcHBwcHBwcHBw$AAAA" == none
        && Stored.read? "$argon2id$v=19$m=64,t=1,p=1$c2hvcnQ$AAAA" == none
        && Stored.read? "$argon2id$v=19$m=4,t=1,p=1$BwcHBwcHBwcHBwcHBwcHBw$AAAA" == none
        && Stored.read? "$argon2id$v=19$m=64,t=0,p=1$BwcHBwcHBwcHBwcHBwcHBw$AAAA" == none
        && Stored.read? "$argon2id$v=19$t=1,m=64,p=1$BwcHBwcHBwcHBwcHBwcHBw$AAAA" == none
        && Stored.read? "zz" == none),
    ("password: a hash prints its cost only",
      match stored with | .phc p => reprStr p == "<argon2id m=64,t=1,p=1>" | .raw _ => false),
    ("password: two hashes of one password under two salts differ",
      stored != Stored.phc (password.hash (salt16 8).1 (salt16 8).2 "correct horse")) ]

def tests : List (String × Bool) :=
  cookieTests ++ tokenTests ++ loginTests ++ hashTests

end Tests.Auth
