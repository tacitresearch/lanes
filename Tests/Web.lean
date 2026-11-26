/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Tests.Gate
import Examples.BankWeb

/-! End-to-end tests of the HTTP adapter over a real socket. -/

namespace Tests.Web

open Lanes Lanes.Http Std Std.Async Tests.Gate

/-- Std has no HTTP client, so this speaks HTTP/1.1 over a TCP socket. -/
def fetch (port : UInt16) (path : String) (method : String := "GET") (body : String := "") :
    Async String := do
  let socket ← TCP.Socket.Client.mk
  socket.connect (.v4 ⟨.ofParts 127 0 0 1, port⟩)
  let head := s!"{method} {path} HTTP/1.1\r\nHost: localhost\r\nConnection: close\r\n"
  let length := if body.isEmpty then "" else s!"Content-Length: {body.utf8ByteSize}\r\n"
  socket.send (head ++ length ++ "\r\n" ++ body).toUTF8
  let mut received := ByteArray.empty
  repeat
    match ← socket.recv? 4096 with
    | some bytes => received := received ++ bytes
    | none => break
  socket.close
  return (String.fromUTF8? received).getD ""

def serveTest : Async (List (String × Bool)) := do
  let server ← serve (Server.system echo) bridge { port := 0 } { record := true }
  let some port := server.port | return [("web: the server reports its port", false)]
  let ok ← fetch port "/"
  let refused ← fetch port "/bad"
  let many ← Async.concurrentlyAll ((List.range 50).toArray.map fun _ => fetch port "/")
  let head ← fetch port "/" (method := "HEAD")
  let options ← fetch port "/" (method := "OPTIONS")
  server.stop
  let events := (← server.trace).toList
  let inputs := events.countP fun
    | .input _ => true
    | _ => false
  let atMost (n : Nat) : Outside (gatedSig echoSig) Nat :=
    { init := 0, allow := fun seen _ => if seen < n then some (seen + 1) else none }
  return [
    ("web: the server does only what the gate's model of its outside allows",
      (Http.outside echoSig).allows events && inputs == 53),
    ("web: a model the run does not fit is rejected", !(atMost 10).allows events),
    ("web: a request is answered through the gate",
      ok.startsWith "HTTP/1.1 200" && ok.endsWith "ok"),
    ("web: a request the bridge refuses gets its response",
      refused.startsWith "HTTP/1.1 400" && refused.endsWith "bad"),
    ("web: fifty concurrent requests are each answered",
      many.all fun response => response.startsWith "HTTP/1.1 200" && response.endsWith "ok"),
    ("web: HEAD is answered as GET without the body",
      head.startsWith "HTTP/1.1 200" && !head.endsWith "ok"),
    ("web: a method no application handles is refused", options.startsWith "HTTP/1.1 405") ]

/-! Links through a real server: what `Route.link` prints, sent over a socket and decoded by
`Std.Http`, must match the route it came from with the value it was printed from. -/

def echoSlug : Route Slug := .get ("echo" /> .slug)

def mute : Service echoSig Unit where
  init := ()
  step _ _ := ((), [])

/-- Answers a slug route itself and lets everything else wait for a system that never answers. -/
def slugBridge : Bridge echoSig where
  decode id request :=
    match echoSlug.match? request with
    | some slug => .error (.text slug.text)
    | none => .ok id
  encode id := some (id, .text "ok")

def edgeSegments : List String :=
  ["plain", "a b", "a/b", "a%b", "a+b", "%41", "é", "a?b", "a#b", "a.b", "...", "a&b=c", "\"q\""]

def linkTest : Async (List (String × Bool)) := do
  let server ← serve (Server.system mute) slugBridge { port := 0, maxBodyBytes := 16 }
  let some port := server.port | return [("web: the server reports its port", false)]
  let echoed ← edgeSegments.mapM fun text => do
    let some slug := Slug.ofString? text | return false
    let response ← fetch port (echoSlug.link slug)
    return response.startsWith "HTTP/1.1 200" && response.endsWith text
  let tooLarge ← fetch port "/upload" (method := "POST") (body := "more than sixteen bytes of body")
  let pending ← IO.Promise.new
  background do pending.resolve (← fetch port "/never")
  Async.sleep 200
  server.stop
  let abandoned ← await pending
  return [
    ("web: a link reaches its route with the value it was printed from, whatever the text",
      echoed.all (·)),
    ("web: a body over the limit is refused", tooLarge.startsWith "HTTP/1.1 413"),
    ("web: stopping with a request in flight answers it and ends",
      abandoned.startsWith "HTTP/1.1 503") ]

/-! The bank over HTTP with a journal: stop the server, start another on the same journal. -/

def durableTest : Async (List (String × Bool)) := do
  let dir := (← IO.getEnv "TMPDIR").getD "/tmp"
  let journal : System.FilePath := s!"{dir}/lanes-web-{← IO.monoNanosNow}.journal"
  let start := serve (Examples.Bank.bank Examples.BankWeb.Acct 100) Examples.BankWeb.bridge
    { port := 0, journal := some journal }
  let server ← start
  let some port := server.port | return [("web: the server reports its port", false)]
  let moved ← fetch port "/transfer" (method := "POST") (body := "src=0&dst=1&amount=30")
  let before ← fetch port "/accounts/1"
  server.stop
  let server ← start
  let some port := server.port | return [("web: the server reports its port", false)]
  let after ← fetch port "/accounts/1"
  let again ← fetch port "/transfer" (method := "POST") (body := "src=1&dst=2&amount=130")
  let last ← fetch port "/accounts/2"
  server.stop
  IO.FS.removeFile journal
  return [
    ("web: the bank behind a journal keeps its balances across a restart",
      moved.startsWith "HTTP/1.1 200" && before.endsWith "<span>130</span>"
        && after.endsWith "<span>130</span>"),
    ("web: and goes on from them, with request ids that are still fresh",
      again.startsWith "HTTP/1.1 200" && last.endsWith "<span>230</span>") ]

def tests : IO (List (String × Bool)) := do
  return (← serveTest.block) ++ (← linkTest.block) ++ (← durableTest.block)

end Tests.Web
