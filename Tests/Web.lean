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
def fetch (port : UInt16) (path : String) (method : String := "GET") (body : String := "")
    (headers : String := "") : Async String := do
  let socket ← TCP.Socket.Client.mk
  socket.connect (.v4 ⟨.ofParts 127 0 0 1, port⟩)
  let head := s!"{method} {path} HTTP/1.1\r\nHost: localhost\r\nConnection: close\r\n{headers}"
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
  let left ← server.inFlight
  server.stop
  let events := (← server.trace).toList
  let inputs := events.countP fun
    | .input _ => true
    | _ => false
  let atMost (n : Nat) : Outside (servedSig echoSig) Nat :=
    { init := 0, allow := fun seen _ => if seen < n then some (seen + 1) else none }
  return [
    ("web: the server does only what the gate's model of its outside allows",
      (servedOutside echoSig).allows events && inputs == 53),
    ("web: a model the run does not fit is rejected", !(atMost 10).allows events),
    ("web: a request is answered through the gate",
      ok.startsWith "HTTP/1.1 200" && ok.endsWith "ok"),
    ("web: a request the bridge refuses gets its response",
      refused.startsWith "HTTP/1.1 400" && refused.endsWith "bad"),
    ("web: fifty concurrent requests are each answered",
      many.all fun response => response.startsWith "HTTP/1.1 200" && response.endsWith "ok"),
    ("web: once each request is answered none is in flight", left == 0),
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
  let unanswered ← server.inFlight
  server.stop
  let abandoned ← await pending
  return [
    ("web: a link reaches its route with the value it was printed from, whatever the text",
      echoed.all (·)),
    ("web: a body over the limit is refused", tooLarge.startsWith "HTTP/1.1 413"),
    ("web: stopping with a request in flight answers it and ends",
      unanswered == 1 && abandoned.startsWith "HTTP/1.1 503") ]

def deadlineTest : Async (List (String × Bool)) := do
  let server ← serve (Server.system mute) slugBridge
    { port := 0, gate := { requestTimeout_ms := 50 } }
  let some port := server.port | return [("web: the server reports its port", false)]
  let answers ← Async.concurrentlyAll ((List.range 10).toArray.map fun _ => fetch port "/never")
  let left ← server.inFlight
  server.stop
  return [
    ("web: requests the system never answers get 504 at their deadline, and none is left in "
      ++ "flight", answers.all (·.startsWith "HTTP/1.1 504") && left == 0) ]

/-! The bank over HTTP with a journal: stop the server, start another on the same journal. -/

def durableTest : Async (List (String × Bool)) := do
  let dir := (← IO.getEnv "TMPDIR").getD "/tmp"
  let journal : System.FilePath := s!"{dir}/lanes-web-{← IO.monoNanosNow}.journal"
  let start := serve (Examples.Bank.bank Examples.BankWeb.Acct 100) Examples.BankWeb.bridge
    { port := 0, journal := some journal } { record := true, snapshotEvery := 4 }
    (some { actors := Examples.Bank.actors Codec.fin 100, out := Examples.Bank.Response.codec })
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
  let taken ← try
      discard <| serve (Examples.Bank.bank Examples.BankWeb.Acct 100) Examples.BankWeb.bridge
        { port, journal := some (journal.addExtension "other") }
      pure false
    catch _ => pure true
  let free ← (Journal.Store.open
    (sys := served (Examples.Bank.bank Examples.BankWeb.Acct 100) Examples.BankWeb.bridge {})
    { path := journal.addExtension "other", input := Codec.pair Codec.nat Request.codec
      system := ServerConfig.journalName {} }).toBaseIO
  if let .ok log := free then log.close
  server.stop
  let ids := (← server.trace).toList.filterMap fun
    | .input (id, _) => some id
    | _ => none
  for file in [journal.addExtension "other", (journal.addExtension "other").addExtension "lock"] do
    if ← file.pathExists then IO.FS.removeFile file
  let cut ← (journal.addExtension "snapshot").pathExists
  for file in [journal, journal.addExtension "lock", journal.addExtension "snapshot"] do
    if ← file.pathExists then IO.FS.removeFile file
  return [
    ("web: the bank behind a journal keeps its balances across a restart",
      moved.startsWith "HTTP/1.1 200" && before.endsWith "<span>130</span>"
        && after.endsWith "<span>130</span>"),
    ("web: and goes on from them",
      again.startsWith "HTTP/1.1 200" && last.endsWith "<span>230</span>"),
    ("web: request ids used before the restart are not used again, though the journal was cut",
      cut && ids.length == 3 && ids.all (2 ≤ ·)),
    ("web: a server that cannot bind its port fails, and leaves its journal free",
      taken && free.toOption.isSome) ]

/-- A journal written by `serve` before D42, when the gate was an actor of the system behind it
and the journal was named by the application alone, is refused and left as it was: replayed
through the gate in front it may give a state that gate never reaches. -/
def oldJournalTest : Async (List (String × Bool)) := do
  let dir := (← IO.getEnv "TMPDIR").getD "/tmp"
  let journal : System.FilePath := s!"{dir}/lanes-web-old-{← IO.monoNanosNow}.journal"
  let old := Journal.file (σ := servedSig echoSig) (Codec.pair Codec.nat Request.codec) "echo 1"
    [.input (0, get [])]
  IO.FS.writeBinFile journal old
  let config : ServerConfig := { port := 0, journal := some journal, system := "echo 1" }
  let refusal ← try
      (← serve (Server.system echo) bridge config).stop
      pure ""
    catch e => pure (toString e)
  let after ← IO.FS.readBinFile journal
  for file in [journal, journal.addExtension "lock"] do
    if ← file.pathExists then IO.FS.removeFile file
  return [
    ("web: a journal of the server from before its gate was a front is refused, saying why",
      refusal == s!"lanes: the journal {journal} is refused: it is the journal of \"echo 1\", "
        ++ "not of \"echo 1, behind a gate of 30000 ms and 1024 requests\""),
    ("web: and is left as it was", after == old) ]

/-- A bridge whose `prepare` takes a secret header out and says on the path that it did. -/
def guarded : Bridge echoSig :=
  { bridge with
    prepare := fun r =>
      if r.headers.any (·.1 == "x-secret") then
        { r with headers := r.headers.filter (·.1 != "x-secret"), path := ["bad"] }
      else r }

def prepareTest : Async (List (String × Bool)) := do
  let dir := (← IO.getEnv "TMPDIR").getD "/tmp"
  let journal : System.FilePath := s!"{dir}/lanes-web-prepare-{← IO.monoNanosNow}.journal"
  let server ← serve (Server.system echo) guarded { port := 0, journal := some journal }
  let some port := server.port | return [("web: the server reports its port", false)]
  let secret ← fetch port "/" (headers := "X-Secret: hunter2hunter2\r\n")
  let plain ← fetch port "/"
  server.stop
  let bytes := (← IO.FS.readBinFile journal).data.toList
  let holds (text : String) := (List.range bytes.length).any fun k =>
    text.toUTF8.data.toList.isPrefixOf (bytes.drop k)
  for file in [journal, journal.addExtension "lock"] do
    if ← file.pathExists then IO.FS.removeFile file
  return [
    ("web: the system sees a request as the bridge prepared it",
      secret.startsWith "HTTP/1.1 400" && plain.startsWith "HTTP/1.1 200"),
    ("web: and the journal holds the prepared request, not what was sent",
      !holds "hunter2hunter2" && !holds "x-secret" && holds "bad") ]

/-- The journal stops taking writes while the server runs. A request in flight is answered, the
server shuts down, and `wait` fails, so that the process ends and can be started again. -/
def journalFailTest : Async (List (String × Bool)) := do
  let calls ← IO.mkRef 0
  let log : Journal.Log (served (Server.system echo) bridge {}) := {
    past := []
    append := fun _ => do
      if (← calls.modifyGet fun n => (n, n + 1)) ≥ 2 then
        throw (IO.userError "no room on the device")
    note := fun _ => pure ()
    close := pure () }
  let server ← serveWith (Server.system echo) bridge { port := 0 } {} (some log)
  let some port := server.port | return [("web: the server reports its port", false)]
  let within := fun (action : Async String) =>
    Async.race (some <$> action) (do Async.sleep 3000; return none)
  let mut answers := #[]
  for _ in [0:4] do
    answers := answers.push (← within (try fetch port "/" catch _ => pure "refused"))
  let waited ← Async.race (try server.wait; pure (some false) catch _ => pure (some true))
    (do Async.sleep 3000; return none)
  return [
    ("web: when the journal cannot be written, no request is left without an answer",
      answers.all (·.isSome)),
    ("web: requests before the failure are answered and later ones are refused",
      (answers[0]!.getD "").startsWith "HTTP/1.1 200"
        && answers.any fun a => !(a.getD "").startsWith "HTTP/1.1 200"),
    ("web: and the server ends with the error", waited == some true) ]

def tests : IO (List (String × Bool)) := do
  return (← serveTest.block) ++ (← linkTest.block) ++ (← deadlineTest.block)
    ++ (← durableTest.block) ++ (← oldJournalTest.block) ++ (← prepareTest.block)
    ++ (← journalFailTest.block)

end Tests.Web
