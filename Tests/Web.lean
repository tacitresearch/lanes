/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Tests.Gate
import Tests.Fixtures.BankWeb

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

def serveTest (ioThreads : Nat := 0) : Async (List (String × Bool)) := do
  let server ← serve (Server.system echo) bridge { port := 0, ioThreads } { record := true }
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
    ("web: a method no application handles is refused", options.startsWith "HTTP/1.1 501") ]

/-! Links through a real server: what `Route.link` prints, sent over a socket and decoded by
the server's reader, must match the route it came from with the value it was printed from. -/

def echoSlug : Route Slug := .get ("echo" /> .slug)

def mute : Service ReqId ReqId Unit where
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
  let start := serve (Tests.Fixtures.Bank.bank Tests.Fixtures.BankWeb.Acct 100) Tests.Fixtures.BankWeb.bridge
    { port := 0, journal := some journal } { record := true, snapshotEvery := 4 }
    (some { actors := Tests.Fixtures.Bank.actors Codec.fin 100, out := Tests.Fixtures.Bank.Response.codec })
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
      discard <| serve (Tests.Fixtures.Bank.bank Tests.Fixtures.BankWeb.Acct 100) Tests.Fixtures.BankWeb.bridge
        { port, journal := some (journal.addExtension "other") }
      pure false
    catch _ => pure true
  let free ← (Journal.Store.open
    (sys := served (Tests.Fixtures.Bank.bank Tests.Fixtures.BankWeb.Acct 100) Tests.Fixtures.BankWeb.bridge {})
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

/-- A journal written by `serve` when the gate was an actor of the system behind it and the
journal was named by the application alone, is refused and left as it was: replayed
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

/-- `arrive` runs for at most `arriving_max` requests at once, each on a thread of its own: one
more is answered `503` before its work begins, and once one is done the next is taken. -/
def arriveTest : Async (List (String × Bool)) := do
  let release ← IO.Promise.new
  let work (_ : Request) : IO (Except Response Request) := do
    let _ ← IO.wait release.result?
    return .error (.text "worked")
  let server ← serve (Server.system mute) slugBridge { port := 0, arriving_max := 1 }
    (arrive := some work)
  let some port := server.port | return [("web: the server reports its port", false)]
  let first ← IO.Promise.new
  background do first.resolve (← fetch port "/a")
  Async.sleep 200
  let second ← fetch port "/b"
  release.resolve ()
  let first ← await first
  let third ← fetch port "/c"
  server.stop
  return [
    ("web: beyond arriving_max, a request whose work is in IO is answered 503 at once",
      second.startsWith "HTTP/1.1 503" && first.endsWith "worked" && third.endsWith "worked") ]

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

/-! The connection loop over a real socket: the bytes as a client sends them, in pieces, pipelined,
slowly or too many, and connections kept, left idle, beyond the bound and open at `stop`. -/

/-- Write `pieces` with `gap_ms` between them, wait `wait_ms`, then read until the server closes
or three seconds pass; `none` if the connection was reset. -/
def exchange (port : UInt16) (pieces : List String) (gap_ms : Nat := 0) (wait_ms : Nat := 0) :
    Async (Option String) := do
  let socket ← TCP.Socket.Client.mk
  socket.connect (.v4 ⟨.ofParts 127 0 0 1, port⟩)
  for piece in pieces do
    socket.send piece.toUTF8
    if gap_ms > 0 then Async.sleep (.ofNat gap_ms)
  if wait_ms > 0 then Async.sleep (.ofNat wait_ms)
  let reading : Async (Option ByteArray) := do
    let mut received := ByteArray.empty
    repeat
      match ← socket.recv? 65536 with
      | some bytes => received := received ++ bytes
      | none => break
    return some received
  let got ← try Async.race reading (do Async.sleep 3000; return none) catch _ => pure none
  socket.close
  return got.map fun bytes => (String.fromUTF8? bytes).getD ""

def get (path : String) (close : Bool := false) : String :=
  s!"GET {path} HTTP/1.1\r\nHost: h\r\n" ++ (if close then "Connection: close\r\n" else "") ++ "\r\n"

def statuses (text : String) : List String :=
  (text.splitOn "HTTP/1.1 ").drop 1 |>.map (·.take 3 |>.toString)

def wireTest (ioThreads : Nat := 0) : Async (List (String × Bool)) := do
  let server ← serve (Server.system mute) slugBridge
    { port := 0, head_ms := 300, idle_ms := 300, connections_max := 3, ioThreads }
  let some port := server.port | return [("web: the server reports its port", false)]
  let pipelined ← exchange port [get "/echo/a" ++ get "/echo/b" ++ get "/echo/c" true]
  let pieces ← exchange port ["GE", "T /echo/s HTTP/1.1\r\nHo", "st: h\r\nConnection: close\r\n", "\r\n"]
    (gap_ms := 30)
  let many ← exchange port ((List.range 100).map (fun _ => get "/echo/k") ++ [get "/echo/end" true])
  let refused ← exchange port
    ["GET /echo/x HTTP/1.1\r\nHost: h\r\nContent-Length: 1\r\nContent-Length: 1\r\n\r\nx"
      ++ String.ofList (List.replicate 200000 'z')] (wait_ms := 300)
  let slow ← exchange port ["GET /echo/x HTTP/1.1\r\nHost: h\r\n"]
  let started ← IO.monoMsNow
  let idle ← exchange port []
  let idled := (← IO.monoMsNow) - started
  let ended ← Async.race (do server.stop; return true) (do Async.sleep 3000; return false)
  -- The bound, on a server whose deadlines are long: a held connection the server closed at its
  -- deadline would free a place for the one beyond it. Each held connection is answered once
  -- before the next, so all three are counted when the fourth arrives.
  let bound ← serve (Server.system mute) slugBridge
    { port := 0, head_ms := 10000, idle_ms := 10000, connections_max := 3, ioThreads }
  let some boundPort := bound.port | return [("web: the server reports its port", false)]
  let held ← (List.range 3).mapM fun _ => do
    let socket ← TCP.Socket.Client.mk
    socket.connect (.v4 ⟨.ofParts 127 0 0 1, boundPort⟩)
    socket.send (get "/echo/held").toUTF8
    let answer ← try Async.race (socket.recv? 65536) (do Async.sleep 3000; return none)
      catch _ => pure none
    return (socket, answer.isSome)
  let beyond ← exchange boundPort [get "/echo/n" true]
  for (socket, _) in held do socket.close
  discard <| Async.race (do bound.stop; return true) (do Async.sleep 3000; return false)
  let server ← serve (Server.system mute) slugBridge { port := 0, ioThreads }
  let some port := server.port | return [("web: the server reports its port", false)]
  let socket ← TCP.Socket.Client.mk
  socket.connect (.v4 ⟨.ofParts 127 0 0 1, port⟩)
  socket.send (get "/echo/kept").toUTF8
  let first ← socket.recv? 65536
  let stopped ← Async.race (do server.stop; return true) (do Async.sleep 3000; return false)
  let after ← try Async.race (socket.recv? 65536) (do Async.sleep 3000; return some ByteArray.empty)
    catch _ => pure none
  socket.close
  return [
    ("web: pipelined requests in one write are answered in order, and the connection closes "
      ++ "after the one that asks", pipelined.any fun text =>
        statuses text == ["200", "200", "200"]
          && ((text.splitOn "\r\n\r\n").drop 1).map (·.takeWhile (· != 'H') |>.toString)
            == ["a", "b", "c"]),
    ("web: a request sent in pieces is read", pieces.any (·.endsWith "s")),
    ("web: a hundred and one requests on one connection are each answered",
      many.any fun text => (statuses text).length == 101 && text.endsWith "end"),
    ("web: a request refused with more bytes behind it is answered 400, not reset",
      refused.any (statuses · == ["400"])),
    ("web: a head that does not arrive in time is answered 408 and the connection closed",
      slow.any (statuses · == ["408"])),
    ("web: an idle connection is closed at its deadline, with nothing written",
      idle == some "" && 250 ≤ idled),
    ("web: a connection beyond the bound is closed without an answer",
      held.all (·.2) && beyond.getD "" == ""),
    ("web: and stop then returns, every connection answered and closed", ended),
    ("web: stop closes a connection kept open, after its response",
      (first.bind String.fromUTF8?).any (·.endsWith "kept") && stopped && after == none) ]

def tests : IO (List (String × Bool)) := do
  let onLanes := fun (results : List (String × Bool)) =>
    results.map fun (name, ok) => (s!"{name} (on 2 IO threads)", ok)
  return (← (serveTest 0).block) ++ (← linkTest.block) ++ (← deadlineTest.block)
    ++ (← durableTest.block) ++ (← oldJournalTest.block) ++ (← prepareTest.block)
    ++ (← journalFailTest.block) ++ (← arriveTest.block) ++ (← (wireTest 0).block)
    ++ onLanes ((← (serveTest 2).block) ++ (← (wireTest 2).block))

end Tests.Web
