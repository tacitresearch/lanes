/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Tests.Web
import Tests.Fronted

/-!
Metrics, health and the access log. The rendering against text checked by hand; who may read the
metrics page; then a server with all of it on: readiness before the shard has recovered, after,
and while draining; a scrape of the metrics page, with its path written as itself and
percent-encoded, and the page hidden from a peer elsewhere; request ids; access-log lines read
back as JSON; a connection refused at the bound, counted; and the same journal with all of it on
as with all of it off. Last, a process stopped by SIGTERM with a request in flight
(`Server.stopOnSignal`).
-/

namespace Tests.Ops

open Lanes Lanes.Http Lanes.Metrics Std Std.Async

def sample : List Family :=
  [ { name := "http_requests_total", help := "Requests.\nWith a \\ backslash."
      series := .counter [([("method", "GET"), ("path", "/a\"b\nc\\d")], 3), ([], 0)] },
    { name := "temperature", help := "Degrees", scale := 1
      series := .gauge [([], -15), ([("room", "x")], 200)] },
    { name := "latency_seconds", help := "Latency.", scale := 3
      series := .histogram [5, 250, 1000]
        [([("route", "home")], Histogram.observeAll [5, 250, 1000] [1, 5, 6, 300, 2000])] },
    { name := "9 bad-name", help := "", series := .counter [([("bad label", "v")], 1)] } ]

def sampleText : String :=
  "# HELP http_requests_total Requests.\\nWith a \\\\ backslash.\n" ++
  "# TYPE http_requests_total counter\n" ++
  "http_requests_total{method=\"GET\",path=\"/a\\\"b\\nc\\\\d\"} 3\n" ++
  "http_requests_total 0\n" ++
  "# HELP temperature Degrees\n" ++
  "# TYPE temperature gauge\n" ++
  "temperature -1.5\n" ++
  "temperature{room=\"x\"} 20\n" ++
  "# HELP latency_seconds Latency.\n" ++
  "# TYPE latency_seconds histogram\n" ++
  "latency_seconds_bucket{route=\"home\",le=\"0.005\"} 2\n" ++
  "latency_seconds_bucket{route=\"home\",le=\"0.25\"} 3\n" ++
  "latency_seconds_bucket{route=\"home\",le=\"1\"} 4\n" ++
  "latency_seconds_bucket{route=\"home\",le=\"+Inf\"} 5\n" ++
  "latency_seconds_sum{route=\"home\"} 2.312\n" ++
  "latency_seconds_count{route=\"home\"} 5\n" ++
  "# HELP _9_bad_name \n" ++
  "# TYPE _9_bad_name counter\n" ++
  "_9_bad_name{bad_label=\"v\"} 1\n"

def access : Ops.Access :=
  { time_ms := 1700000000123, method := .get, path := ["videos", "42"], status := 200
    duration_us := 1500, bytes := 12, requestId := "abc" }

def awkward : Ops.Access :=
  { access with path := ["a\nb", "q\"x"], method := .post, status := 503, duration_us := 7 }

def field (line key : String) : Option Json :=
  (Json.parse line).toOption.bind fun j => (j.getObjVal? key).toOption

def loopback : Option Ip.Addr := Ip.parse "127.0.0.1"

def elsewhere : Option Ip.Addr := Ip.parse "10.0.3.7"

def isLoopback (text : String) : Option Bool :=
  (Ip.parse text).map (·.isLoopback)

def bearer (token : String) : String × String :=
  ("authorization", "Bearer " ++ token)

def metricsFrom (access : OpsConfig) (peer : Option Ip.Addr)
    (headers : List (String × String) := []) : Option Ops.Endpoint :=
  Ops.route? { access with metricsPath := some "/metrics" } peer
    { method := .get, path := ["metrics"], headers }

def health : OpsConfig :=
  { metricsPath := some "/metrics", livenessPath := some "/healthz", readinessPath := some "/readyz" }

def stats : Ops.Stats [1000] :=
  (({} : Ops.Stats [1000]).answered .get 200 500 |>.answered .get 204 2000
    |>.answered .post 503 10 |>.refuse |>.appended 3 |>.saved)

def tests : List (String × Bool) :=
  let page := Metrics.render (Ops.families stats
    { connections := 2, inflight := 1, inbox := 0, ready := true })
  [ ("metrics: a page is rendered in the text format, escaped, as checked by hand",
      Metrics.render sample == sampleText),
    ("metrics: a valid name is left as it is and an invalid one made valid",
      sanitize "lanes_http_requests_total" == "lanes_http_requests_total"
        && sanitize "" == "_" && sanitize "a.b" == "a_b"),
    ("metrics: the server's counts render with their labels and gauges",
      page.contains "lanes_http_requests_total{method=\"GET\",status_class=\"2xx\"} 2\n"
        && page.contains "lanes_http_requests_total{method=\"POST\",status_class=\"5xx\"} 1\n"
        && page.contains "lanes_http_request_duration_seconds_bucket{le=\"0.001\"} 2\n"
        && page.contains "lanes_http_request_duration_seconds_count 3\n"
        && page.contains "lanes_http_request_duration_seconds_sum 0.00251\n"
        && page.contains "lanes_http_connections_refused_total 1\n"
        && page.contains "lanes_journal_entries_total 3\n"
        && page.contains "lanes_journal_saves_total 1\n"
        && page.contains "lanes_http_connections 2\n" && page.contains "lanes_ready 1\n"),
    ("ops: an access line is the record's fields, in order",
      access.line == "{\"time\":\"2023-11-14T22:13:20.123Z\",\"method\":\"GET\","
        ++ "\"path\":\"/videos/42\",\"status\":200,\"duration_ms\":1.5,\"bytes\":12,"
        ++ "\"request_id\":\"abc\"}"),
    ("ops: an awkward path stays on its line and reads back",
      !awkward.line.contains '\n'
        && field awkward.line "path" == some (.str "/a%0Ab/q%22x")
        && field awkward.line "duration_ms" == some (.num (JsonNumber.ofDecimal 7 3))
        && field awkward.line "method" == some (.str "POST")),
    ("ops: a client's request id is taken only when well formed and bounded",
      Ops.RequestId.accept? 64 "trace-42.a_b" == some "trace-42.a_b"
        && Ops.RequestId.accept? 64 "" == none && Ops.RequestId.accept? 64 "has space" == none
        && Ops.RequestId.accept? 4 "abcde" == none && Ops.RequestId.accept? 64 "é" == none
        && Ops.RequestId.accept? 64 "a\nb" == none),
    ("ops: an id made from bytes is hexadecimal",
      Ops.RequestId.ofBytes [0, 15, 171, 255] == "000FABFF"),
    ("ops: a response carries exactly one request id",
      (Ops.RequestId.tag "x" { headers := [("x-request-id", "app"), ("a", "b")] }).headers
        == [("a", "b"), ("x-request-id", "x")]),
    ("ops: with nothing configured no request is the operators'",
      Ops.route? {} loopback { method := .get, path := ["metrics"] } == none
        && !({} : OpsConfig).active && !({} : OpsConfig).counting),
    ("ops: counts are kept only for a metrics page, and a log alone is active",
      ({ metricsPath := some "/m" } : OpsConfig).counting
        && !({ accessLog := .stderr } : OpsConfig).counting
        && ({ accessLog := .stderr } : OpsConfig).active),
    ("ops: a GET at a configured path is, and nothing else",
      Ops.route? { metricsPath := some "/metrics" } loopback { method := .get, path := ["metrics"] }
          == some .metrics
        && Ops.route? { metricsPath := some "/metrics" } loopback
          { method := .post, path := ["metrics"] } == none
        && Ops.route? { readinessPath := some "/readyz" } loopback { method := .get, path := [] }
          == none),
    ("ops: loopback addresses are 127.0.0.0/8, ::1 and 127.0.0.0/8 mapped into IPv6",
      ["127.0.0.1", "127.255.3.4", "::1", "::ffff:127.0.0.1"].all (isLoopback · == some true)
        && ["126.255.255.255", "128.0.0.1", "10.0.0.1", "0.0.0.0", "::", "::2", "::ffff:10.0.0.1",
          "fe80::1", "::127.0.0.1"].all (isLoopback · == some false)),
    ("ops: by default the metrics page is answered to a loopback peer only, and hidden from others",
      metricsFrom {} loopback == some .metrics && metricsFrom {} (Ip.parse "::1") == some .metrics
        && metricsFrom {} elsewhere == some .hidden && metricsFrom {} none == some .hidden
        && (Ops.answer .hidden { recovered := true, stopping := false } "").status == 404),
    ("ops: with a token, a peer elsewhere reads the page only with it",
      metricsFrom { metricsAccess := .token "s3cret" } elsewhere [bearer "s3cret"] == some .metrics
        && metricsFrom { metricsAccess := .token "s3cret" } elsewhere
          [("authorization", "bearer s3cret")] == some .metrics
        && metricsFrom { metricsAccess := .token "s3cret" } loopback == some .metrics
        && [[], [bearer "s3cre"], [bearer "s3cret!"], [bearer ""], [("authorization", "s3cret")],
            [("authorization", "Basic s3cret")], [("authorization", "Bearer s3cret x")]].all
          (metricsFrom { metricsAccess := .token "s3cret" } elsewhere · == some .hidden)),
    ("ops: with anyone, every peer reads the page",
      metricsFrom { metricsAccess := .anyone } elsewhere == some .metrics),
    ("ops: liveness and readiness answer every peer",
      [loopback, elsewhere, none].all fun peer =>
        Ops.route? health peer { method := .get, path := ["healthz"] } == some .live
          && Ops.route? health peer { method := .get, path := ["readyz"] } == some .ready) ]

/-! A server with all of it on. -/

def opsConfig (lines : IO.Ref (Array String)) : OpsConfig :=
  { metricsPath := some "/metrics", livenessPath := some "/healthz"
    readinessPath := some "/readyz", accessLog := .call fun l => lines.modify (·.push l)
    requestIds := true }

/-- The value of the sample that starts with `name`, followed by a space. -/
def valueOf (page name : String) : Option Nat :=
  (page.splitOn "\n").findSome? fun line =>
    if line.startsWith (name ++ " ") then (line.drop (name.length + 1)).toString.toNat? else none

def status (response : String) : String :=
  ((response.drop 9).take 3).toString

/-- A journal held in memory, which records what is appended to it. -/
def memory {σ : Signature} (sys : System σ) (past : List (Journal.Entry σ)) :
    IO (Journal.Log sys × IO.Ref (Array (Journal.Entry σ))) := do
  let written ← IO.mkRef #[]
  return ({ past, append := fun es => written.modify (· ++ es.toArray), note := fun _ => pure ()
            close := pure () }, written)

/-- The desk starts on a journal that owes a memo, and the handler holds the memo, so the shard
has not recovered until it is let go. -/
def readyTest : Async (List (String × Bool)) := do
  let lines ← IO.mkRef #[]
  let release : IO.Promise Unit ← IO.Promise.new
  let (log, _) ← memory (admittedFronted (Server.system Tests.Fronted.desk) Tests.Fronted.bridge) [.advance 0, .input (.inr (.note 7)), .batch 64]
  let server ← serveFronted (Server.system Tests.Fronted.desk) Tests.Fronted.bridge
    { port := 0, ops := opsConfig lines } {}
    (fun _ out => match out with | .memo _ => discard <| await release.result? | .reply _ => pure ())
    (log := some log)
  let some port := server.port | return [("ops: the server reports its port", false)]
  let early ← Tests.Web.fetch port "/readyz"
  let alive ← Tests.Web.fetch port "/healthz"
  release.resolve ()
  let mut polls := 0
  let mut ready := ""
  for _ in [0:200] do
    polls := polls + 1
    ready ← Tests.Web.fetch port "/readyz"
    if status ready == "200" then break
    Async.sleep 10
  for _ in [0:3] do discard <| Tests.Web.fetch port "/"
  let page ← Tests.Web.fetch port "/metrics"
  let encoded ← Tests.Web.fetch port "/%6Detrics"
  server.drain
  let draining ← Tests.Web.fetch port "/readyz"
  let stillAlive ← Tests.Web.fetch port "/healthz"
  let served ← Tests.Web.fetch port "/"
  server.stop
  let logged ← lines.get
  return [
    ("ops: not ready before the shard has recovered, and alive",
      status early == "503" && status alive == "200"),
    ("ops: ready once it has", status ready == "200"),
    ("ops: the metrics page is served in the text format, to a peer on the loopback address",
      status page == "200" && page.contains ("content-type: " ++ Metrics.contentType)),
    ("ops: its path is matched once decoded",
      status encoded == "200" && encoded.contains "lanes_ready 1"),
    ("ops: it counts what was answered, by method and status class",
      valueOf page "lanes_http_requests_total{method=\"GET\",status_class=\"2xx\"}" == some 5
        && valueOf page "lanes_http_requests_total{method=\"GET\",status_class=\"5xx\"}"
          == some polls
        && valueOf page "lanes_http_request_duration_seconds_count" == some (polls + 5)
        && valueOf page "lanes_ready" == some 1 && valueOf page "lanes_http_connections" == some 1
        && (valueOf page "lanes_journal_appends_total").any (· > 0)),
    ("ops: draining is not ready, still alive, and still serves",
      status draining == "503" && status stillAlive == "200" && status served == "200"),
    ("ops: every answer has its line in the access log, and each line is JSON",
      logged.size == polls + 10 && logged.all fun l => (Json.parse l).toOption.isSome) ]

/-- `Ops.front` for a connection from elsewhere: the metrics page, however its path was written,
is answered `404` and never handed on; liveness is answered. -/
def hiddenTest : Async (List (String × Bool)) := do
  let lines ← IO.mkRef #[]
  let ops ← Ops.new (opsConfig lines)
  let handed ← IO.mkRef 0
  let submit : Request → (Response → BaseIO Unit) → BaseIO Unit := fun _ answer => do
    handed.modify (· + 1)
    answer (.text "app\n")
  let probe : BaseIO Ops.Probe :=
    return { recovered := true, stopping := false, connections := 1, inflight := 0, inbox := 0 }
  let ask (peer : Option Ip.Addr) (target : String) : BaseIO Response := do
    let .ok (path, _) := Request.target? target.toList | return .text "unparsed" 400
    let request : Request := { method := .get, path }
    let answered ← IO.Promise.new
    ops.front probe peer submit request answered.resolve
    return answered.result?.get.getD (.text "unanswered" 500)
  let plain ← ask elsewhere "/metrics"
  let encoded ← ask elsewhere "/%6Detrics"
  let alive ← ask elsewhere "/healthz"
  let here ← ask loopback "/%6D%65trics"
  return [
    ("ops: from elsewhere, the metrics page is not found, written plainly or percent-encoded",
      plain.status == 404 && encoded.status == 404 && (← handed.get) == 0
        && !(String.fromUTF8! plain.body).contains "lanes_"),
    ("ops: from elsewhere, liveness answers; from the loopback address, the page does",
      alive.status == 200 && here.status == 200
        && (String.fromUTF8! here.body).contains "lanes_ready 1") ]

/-- Request ids, and what the log leaves out. -/
def logTest : Async (List (String × Bool)) := do
  let lines ← IO.mkRef #[]
  let server ← serve (Server.system Tests.Gate.echo) Tests.Gate.bridge
    { port := 0, ops := opsConfig lines }
  let some port := server.port | return [("ops: the server reports its port", false)]
  let given ← Tests.Web.fetch port "/videos/42?secret=s3"
    (headers := "X-Request-Id: trace-42\r\nAuthorization: Bearer hunter2\r\nCookie: sid=c00k\r\n")
  let bad ← Tests.Web.fetch port "/" (headers := "X-Request-Id: not a good id\r\n")
  let missing ← Tests.Web.fetch port "/"
  server.stop
  let logged ← lines.get
  let first := logged[0]?.getD ""
  let idOf := fun (response : String) =>
    ((response.splitOn "x-request-id: ")[1]?.getD "").takeWhile (· != '\r') |>.toString
  return [
    ("ops: a well-formed request id is echoed and logged",
      idOf given == "trace-42" && field first "request_id" == some (.str "trace-42")),
    ("ops: a malformed or missing one is replaced by a new one, echoed and logged",
      (idOf bad).length == 16 && (idOf missing).length == 16 && idOf bad != idOf missing
        && field (logged[1]?.getD "") "request_id" == some (.str (idOf bad))),
    ("ops: the log has the path without its query, the status and the size of the body",
      field first "path" == some (.str "/videos/42") && field first "status" == some (.num 200)
        && field first "bytes" == some (.num 2) && field first "method" == some (.str "GET")),
    ("ops: and never the query, a credential or a cookie",
      logged.all fun l => !l.contains "s3" && !l.contains "hunter2" && !l.contains "c00k"
        && !l.contains "secret") ]

/-- One connection beyond the bound is closed and counted. -/
def refusedTest : Async (List (String × Bool)) := do
  let lines ← IO.mkRef #[]
  let server ← serve (Server.system Tests.Gate.echo) Tests.Gate.bridge
    { port := 0, connections_max := 1, ops := opsConfig lines }
  let some port := server.port | return [("ops: the server reports its port", false)]
  let held ← TCP.Socket.Client.mk
  held.connect (.v4 ⟨.ofParts 127 0 0 1, port⟩)
  Async.sleep 200
  let refused ← try Tests.Web.fetch port "/metrics" catch _ => pure ""
  held.close
  let mut page := ""
  let mut more := 0
  for _ in [0:200] do
    page ← try Tests.Web.fetch port "/metrics" catch _ => pure ""
    if status page == "200" then break
    more := more + 1
    Async.sleep 10
  server.stop
  return [
    ("ops: a connection beyond the bound is closed and counted",
      refused.isEmpty && valueOf page "lanes_http_connections_refused_total" == some (1 + more)) ]

/-- The same requests, with all of it off and with all of it on and probed between them: the
journals hold the same inputs, the four the gate admits (`/bad` it refuses before the shard). -/
def journalTest : Async (List (String × Bool)) := do
  let run := fun (ops : OpsConfig) (probe : Bool) => do
    let (log, written) ← memory (admitted (Server.system Tests.Gate.echo) Tests.Gate.bridge) []
    let server ← serveWith (Server.system Tests.Gate.echo) Tests.Gate.bridge
      { port := 0, ops } {} (some log)
    let port := server.port.getD 0
    let mut page := ""
    for path in ["/a", "/b?q=1", "/bad", "/c", "/"] do
      discard <| Tests.Web.fetch port path (headers := "X-Request-Id: fixed\r\n")
      if probe then
        discard <| Tests.Web.fetch port "/healthz"
        discard <| Tests.Web.fetch port "/readyz"
        page ← Tests.Web.fetch port "/metrics"
    server.stop
    let inputs := (← written.get).toList.filterMap fun
      | .input x => some x
      | _ => none
    return (inputs, page)
  let lines ← IO.mkRef #[]
  let (off, _) ← run {} false
  let (on, page) ← run (opsConfig lines) true
  return [
    ("ops: with metrics, health and logs on, the journal holds the same inputs as with them off",
      off.length == 4 && off == on),
    ("ops: and the journal's appends were counted",
      (valueOf page "lanes_journal_entries_total").any (· > 0)) ]

/-! ## A stop -/

/-- Wait for a child's exit, for at most `ms`; kill it if it has not. -/
def exitWithin {cfg : IO.Process.StdioConfig} (child : IO.Process.Child cfg) (ms : Nat) :
    Async (Option UInt32) := do
  let waited ← IO.asTask (prio := .dedicated) child.wait
  let code ← Tests.Durable.within ms (await waited)
  if code.isNone then child.kill
  return code.bind (·.toOption)

/-- The next line of `out`, waited for at most `ms`. -/
def lineWithin (out : IO.FS.Handle) (ms : Nat) : Async String := do
  let line ← IO.asTask (prio := .dedicated) out.getLine
  return (((← Tests.Durable.within ms (await line)).bind (·.toOption)).getD "").trimAscii.toString

/-- Poll readiness until it answers `want`, at most 500 times. -/
def readiness (port : UInt16) (want : String) : Async Bool := do
  for _ in [0:500] do
    if status (← Tests.Web.fetch port "/readyz") == want then return true
    Async.sleep 10
  return false

/-- A child serves, a request starts work, and the child is sent SIGTERM; the work is done during
the drain if `finish`. What the request was answered, whether each step was seen, and the exit
status. -/
def stopRun (drain_ms : Nat) (finish : Bool) : Async (Option (String × Bool × Option UInt32)) := do
  let child ← IO.Process.spawn {
    cmd := ((← IO.appPath).parent.getD "." / "lanesStopChild").toString
    args := #[toString drain_ms]
    stdin := .piped, stdout := .piped }
  let some port := ((← lineWithin child.stdout 60000).dropPrefix? "listening ").bind
      (·.toString.toNat?) |
    child.kill
    return none
  let port := port.toUInt16
  let ready ← readiness port "200"
  let request ← async (Tests.Web.fetch port "/work")
  let started := (← lineWithin child.stdout 10000) == "working"
  discard <| IO.Process.output { cmd := "kill", args := #["-TERM", toString child.pid] }
  let draining ← if finish then readiness port "503" else pure true
  let (stdin, child) ← child.takeStdin
  if finish then
    stdin.putStrLn "done"
    stdin.flush
  let response ← Tests.Durable.within 10000 (await request)
  let code ← exitWithin child 10000
  return some ((response.getD "").take 12 |>.toString, ready && started && draining, code)

def stopTest : Async (List (String × Bool)) := do
  let finished ← stopRun 30000 true
  let cut ← stopRun 300 false
  return [
    ("stop: on SIGTERM, readiness answers 503 while a request in flight is answered, and the "
      ++ "process exits 0",
      finished == some ("HTTP/1.1 200", true, some 0)),
    ("stop: a request still in flight at the drain's deadline is answered 503, and the process "
      ++ "exits 0",
      cut == some ("HTTP/1.1 503", true, some 0)) ]

def live : Async (List (String × Bool)) := do
  return (← readyTest) ++ (← hiddenTest) ++ (← logTest) ++ (← refusedTest) ++ (← journalTest)
    ++ (← stopTest)

end Tests.Ops
