/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Tests.Web
import Tests.Fronted

/-!
Metrics, health and the access log. The rendering against text checked by hand; then a server
with all of it on: readiness before the shard has recovered, after, and while draining; a scrape
of the metrics page; request ids; access-log lines read back as JSON; a connection refused at the
bound, counted; and the same journal with all of it on as with all of it off.
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
      Ops.route? {} { method := .get, path := ["metrics"] } == none
        && !({} : OpsConfig).active && !({} : OpsConfig).counting),
    ("ops: counts are kept only for a metrics page, and a log alone is active",
      ({ metricsPath := some "/m" } : OpsConfig).counting
        && !({ accessLog := .stderr } : OpsConfig).counting
        && ({ accessLog := .stderr } : OpsConfig).active),
    ("ops: a GET at a configured path is, and nothing else",
      Ops.route? { metricsPath := some "/metrics" } { method := .get, path := ["metrics"] }
          == some .metrics
        && Ops.route? { metricsPath := some "/metrics" } { method := .post, path := ["metrics"] }
          == none
        && Ops.route? { readinessPath := some "/readyz" } { method := .get, path := [] } == none) ]

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
  let (log, _) ← memory (Tests.Fronted.Fronted {}) [.advance 0, .input (.inr (.note 7)), .batch 64]
  let server ← serveFronted (Server.system Tests.Fronted.desk) Tests.Fronted.bridge
    { port := 0, ops := opsConfig lines } {}
    (fun | .memo _ => discard <| await release.result? | .reply _ => pure ()) (log := some log)
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
    ("ops: the metrics page is served in the text format",
      status page == "200" && page.contains "content-type: text/plain; version=0.0.4"),
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
      logged.size == polls + 9 && logged.all fun l => (Json.parse l).toOption.isSome) ]

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
journals hold the same inputs. -/
def journalTest : Async (List (String × Bool)) := do
  let run := fun (ops : OpsConfig) (probe : Bool) => do
    let (log, written) ← memory (served (Server.system Tests.Gate.echo) Tests.Gate.bridge {}) []
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
      off.length == 5 && off == on),
    ("ops: and the journal's appends were counted",
      (valueOf page "lanes_journal_entries_total").any (· > 0)) ]

def live : Async (List (String × Bool)) := do
  return (← readyTest) ++ (← logTest) ++ (← refusedTest) ++ (← journalTest)

end Tests.Ops
