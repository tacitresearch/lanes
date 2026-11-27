/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Lib.Metrics
public import Lanes.Lib.Encoding.Json
public import Lanes.Lib.Time.Format
public import Lanes.Web.Http.Basic

/-!
What the HTTP server tells its operators, as pure functions: which requests are theirs (a
metrics page, liveness, readiness), what each answers, the server's counts and how they render
as metrics, a request id taken from the client or made, and a line of the access log.

Nothing here reaches a system: an operator's request is answered by the server
(`docs/decisions/new-observability.md`). With the default configuration no request is the
operators' (`route?_default`), and a request is one only at a path configured for it
(`route?_some`). Readiness answers `200` exactly when the shard has recovered and the server is
not stopping (`answer_ready`). A request id taken from a client is bounded and has only letters,
digits and `-._` (`RequestId.accept?_eq_some`), and so does one made (`RequestId.accept?_ofBytes`);
a response carries exactly one (`header_tag`). A line of the access log is the JSON text of its
record (`Ops.Access.parse_line`, in `Lanes/Web/Http/OpsSound.lean`). It holds the method, the path without its query, the status, the
time taken, the size of the body and the request id; never a header, a query or a body.
-/

@[expose] public section

namespace Lanes.Http

/-- Where the access log goes: nowhere, a line at a time to standard error, or to a function. -/
inductive LogSink where
  | off
  | stderr
  | call (write : String → IO Unit)

def LogSink.isOn : LogSink → Bool
  | .off => false
  | _ => true

/-- Everything is off by default. A path is the request's path as the server reads it, with no
query (`/metrics`). -/
structure OpsConfig where
  /-- The metrics page, in the Prometheus text format. -/
  metricsPath : Option String := none
  /-- `200` while the server answers at all. -/
  livenessPath : Option String := none
  /-- `200` once the shard has recovered its journal, and `503` from `Server.drain` or `stop`. -/
  readinessPath : Option String := none
  accessLog : LogSink := .off
  /-- Answer every request with an `X-Request-Id`: the client's if it is well formed, else a
  new one. The access log carries it either way. -/
  requestIds : Bool := false
  requestIdMax : Nat := 64
  /-- The bounds of the latency histogram. -/
  latencyBounds_us : List Nat :=
    [1000, 2500, 5000, 10000, 25000, 50000, 100000, 250000, 500000, 1000000, 2500000, 5000000,
      10000000]

namespace OpsConfig

/-- Whether the server keeps counts: only for a metrics page. -/
def counting (c : OpsConfig) : Bool :=
  c.metricsPath.isSome

/-- Whether anything is on. When nothing is, the server is as it was without operators. -/
def active (c : OpsConfig) : Bool :=
  c.metricsPath.isSome || c.livenessPath.isSome || c.readinessPath.isSome || c.accessLog.isOn
    || c.requestIds

end OpsConfig

namespace Ops

/-- The path as text, each segment percent-encoded again, with no query. -/
def pathText (path : List String) : String :=
  if path.isEmpty then "/" else String.join (path.map fun s => "/" ++ percentEncode s)

inductive Endpoint where
  | metrics
  | live
  | ready
  deriving DecidableEq, Repr

/-- The operators' endpoint a request asks for, if any: a `GET` at a configured path. -/
def route? (c : OpsConfig) (r : Request) : Option Endpoint :=
  if r.method != .get then none
  else
    let path := some (pathText r.path)
    if c.metricsPath == path then some .metrics
    else if c.livenessPath == path then some .live
    else if c.readinessPath == path then some .ready
    else none

theorem route?_default (r : Request) : route? {} r = none := by
  simp [route?]

/-- Only a `GET` at a path configured for it is the operators'. -/
theorem route?_some {c : OpsConfig} {r : Request} {e : Endpoint} (h : route? c r = some e) :
    r.method = .get ∧ (c.metricsPath = some (pathText r.path) ∨
      c.livenessPath = some (pathText r.path) ∨ c.readinessPath = some (pathText r.path)) := by
  unfold route? at h
  split at h
  · simp at h
  · rename_i hm
    refine ⟨by simpa using hm, ?_⟩
    by_cases h1 : c.metricsPath = some (pathText r.path)
    · exact .inl h1
    by_cases h2 : c.livenessPath = some (pathText r.path)
    · exact .inr (.inl h2)
    by_cases h3 : c.readinessPath = some (pathText r.path)
    · exact .inr (.inr h3)
    simp [h1, h2, h3] at h

structure Health where
  /-- The shard has replayed its journal and handed over what it owed. -/
  recovered : Bool
  /-- The server is draining or stopping. -/
  stopping : Bool

def Health.ready (h : Health) : Bool :=
  h.recovered && !h.stopping

def answer (e : Endpoint) (health : Health) (metrics : String) : Response :=
  match e with
  | .metrics => { headers := [("content-type", Metrics.contentType)], body := metrics.toUTF8 }
  | .live => .text "ok\n"
  | .ready => if health.ready then .text "ready\n" else .text "not ready\n" 503

/-- Readiness answers `200` exactly when the shard has recovered and the server is not stopping;
otherwise `503`. -/
theorem answer_ready (health : Health) (metrics : String) :
    ((answer .ready health metrics).status = 200 ↔
      health.recovered = true ∧ health.stopping = false) ∧
    ((answer .ready health metrics).status = 503 ↔ ¬health.ready = true) := by
  cases hr : health.recovered <;> cases hs : health.stopping <;>
    simp [answer, Health.ready, hr, hs, Response.text, Response.ofText]

/-! ## Counts -/

def methodName : Method → String
  | .get => "GET"
  | .post => "POST"
  | .put => "PUT"
  | .patch => "PATCH"
  | .delete => "DELETE"

def statusClass (status : Nat) : String :=
  toString (status / 100) ++ "xx"

/-- Add one to the count under `k`, or start it at one. -/
def bumpKey {κ : Type} [BEq κ] (k : κ) : List (κ × Nat) → List (κ × Nat)
  | [] => [(k, 1)]
  | (k', n) :: rest => if k' == k then (k', n + 1) :: rest else (k', n) :: bumpKey k rest

theorem lookup_bumpKey {κ : Type} [DecidableEq κ] (k j : κ) : ∀ l : List (κ × Nat),
    (bumpKey k l).lookup j = if j = k then some ((l.lookup j).getD 0 + 1) else l.lookup j
  | [] => by
    by_cases h : j = k
    · simp [bumpKey, List.lookup, h]
    · simp [bumpKey, List.lookup, h, beq_eq_false_iff_ne.mpr h]
  | (k', n) :: rest => by
    have ih := lookup_bumpKey k j rest
    by_cases hk : k' = k
    · subst hk
      by_cases h : j = k'
      · simp [bumpKey, List.lookup, h]
      · simp [bumpKey, List.lookup, h, beq_eq_false_iff_ne.mpr h]
    · by_cases h : j = k'
      · subst h; simp [bumpKey, List.lookup, hk]
      · simp [bumpKey, List.lookup, hk, ih, beq_eq_false_iff_ne.mpr h]

/-- What the server counts. -/
structure Stats (bounds : List Nat) where
  /-- Answers, by method and status class. -/
  requests : List ((String × String) × Nat) := []
  latency : Metrics.Histogram bounds := {}
  /-- Connections closed on accepting them, at `connections_max`. -/
  refused : Nat := 0
  appends : Nat := 0
  entries : Nat := 0
  saves : Nat := 0

namespace Stats

variable {bounds : List Nat}

def answered (method : Method) (status duration_us : Nat) (s : Stats bounds) : Stats bounds :=
  { s with requests := bumpKey (methodName method, statusClass status) s.requests
           latency := s.latency.observe duration_us }

def refuse (s : Stats bounds) : Stats bounds :=
  { s with refused := s.refused + 1 }

def appended (entries : Nat) (s : Stats bounds) : Stats bounds :=
  { s with appends := s.appends + 1, entries := s.entries + entries }

def saved (s : Stats bounds) : Stats bounds :=
  { s with saves := s.saves + 1 }

end Stats

/-- What is read when the page is asked for rather than counted. -/
structure Gauges where
  connections : Nat
  inflight : Nat
  inbox : Nat
  ready : Bool

def families {bounds : List Nat} (s : Stats bounds) (g : Gauges) : List Metrics.Family :=
  [ { name := "lanes_http_requests_total", help := "Requests answered, by method and status class."
      series := .counter (s.requests.map fun ((m, c), n) => ([("method", m), ("status_class", c)], n)) },
    { name := "lanes_http_request_duration_seconds"
      help := "From a request read to its answer handed to its connection.", scale := 6
      series := .histogram bounds [([], s.latency)] },
    { name := "lanes_http_requests_in_flight", help := "Requests the shard has taken and not answered."
      series := .gauge [([], g.inflight)] },
    { name := "lanes_http_connections", help := "Connections open."
      series := .gauge [([], g.connections)] },
    { name := "lanes_http_connections_refused_total", help := "Connections closed at connections_max."
      series := .counter [([], s.refused)] },
    { name := "lanes_runtime_inbox_depth", help := "Commands waiting in the shard's inbox."
      series := .gauge [([], g.inbox)] },
    { name := "lanes_journal_appends_total", help := "Synced appends to the journal."
      series := .counter [([], s.appends)] },
    { name := "lanes_journal_entries_total", help := "Entries appended to the journal."
      series := .counter [([], s.entries)] },
    { name := "lanes_journal_saves_total", help := "Snapshots saved."
      series := .counter [([], s.saves)] },
    { name := "lanes_ready", help := "1 when readiness answers 200."
      series := .gauge [([], if g.ready then 1 else 0)] } ]

/-! ## Request ids -/

namespace RequestId

def allowed (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || ('0' ≤ c && c ≤ '9') || c == '-' || c == '_'
    || c == '.'

/-- A client's id, if it is not empty, at most `max` characters, and only letters, digits and
`-._`: safe in a header and in a log. -/
def accept? (max : Nat) (s : String) : Option String :=
  if 0 < s.length && s.length ≤ max && s.toList.all allowed then some s else none

theorem accept?_eq_some {max : Nat} {s t : String} :
    accept? max s = some t ↔
      t = s ∧ 0 < s.length ∧ s.length ≤ max ∧ ∀ c ∈ s.toList, allowed c = true := by
  unfold accept?
  split
  · rename_i h
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    simp only [Option.some.injEq]
    exact ⟨fun e => ⟨e.symm, h.1.1, h.1.2, h.2⟩, fun ⟨e, _⟩ => e.symm⟩
  · rename_i h
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    simp only [reduceCtorEq, false_iff, not_and]
    exact fun _ a b c => h ⟨⟨a, b⟩, c⟩

/-- Bytes as hexadecimal. -/
def ofBytes (b : List UInt8) : String :=
  String.ofList (b.flatMap fun x => [hexDigit (x.toNat / 16), hexDigit (x.toNat % 16)])

theorem allowed_hexDigit : ∀ k, k < 16 → allowed (hexDigit k) = true := by
  decide

/-- An id made from `n` random bytes is accepted from a client when `2 * n ≤ max`. -/
theorem accept?_ofBytes {max : Nat} {b : List UInt8} (hpos : 0 < b.length)
    (hmax : 2 * b.length ≤ max) : accept? max (ofBytes b) = some (ofBytes b) := by
  have len : (ofBytes b).length = 2 * b.length := by
    simp [ofBytes, List.length_flatMap, List.map_const', List.sum_replicate_nat, Nat.mul_comm]
  refine accept?_eq_some.mpr ⟨rfl, by omega, by omega, ?_⟩
  simp only [ofBytes, String.toList_ofList, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
    or_false]
  rintro c ⟨x, _, rfl | rfl⟩
  · exact allowed_hexDigit _ (by have := x.toNat_lt; omega)
  · exact allowed_hexDigit _ (Nat.mod_lt _ (by decide))

/-- The response with `x-request-id` set to `id`, and no other. -/
def tag (id : String) (r : Response) : Response :=
  { r with headers := r.headers.filter (·.1 != "x-request-id") ++ [("x-request-id", id)] }

theorem header_tag (id : String) (r : Response) :
    (tag id r).headers.filter (·.1 == "x-request-id") = [("x-request-id", id)] := by
  simp only [tag, List.filter_append, List.filter_filter]
  rw [List.filter_eq_nil_iff.mpr (by simp)]
  simp

end RequestId

/-! ## The access log -/

/-- One request, as the access log records it. -/
structure Access where
  /-- Milliseconds since the epoch, by the wall clock. -/
  time_ms : Nat
  method : Method
  path : List String
  status : Nat
  duration_us : Nat
  /-- The size of the response's body. -/
  bytes : Nat
  requestId : String

def Access.time (a : Access) : String :=
  let dateTime := Civil.DateTime.ofUnix (a.time_ms / 1000 : Nat)
  let nanos : Fin 1000000000 := ⟨a.time_ms % 1000 * 1000000, by omega⟩
  (TimeFormat.printRfc3339? { dateTime, nanos, offset := ⟨0, by decide⟩ }).getD ""

/-- The record's fields in a fixed order, as `slog`'s JSON handler writes them. -/
def Access.json (a : Access) : Json :=
  .obj #[("time", .str a.time), ("method", .str (methodName a.method)),
    ("path", .str (pathText a.path)), ("status", .num a.status),
    ("duration_ms", .num (JsonNumber.ofDecimal a.duration_us 3)), ("bytes", .num a.bytes),
    ("request_id", .str a.requestId)]

def Access.line (a : Access) : String :=
  a.json.compress

end Ops

end Lanes.Http
