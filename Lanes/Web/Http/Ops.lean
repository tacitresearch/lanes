/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Lib.Metrics
public import Lanes.Lib.Crypto.Native
public import Lanes.Lib.Encoding.Json
public import Lanes.Lib.Log
public import Lanes.Lib.Net.Ip
public import Lanes.Proof.Utf8
public import Lanes.Web.Http.Basic

/-!
What the HTTP server tells its operators, as pure functions: which requests are theirs (a
metrics page, liveness, readiness), what each answers, the server's counts and how they render
as metrics, a request id taken from the client or made, and a line of the access log.

Nothing here reaches a system: an operator's request is answered by the server
(`docs/decisions/D69-observability.md`). With the default configuration no request is the
operators' (`route?_default`), and a request is one only at a path configured for it
(`route?_some`). The metrics page is answered only to a peer `OpsConfig.metricsAccess` allows, by
default one on a loopback address, however the client wrote its path (`route?_metrics`), and to
any other as if there were none (`route?_hidden`); liveness and readiness answer every peer
alike (`route?_peer`). Readiness answers `200` exactly when the shard has recovered and the server is
not stopping (`answer_ready`). A request id taken from a client is bounded and has only letters,
digits and `-._` (`RequestId.accept?_eq_some`), and so does one made (`RequestId.accept?_ofBytes`);
a response carries exactly one (`header_tag`). A line of the access log is a log record
(`Lanes/Lib/Log.lean`): one line, the JSON text of its record (`Ops.Access.parse_line`, in
`Lanes/Web/Http/OpsSound.lean`). It holds the method, the path without its query, the status,
the time taken, the size of the body and the request id; never a header, a query or a body.
-/

@[expose] public section

namespace Lanes.Http

/-- Who may read the metrics page. Its path is matched after percent-decoding, so a rule of a
load balancer on the path as written (`/metrics`) lets `/%6Detrics` by; this is what keeps the
page from the internet. -/
inductive MetricsAccess where
  /-- A peer on a loopback address: a scraper on the same machine. -/
  | loopback
  /-- A peer on a loopback address, or a request with `Authorization: Bearer` and this token,
  compared in a time that depends on the lengths only. -/
  | token (secret : String)
  /-- Every peer: only where something else keeps the page from the internet. -/
  | anyone
  deriving DecidableEq, Repr

/-- Everything is off by default. A path is the request's path as the server reads it, with no
query (`/metrics`). -/
structure OpsConfig where
  /-- The metrics page, in the Prometheus text format. -/
  metricsPath : Option String := none
  /-- Who may read it. Any other peer is answered `404` at its path. -/
  metricsAccess : MetricsAccess := .loopback
  /-- `200` while the server answers at all. -/
  livenessPath : Option String := none
  /-- `200` once the shard has booted, and `503` from `Server.drain` or `stop`. -/
  readinessPath : Option String := none
  accessLog : Log.Sink := .off
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
  /-- The metrics page, asked for by a peer it is not for: `404`, as if there were none. -/
  | hidden
  | live
  | ready
  deriving DecidableEq, Repr

/-- Whether the peer is on a loopback address. `none` is a peer the server could not read. -/
def fromLoopback (peer : Option Ip.Addr) : Bool :=
  peer.any Ip.Addr.isLoopback

/-- The token of an `Authorization: Bearer` header. -/
def bearer? (r : Request) : Option String :=
  (r.header? "authorization").bind fun v =>
    match v.splitOn " " with
    | [scheme, token] => if scheme.toLower == "bearer" && !token.isEmpty then some token else none
    | _ => none

/-- Whether `access` lets `peer` read the metrics page with request `r`. -/
def allows : MetricsAccess → Option Ip.Addr → Request → Bool
  | .loopback, peer, _ => fromLoopback peer
  | .token secret, peer, r =>
    fromLoopback peer || (bearer? r).any fun given => Bytes.same given.toUTF8 secret.toUTF8
  | .anyone, _, _ => true

theorem allows_eq_true {a : MetricsAccess} {peer : Option Ip.Addr} {r : Request} :
    allows a peer r = true ↔ fromLoopback peer = true ∨ a = .anyone ∨
      ∃ secret, a = .token secret ∧ bearer? r = some secret := by
  cases a with
  | loopback => simp [allows]
  | anyone => simp [allows]
  | token secret =>
    simp only [allows, Bool.or_eq_true, Option.any_eq_true, Bytes.same_iff, String.toUTF8,
      toByteArray_inj, reduceCtorEq, MetricsAccess.token.injEq, false_or]
    constructor
    · rintro (h | ⟨given, h, rfl⟩)
      · exact .inl h
      · exact .inr ⟨given, rfl, h⟩
    · rintro (h | ⟨_, rfl, h⟩)
      · exact .inl h
      · exact .inr ⟨_, h, rfl⟩

/-- The operators' endpoint a request from `peer` asks for, if any: a `GET` at a configured
path. -/
def route? (c : OpsConfig) (peer : Option Ip.Addr) (r : Request) : Option Endpoint :=
  if r.method != .get then none
  else
    let path := some (pathText r.path)
    if c.metricsPath == path then
      some (if allows c.metricsAccess peer r then .metrics else .hidden)
    else if c.livenessPath == path then some .live
    else if c.readinessPath == path then some .ready
    else none

theorem route?_default (peer : Option Ip.Addr) (r : Request) : route? {} peer r = none := by
  simp [route?]

/-- Only a `GET` at a path configured for it is the operators'. -/
theorem route?_some {c : OpsConfig} {peer : Option Ip.Addr} {r : Request} {e : Endpoint}
    (h : route? c peer r = some e) :
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

/-- The metrics page is answered only to a peer on a loopback address, or to one the
configuration lets in. The path is compared once decoded, so this holds however it was
written. -/
theorem route?_metrics {c : OpsConfig} {peer : Option Ip.Addr} {r : Request}
    (h : route? c peer r = some .metrics) :
    fromLoopback peer = true ∨ c.metricsAccess = .anyone ∨
      ∃ secret, c.metricsAccess = .token secret ∧ bearer? r = some secret := by
  refine allows_eq_true.mp ?_
  dsimp only [route?] at h
  split at h
  · simp at h
  · split at h
    · split at h
      · assumption
      · simp at h
    · split at h
      · simp at h
      · split at h <;> simp at h

/-- By default, only to a peer on a loopback address. -/
theorem route?_metrics_loopback {c : OpsConfig} {peer : Option Ip.Addr} {r : Request}
    (hc : c.metricsAccess = .loopback) (h : route? c peer r = some .metrics) :
    fromLoopback peer = true := by
  rcases route?_metrics h with h | h | ⟨_, h, _⟩ <;> simp_all

/-- A `GET` at the metrics page's path, from a peer it is not for, is answered as no page. -/
theorem route?_hidden {c : OpsConfig} {peer : Option Ip.Addr} {r : Request}
    (hm : r.method = .get) (hp : c.metricsPath = some (pathText r.path))
    (ha : allows c.metricsAccess peer r = false) : route? c peer r = some .hidden := by
  simp [route?, hm, hp, ha]

/-- Liveness and readiness are the same to every peer: a load balancer, wherever it is, reaches
them. -/
theorem route?_peer {c : OpsConfig} {peer : Option Ip.Addr} {r : Request} {e : Endpoint}
    (he : e = .live ∨ e = .ready) (h : route? c peer r = some e) (other : Option Ip.Addr) :
    route? c other r = some e := by
  dsimp only [route?] at h ⊢
  split at h
  · simp at h
  · rename_i hm
    simp only [hm]
    split at h
    · split at h <;> rcases he with rfl | rfl <;> simp at h
    · rename_i h1
      simp only [h1]
      exact h

structure Health where
  /-- The shard has booted and handed over what booting put out. -/
  recovered : Bool
  /-- The server is draining or stopping. -/
  stopping : Bool

def Health.ready (h : Health) : Bool :=
  h.recovered && !h.stopping

def answer (e : Endpoint) (health : Health) (metrics : String) : Response :=
  match e with
  | .metrics => { headers := [("content-type", Metrics.contentType)], body := metrics.toUTF8 }
  | .hidden => .text "not found\n" 404
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

namespace Stats

variable {bounds : List Nat}

def answered (method : Method) (status duration_us : Nat) (s : Stats bounds) : Stats bounds :=
  { s with requests := bumpKey (methodName method, statusClass status) s.requests
           latency := s.latency.observe duration_us }

def refuse (s : Stats bounds) : Stats bounds :=
  { s with refused := s.refused + 1 }

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

/-- The record of a request, as `slog`'s JSON handler writes an attribute list: the time, `INFO`,
`request`, then the fields in a fixed order and the request id. -/
def Access.record (a : Access) : Log.Record where
  time_ms := a.time_ms
  level := .info
  msg := "request"
  attrs := [("method", .str (methodName a.method)), ("path", .str (pathText a.path)),
    ("status", .num a.status), ("duration_ms", .num (JsonNumber.ofDecimal a.duration_us 3)),
    ("bytes", .num a.bytes)]
  requestId := some a.requestId

def Access.json (a : Access) : Json :=
  a.record.json

def Access.line (a : Access) : String :=
  Log.render a.record

end Ops

end Lanes.Http
