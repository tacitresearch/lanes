/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std.Async
public import Lanes.Runtime.IO.Shell
public import Lanes.Outside.Basic
public import Lanes.Web.Http.Compress
public import Lanes.Web.Http.Sse
public import Lanes.Lib.Net.IO.Tls
public import Lanes.Lib.Net.Url

/-!
The HTTP client as an adapter. A system calls another service with an output and gets the
response, or the news that there is none, as an input. `Client.outside` is what such a service
may do, which the checker explores; `Client.handler` does it over a socket.

HTTP/1.1, or HTTPS through `Tls.Session`, one request per connection, over IPv4. What is sent
and what the bytes received mean are the pure `Request.wire` and `Response.read` either way.
-/

public section

namespace Lanes.Http.Client

open Std Std.Async

variable {σ : Signature}

inductive Scheme where
  | http
  /-- HTTP over TLS: the server's certificate is verified, and must be for the call's host. -/
  | https
  deriving DecidableEq, Repr, Hashable

structure Call where
  /-- An IPv4 address, or a name, resolved to its first IPv4 address. -/
  host : String
  port : UInt16
  request : Request
  scheme : Scheme := .http
  /-- Sent as `HEAD`, whatever the request's method, and the answer read without a body. -/
  headOnly : Bool := false
  deriving DecidableEq, Repr, Hashable

/-- What the `Host` header names: the host, and the port when it is not the scheme's. -/
def Call.authority (call : Call) : String :=
  if call.port == (if call.scheme == .https then 443 else 80) then call.host
  else call.host ++ ":" ++ toString call.port

/-- A call to the origin `url` names, `http://host[:port]` or `https://host[:port]` with at most a
`/` after it, the port the scheme's when it gives none; the request carries the path. -/
def Call.at (url : String) (request : Request) : Option Call := do
  let u ← Url.parse url
  let scheme ← match u.scheme with
    | some "http" => some Scheme.http
    | some "https" => some Scheme.https
    | _ => none
  let a ← u.authority
  unless a.userinfo.isNone && (u.path == "" || u.path == "/") && u.query.isNone
      && u.fragment.isNone do none
  let host ← match a.host with
    | .ip (.v4 n) => some (String.ofList (Ip.print4 n.val))
    | .ip (.v6 _) => none
    | .name s => if s.isEmpty || s.contains '%' then none else some s
  let port ← match a.port.filter (· != "") with
    | none => some (if scheme == .https then 443 else 80)
    | some digits => digits.toNat?.filter (fun n => 0 < n && n < 65536) |>.map (·.toUInt16)
  return { host, port, request, scheme }

/-- Which outputs are calls and which inputs answer them. `none` for a response means there was
none: the service could not be reached, took too long, or answered what is not HTTP. -/
structure Port (σ : Signature) where
  called : σ.Out → Option (Nat × Call)
  reply : (call : Nat) → Option Response → σ.In
  replied : σ.In → Option Nat

/-- What a service may do: answer a call that is open, once, with any response or with none. It
may also never answer, so whoever calls keeps its own deadline. It remembers the open calls. -/
@[expose] def outside (port : Port σ) : Outside σ (List Nat) where
  init := []
  allow calls x :=
    match port.replied x with
    | some call => if call ∈ calls then some (calls.erase call) else none
    | none => none
  observe calls out :=
    match port.called out with
    | some (call, _) => call :: calls
    | none => calls

/-- Every limit is explicit (rule 2.6). -/
structure Config where
  timeout_ms : Nat := 10000
  maxResponseBytes : Nat := 1048576
  /-- What an `https` server's certificate must chain to. -/
  trust : Tls.Trust := .system
  /-- Ask for gzip and read a response in gzip or `deflate`, as Go's client does, unless the
  request names its own `Accept-Encoding`; decoded, a body is bounded by `maxResponseBytes`
  too. -/
  acceptGzip : Bool := true

private def converse (socket : TCP.Socket.Client) (address : Std.Net.SocketAddress)
    (request : ByteArray) (read : ByteArray → Bool → Reading Response) : Async (Option Response) := do
  socket.connect address
  socket.send request
  let mut received := ByteArray.empty
  repeat
    let arrived ← socket.recv? 65536
    received := received ++ arrived.getD .empty
    if let .done answer := read received arrived.isNone then
      return answer
  return none

/-- Over TLS: the handshake, the request, then what is decrypted until the answer is whole. Only
the server's `close_notify` ends the response: a connection that ends without it may have been
cut by an attacker, so a response framed by its end is then no answer. -/
private def converseTls (socket : TCP.Socket.Client) (address : Std.Net.SocketAddress)
    (request : ByteArray) (session : Tls.Session) (read : ByteArray → Bool → Reading Response) :
    Async (Option Response) := do
  socket.connect address
  let flush : Async Unit := do
    let out ← session.take
    unless out.isEmpty do socket.send out
  repeat
    let done ← session.handshake
    flush
    if done then break
    let some arrived ← socket.recv? 65536 | return none
    session.feed arrived
  session.write request
  flush
  let mut received := ByteArray.empty
  repeat
    let arrived ← socket.recv? 65536
    if let some bytes := arrived then session.feed bytes
    received := received ++ (← session.readAll)
    flush
    if let .done answer := read received (← session.closed) then
      try session.shutdown; flush catch _ => pure ()
      return answer
    if arrived.isNone then return none
  return none

private def resolve (call : Call) : Async (Option Std.Net.SocketAddress) := do
  if let some addr := Std.Net.IPv4Addr.ofString call.host then return some (.v4 ⟨addr, call.port⟩)
  let found ← DNS.getAddrInfo call.host "" (some .ipv4)
  return found.toList.findSome? fun
    | .v4 addr => some (.v4 ⟨addr, call.port⟩)
    | .v6 _ => none

/-- Make one call: its response, or why there is none by the deadline (the address not found, the
connection or handshake refused, with OpenSSL's reason, no whole answer, or the time run out).
`Async.race` leaves the loser running, so the socket is closed whoever wins: that fails what a
call given up on still waits for, and ends its task. -/
def exchangeExplained (call : Call) (config : Config) : Async (Except String Response) := do
  let gzip := config.acceptGzip && !call.headOnly
    && (headerValue? call.request.headers "accept-encoding").isNone
  let call := if gzip then { call with request := { call.request with
    headers := call.request.headers ++ [("accept-encoding", "gzip")] } } else call
  let wire := if call.headOnly then call.request.wireHead else call.request.wire
  let some request := wire call.authority | return .error "the request cannot be written"
  let read := if call.headOnly then Response.readHead config.maxResponseBytes
    else Response.read config.maxResponseBytes
  let socket ← TCP.Socket.Client.mk
  let attempt : Async (Except String Response) := do
    try
      let some address ← resolve call | return .error s!"no IPv4 address for {call.host}"
      let answer ← match call.scheme with
        | .http => converse socket address request read
        | .https =>
          converseTls socket address request (← Tls.Session.start config.trust call.host) read
      return match answer with
        | none => .error "the connection ended without a whole answer"
        | some r => if gzip then decode config.maxResponseBytes r else .ok r
    catch e => pure (.error (toString e))
  let patience := (fun _ => (.error "no answer by the deadline" : Except String Response)) <$>
    Async.sleep (.ofNat config.timeout_ms)
  try Async.race attempt patience
  finally socket.close

/-- Make one call: its response, or `none` if there is none by the deadline. -/
def exchange (call : Call) (config : Config) : Async (Option Response) :=
  (·.toOption) <$> exchangeExplained call config

/-- One request to a server on this machine, for tests: its response, or an error that says why
there is none. -/
def fetch (port : UInt16) (request : Request) (config : Config := {}) (host := "127.0.0.1") :
    IO Response := do
  match ← (exchangeExplained { host, port, request } config).block with
  | .ok response => return response
  | .error why => throw (IO.userError s!"lanes: no response from {host}:{port} to {request.target}: {why}")

/-- A stream of events from a server on this machine, for tests: the events read once `enough`
holds of them, or when the server ends the stream, or at the deadline. -/
def events (port : UInt16) (request : Request) (enough : List Sse.Event → Bool)
    (timeout_ms : Nat := 5000) (host := "127.0.0.1") : IO (List Sse.Event) := do
  let some addr := Std.Net.IPv4Addr.ofString host | return []
  let some bytes := request.wire host | return []
  let socket ← TCP.Socket.Client.mk
  let received ← IO.mkRef ByteArray.empty
  let read : Async Unit := do
    socket.connect (.v4 ⟨addr, port⟩)
    socket.send bytes
    repeat
      let some more ← socket.recv? 65536 | break
      received.modify (· ++ more)
      if enough (Sse.received (← received.get)) then break
  try (Async.race (try read catch _ => pure ()) (Async.sleep (.ofNat timeout_ms))).block
  finally discard socket.close.toBaseIO
  return Sse.received (← received.get)

/-- Makes the call on a task of its own, so the worker that put the output out does not wait for
the network, and hands the answer back as an input. An answer that finds the inbox full is dropped. -/
def handler {sys : System σ} [Hashable σ.Id] (port : Port σ) (config : Config := {})
    (rt : Runtime sys) (out : σ.Out) : Async Unit := do
  if let some (id, call) := port.called out then
    background do
      let answer ← try exchange call config catch _ => pure none
      discard <| rt.tryInput (port.reply id answer)

/-- The call with `key` in `Idempotency-Key`, the header Stripe reads, unless it has one: a key
the application chose, which its own retries keep, comes first. -/
def Call.keyed (key : String) (call : Call) : Call :=
  if call.request.headers.any (·.1.toLower == "idempotency-key") then call
  else { call with request := { call.request with
    headers := call.request.headers ++ [("idempotency-key", key)] } }

/-- `handler`, with the idempotency key the application gives for each output (`Call.keyed`):
a key it chose from its own data, such as the id of the payment, so that a call made again, by
the application or after a restart, carries the key it carried the first time, and a service
that takes keys, as Stripe does, has its effect once. With no key, the call is made as it is. -/
def handlerKeyed {sys : System σ} [Hashable σ.Id] (port : Port σ) (key : σ.Out → Option String)
    (config : Config := {}) (rt : Runtime sys) (out : σ.Out) : Async Unit := do
  if let some (id, call) := port.called out then
    let call := match key out with
      | some k => call.keyed k
      | none => call
    background do
      let answer ← try exchange call config catch _ => pure none
      discard <| rt.tryInput (port.reply id answer)

end Lanes.Http.Client
