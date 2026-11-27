/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std.Async
public import Lanes.Runtime.IO.Shell
public import Lanes.Outside.Basic
public import Lanes.Web.Http.Wire
public import Lanes.Web.IO.Tls
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
  deriving DecidableEq, Repr, Hashable

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

private def converse (socket : TCP.Socket.Client) (address : Std.Net.SocketAddress)
    (request : ByteArray) (config : Config) : Async (Option Response) := do
  socket.connect address
  socket.send request
  let mut received := ByteArray.empty
  repeat
    let arrived ← socket.recv? 65536
    received := received ++ arrived.getD .empty
    if let .done answer := Response.read config.maxResponseBytes received arrived.isNone then
      return answer
  return none

/-- Over TLS: the handshake, the request, then what is decrypted until the answer is whole. Only
the server's `close_notify` ends the response: a connection that ends without it may have been
cut by an attacker, so a response framed by its end is then no answer. -/
private def converseTls (socket : TCP.Socket.Client) (address : Std.Net.SocketAddress)
    (request : ByteArray) (session : Tls.Session) (config : Config) : Async (Option Response) := do
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
    if let .done answer := Response.read config.maxResponseBytes received (← session.closed) then
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

/-- Make one call: its response, or `none` if there is none by the deadline. `Async.race` leaves
the loser running, so the socket is closed whoever wins: that fails what a call given up on
still waits for, and ends its task. -/
def exchange (call : Call) (config : Config) : Async (Option Response) := do
  let some request := call.request.wire call.host | return none
  let socket ← TCP.Socket.Client.mk
  let attempt : Async (Option Response) := do
    try
      let some address ← resolve call | return none
      match call.scheme with
      | .http => converse socket address request config
      | .https =>
        converseTls socket address request (← Tls.Session.start config.trust call.host) config
    catch _ => pure none
  let patience := (fun _ => (none : Option Response)) <$> Async.sleep (.ofNat config.timeout_ms)
  try Async.race attempt patience
  finally socket.close

/-- Makes the call on a task of its own, so the shard does not wait for the network, and hands
the answer back as an input. An answer that finds the inbox full is dropped. -/
def handler {sys : System σ} [Hashable σ.Id] (port : Port σ) (config : Config := {})
    (rt : Runtime sys) (out : σ.Out) : Async Unit := do
  if let some (id, call) := port.called out then
    background do
      let answer ← try exchange call config catch _ => pure none
      discard <| rt.tryInput (port.reply id answer)

end Lanes.Http.Client
