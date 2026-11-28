import Chat.Web
import Lanes.Testing

/-!
Run by `lake test`. The room model-checked against itself as the spec, on joins, lines and
leaves in any order (rule 5.1); then the front: what the bridge makes of the requests the server
hands it for a socket, and of the rest. `Tests/WebSocket.lean` in Lanes runs a room like this
one over a real socket.
-/

open Lanes Chat Chat.Web

instance : sig.Inspect := {}
instance : (system { members_max := 1 }).Inspect := {}

def requests : List Request :=
  [.join 1, .join 2, .say 3 1 "hi", .leave 4 1]

def check : Lanes.Testing.Result :=
  let report := Check.system (system { members_max := 1 })
    { driver := (service { members_max := 1 }).monitored (Driver.anyOrder requests) }
    [ Check.refines "every output is allowed by the spec",
      .always "the room holds at most one member" fun w =>
        let m : State := w.state.state (); m.length ≤ 1,
      .always "a line goes only to sockets that asked to join" fun w =>
        w.state.outbox.all fun o => match o.reply with
          | .line _ => o.req == 1 || o.req == 2
          | _ => true,
      .sometimes "a line is sent to every member" fun w =>
        w.state.outbox.any (· == ⟨1, .line "hi"⟩),
      .sometimes "a member beyond the bound is refused" fun w =>
        w.state.outbox.any fun o => o.reply matches .full ]
  .check "chat: the room refines itself as the spec, on requests in any order" report
    report.renderSystem

def head : Http.Request :=
  { method := .get, path := ["chat"]
    headers := [("host", "x"), ("upgrade", "websocket"), ("connection", "Upgrade"),
      ("sec-websocket-key", "dGhlIHNhbXBsZSBub25jZQ=="), ("sec-websocket-version", "13")] }

def front : List (String × Bool) :=
  let said := Http.Stream.tag ((WebSocket.Ask.message (.text "hi")).request head 0) 7
  let gone := Http.Stream.tag ((WebSocket.Ask.closed 1001).request head 1) 7
  [ ("the request that opens a socket joins", bridge.decode 3 head matches .ok (.join 3)),
    ("a handshake without its key is refused 400 before the system sees it",
      match bridge.decode 3 { head with headers := head.headers.filter (·.1 != "sec-websocket-key") } with
      | .error r => r.status == 400
      | .ok _ => false),
    ("a line a socket sends is said by that socket", bridge.decode 8 said matches .ok (.say 8 7 "hi")),
    ("a socket that ends leaves", bridge.decode 9 gone matches .ok (.leave 9 7)),
    ("a line for a member is a text to its socket",
      (WebSocket.Send.ofResponse? (encode ⟨7, .line "hi"⟩)) matches some (.message (.text "hi"))),
    ("the page is served", match bridge.decode 1 { method := .get, path := [] } with
      | .error r => r.status == 200
      | .ok _ => false) ]

def main (args : List String) : IO UInt32 :=
  Lanes.Testing.report args (check :: Lanes.Testing.Result.tests front)
