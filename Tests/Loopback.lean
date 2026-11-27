/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Tests.Gate
import Tests.Web
import Tests.Fixtures.BankWeb
import Tests.Fixtures.Upload

/-!
`Http.Loopback`: an application's front end driven with no socket, through the connection, the
gate and the system the server runs, and read back by the client's reader.
-/

namespace Tests.Loopback

open Lanes Lanes.Http Tests.Gate

def status (r : Except String Response) : Nat :=
  match r with
  | .ok r => r.status
  | .error _ => 0

def text (r : Except String Response) : String :=
  match r with
  | .ok r => (String.fromUTF8? r.body).getD ""
  | .error _ => ""

def bank := Tests.Fixtures.Bank.bank Tests.Fixtures.BankWeb.Acct 100

open Tests.Fixtures.Upload in
/-- Requests that stream, with no socket: uploads in pieces, a streamed response, events. -/
def streamed : List (String × Bool) :=
  let lb := Loopback.start system bridge
    (conn := { streams := some Tests.Fixtures.Upload.streams, piece_max := 1000, poll_ms := 10 })
  let (lb, up) := lb.send { method := .put, path := ["upload"], body := body 100000 }
  let (lb, count) := lb.get ["count"]
  let (lb, written) := lb.converse
    ["GET /events HTTP/1.1\r\nHost: h\r\nLast-Event-ID: 0\r\nConnection: close\r\n\r\n".toUTF8]
  let bytes := "POST /upload HTTP/1.1\r\nHost: h\r\nTransfer-Encoding: chunked\r\n\r\n".toUTF8
    ++ chunked (body 5000) 300
  let (_, pieces) := lb.converse ((List.range ((bytes.size + 99) / 100)).map fun k =>
    bytes.extract (k * 100) (k * 100 + 100))
  [ ("loopback: an upload of 100 KB in pieces of 1000 bytes is answered with its size and checksum",
      text up == s!"100000 bytes, Adler-32 {checksum (body 100000)}\n"),
    ("loopback: an upload in chunks, sent 100 bytes at a time, likewise",
      ((String.fromUTF8? pieces).getD "").endsWith s!"5000 bytes, Adler-32 {checksum (body 5000)}\n"),
    ("loopback: a streamed response is read back whole", text count == "0\n1\n2\n"),
    ("loopback: a stream of events resumes after the event the client last read",
      (Sse.received written).map (·.data) == ["e1", "e2"]) ]

/-- The pieces of the stream protocol, one at a time. -/
def parts : List (String × Bool) :=
  let head : Request := { method := .put, path := ["upload"] }
  let e : Sse.Event := { data := "a\nb", event := some "post", id := some "7", retry := some 500 }
  let busy : Conn :=
    { inflow := some { seq := 0, head, framing := .length 3, close := false, asked := some (.empty, false)
                       again := some 40 } }
  [ ("stream: a piece tagged with its head reads back as the piece of that head",
      Stream.msg? (Stream.tag (Stream.piece head 3 "xyz".toUTF8 true) 9)
        == some (.piece 9 3 "xyz".toUTF8 true)
      && Stream.msg? (Stream.tag (Stream.pull head 4 (some "e1")) 2) == some (.pull 2 4 (some "e1"))
      && Stream.msg? head == none),
    ("sse: an event is read back from its bytes, a comment between events is none",
      Sse.parse ((String.fromUTF8? (e.encode ++ Sse.heartbeat ++ e.encode)).getD "").toList == [e, e]),
    ("conn: a piece the system was too busy for is looked at again at its time, the earlier of two",
      busy.wakeAt {} == some 40 && Conn.earlier (some 3) (some 2) == some 2
        && Conn.earlier none (some 5) == some 5) ]

def tests : List (String × Bool) :=
  let lb := Loopback.start (Server.system echo) bridge
  let (lb, ok) := lb.get []
  let (lb, bad) := lb.get ["bad"]
  let (_, missing) := lb.send { method := .get, path := [], headers := [("x", "\r")] }
  let quiet := Loopback.start (Server.system Tests.Web.mute) Tests.Web.slugBridge
    (gate := { requestTimeout_ms := 50 })
  let (quiet, slug) := quiet.get ["echo", "a b"]
  let (quiet, never) := quiet.get ["never"]
  let large := Loopback.start (Server.system Tests.Web.mute) Tests.Web.slugBridge
    (conn := { limits := { body_max := 4 } })
  let (_, tooLarge) := large.post ["x"] [("a", "too long")]
  let bankLb := Loopback.start bank Tests.Fixtures.BankWeb.bridge
  let (bankLb, moved) := bankLb.post ["transfer"] [("src", "0"), ("dst", "1"), ("amount", "30")]
  let (bankLb, balance) := bankLb.get ["accounts", "1"]
  let (bankLb, refused) := bankLb.post ["transfer"] [("src", "0"), ("dst", "2"), ("amount", "500")]
  let (_, after) := bankLb.get ["accounts", "0"]
  [ ("loopback: a request is answered through the connection, the gate and the system",
      status ok == 200 && text ok == "ok"),
    ("loopback: a request the bridge refuses gets its response", status bad == 400),
    ("loopback: a header that cannot be written is left out, and the request still answered",
      status missing == 200),
    ("loopback: a link is decoded as the server decodes it", text slug == "a b"),
    ("loopback: a request the system never answers gets the gate's 504 when its time passes",
      status never == 504 && quiet.nextId == 2),
    ("loopback: a body over the connection's limit is refused 413", status tooLarge == 413),
    ("loopback: the bank moves money and shows it, its state carried from one request to the "
      ++ "next", status moved == 200 && (text balance).endsWith "<span>130</span>"
        && status refused == 200 && (text after).endsWith "<span>70</span>") ] ++ streamed ++ parts

end Tests.Loopback
