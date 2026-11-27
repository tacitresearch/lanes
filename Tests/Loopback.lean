/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Tests.Gate
import Tests.Web
import Tests.Fixtures.BankWeb

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
        && status refused == 200 && (text after).endsWith "<span>70</span>") ]

end Tests.Loopback
