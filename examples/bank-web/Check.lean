import Lanes
import BankWeb

/-!
What the page asks for and what the bridge makes of it, run by `lake test`: every request the
page can make is decoded to the message it means, the page asks for balances and posts
transfers at its own routes, and the whole front, driven with no socket by `Http.Loopback`,
moves money and shows it. The bank behind it is checked in `examples/bank`.
-/

open Lanes Bank BankWeb

def get (path : List String) : Http.Request := { method := .get, path }

def form : Http.Request :=
  { method := .post, path := ["transfer"], body := "src=0&dst=1&amount=10".toUTF8 }

def body (r : Except String Http.Response) : String :=
  match r with
  | .ok r => (String.fromUTF8? r.body).getD ""
  | .error _ => ""

/-- A transfer posted and the balances read, through the connection, the gate and the bank. -/
def throughTheFront : Bool :=
  let lb := Http.Loopback.start (bank Acct 100) bridge
  let (lb, moved) := lb.post ["transfer"] [("src", "0"), ("dst", "1"), ("amount", "30")]
  let (lb, short) := lb.post ["transfer"] [("src", "2"), ("dst", "0"), ("amount", "101")]
  let (lb, zero) := lb.get ["accounts", "0"]
  let (_, one) := lb.get ["accounts", "1"]
  (body moved).endsWith "Transfer accepted.</span>" && (body short).endsWith "Insufficient funds.</span>"
    && (body zero).endsWith "<span>70</span>" && (body one).endsWith "<span>130</span>"

def tests : List (String × Bool) :=
  [ ("through the front, a transfer moves money and a balance shows it", throughTheFront),
 ("a balance is asked of the account the link names",
      match bridge.decode 7 (get ["accounts", "2"]) with
      | .ok (.balance 7 account) => account == 2
      | _ => false),
    ("a transfer is read from the form",
      match bridge.decode 8 form with
      | .ok (.transfer t) => t.req == 8 && t.src == 0 && t.dst == 1 && t.amount == 10
      | _ => false),
    ("an account that does not exist is answered 404",
      match bridge.decode 9 (get ["accounts", "3"]) with
      | .error response => response.status == 404
      | _ => false),
    ("the home page is answered by the bridge itself",
      match bridge.decode 9 (get []) with
      | .error response => response.status == 200
      | _ => false),
    ("the page asks for balances and posts transfers at its own routes",
      let page := Page.render
      page.contains "hx-get=\"/accounts/2\" hx-trigger=\"load, transferred from:body\""
        && page.contains "<form hx-post=\"/transfer\" hx-target=\"#result\">") ]

def main : IO UInt32 := do
  let failed := tests.filter (!·.2)
  for (name, ok) in tests do
    IO.println s!"{if ok then "ok  " else "FAIL"} {name}"
  return if failed.isEmpty then 0 else 1
