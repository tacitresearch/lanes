import Lanes
import BankWeb

/-!
What the page asks for and what the bridge makes of it, run by `lake test`: every request the
page can make is decoded to the message it means, and the page asks for balances and posts
transfers at its own routes. The bank behind it is checked in `examples/bank`.
-/

open Lanes Bank BankWeb

def get (path : List String) : Http.Request := { method := .get, path }

def form : Http.Request :=
  { method := .post, path := ["transfer"], body := "src=0&dst=1&amount=10".toUTF8 }

def tests : List (String × Bool) :=
  [ ("a balance is asked of the account the link names",
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
