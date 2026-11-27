/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Bank

/-!
# The bank behind a web page

The bank reference app served over HTTP with a server-rendered page. All state stays in the
account actors. The browser holds no logic: HTMX swaps in the HTML fragments the server sends.

Run with `lake exe bankWeb` (`Main.lean`) and open http://127.0.0.1:8080.
-/

namespace BankWeb

open Lanes Bank
open scoped Lanes.Html

abbrev Acct := Fin 3

def toAcct (n : Nat) : Option Acct :=
  if h : n < 3 then some ⟨n, h⟩ else none

def parseAcct (s : String) : Option Acct :=
  s.toNat? >>= toAcct

/-! Links and request matching both come from these routes, so they cannot disagree. -/
namespace Routes

def home : Http.Route Unit := .get .root
def account : Http.Route Nat := .get ("accounts" /> .nat)
def transfer : Http.Route Unit := .post (.seg "transfer")

end Routes

/-- Sent by a completed transfer; the balances listen for it and reload. -/
def transferred : String := "transferred"

def AccountRow (account : Acct) : Html :=
  <tr>
    <td>{s!"Account {account}"}</td>
    <td {Hx.request Routes.account account} {Hx.trigger [.load, .fromBody (.event transferred)]}>"…"</td>
  </tr>

def TransferForm : Html :=
  <form {Hx.request Routes.transfer ()} {Hx.target "#result"}>
    <label>"From " <input name="src" type="number" min="0" max="2" value="0" required/></label>
    <label>" to " <input name="dst" type="number" min="0" max="2" value="1" required/></label>
    <label>" amount " <input name="amount" type="number" min="0" value="10" required/></label>
    <button type="submit">"Transfer"</button>
  </form>

def Page : Html :=
  <html lang="en">
    <head>
      <meta charset="utf-8"/>
      <title>"Lanes Bank"</title>
      <script src="https://unpkg.com/htmx.org@2.0.4"></script>
    </head>
    <body>
      <h1>"Lanes Bank"</h1>
      <table>{(List.finRange 3).map AccountRow}</table>
      <TransferForm/>
      <p id="result"></p>
    </body>
  </html>

def OutcomeView : Outcome → Html
  | .accepted => <span class="ok">"Transfer accepted."</span>
  | .insufficient => <span class="error">"Insufficient funds."</span>
  | .balance amount => <span>{amount}</span>

def parseTransfer (id : Http.ReqId) (r : Http.Request) : Option (Transfer Acct) := do
  let src ← r.field? "src" >>= parseAcct
  let dst ← r.field? "dst" >>= parseAcct
  let amount ← r.field? "amount" >>= String.toNat?
  return { req := id, src, dst, amount }

def bridge : Http.Bridge (sig Acct) where
  decode id r :=
    (Http.dispatch [
      Routes.home.handle fun () _ => .error (.html Page.document),
      Routes.account.handle fun n _ =>
        match toAcct n with
        | some account => .ok (.balance id account)
        | none => .error (.text "no such account\n" 404),
      Routes.transfer.handle fun () r =>
        match parseTransfer id r with
        | some t => .ok (.transfer t)
        | none => .error (.html (<span class="error">"Invalid transfer."</span>).render 400)
    ] r).getD (.error (.text "not found\n" 404))
  encode out :=
    let response := Http.Response.html (OutcomeView out.outcome).render
    some (out.req, match out.outcome with
      | .accepted => response.trigger transferred
      | _ => response)

end BankWeb
