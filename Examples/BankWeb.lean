/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Examples.Bank

/-!
# The bank behind a web page

The bank reference app served over HTTP with a server-rendered page. All state stays in the
account actors. The browser holds no logic: HTMX swaps in the HTML fragments the server sends.

The pieces:

- views are pure functions into `Html`;
- `bridge.decode` parses each request into a `Bank.Request` or answers directly (the page, `404`,
  `400`);
- `bridge.encode` renders the bank's answer as an HTML fragment;
- the account actors are the ones checked and proved in `Examples.Bank`, unchanged.

Run with `lake exe bankWeb` and open http://127.0.0.1:8080.
-/

namespace Examples.BankWeb

open Lanes Examples.Bank

/-- The demo runs three accounts. -/
abbrev Acct := Fin 3

/-- Read an account name from text. -/
def parseAcct (s : String) : Option Acct := do
  let n ← s.toNat?
  if h : n < 3 then some ⟨n, h⟩ else none

/-- One account row. It loads its balance when the page loads and after every transfer. -/
def AccountRow (account : Acct) : Html :=
  <tr>
    <td>{s!"Account {account}"}</td>
    <td hx-get={s!"/accounts/{account}"} hx-trigger="load, transferred from:body">"…"</td>
  </tr>

/-- The transfer form. Its result is swapped into `#result`. -/
def TransferForm : Html :=
  <form hx-post="/transfer" hx-target="#result">
    <label>"From " <input name="src" type="number" min="0" max="2" value="0" required/></label>
    <label>" to " <input name="dst" type="number" min="0" max="2" value="1" required/></label>
    <label>" amount " <input name="amount" type="number" min="0" value="10" required/></label>
    <button type="submit">"Transfer"</button>
  </form>

/-- The page. -/
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

/-- The fragment shown for each answer of the bank. -/
def OutcomeView : Outcome → Html
  | .accepted => <span class="ok">"Transfer accepted."</span>
  | .insufficient => <span class="error">"Insufficient funds."</span>
  | .balance amount => <span>{amount}</span>

/-- Parse a transfer form. -/
def parseTransfer (id : Http.ReqId) (r : Http.Request) : Option (Transfer Acct) := do
  let src ← r.field? "src" >>= parseAcct
  let dst ← r.field? "dst" >>= parseAcct
  let amount ← r.field? "amount" >>= String.toNat?
  return { req := id, src, dst, amount }

/-- How the bank meets HTTP. -/
def bridge : Http.Bridge (sig Acct) where
  decode id r :=
    match r.method, r.path with
    | .get, [] => .error (.html Page.document)
    | .get, ["accounts", a] =>
      match parseAcct a with
      | some account => .ok (.balance id account)
      | none => .error (.text "no such account\n" 404)
    | .post, ["transfer"] =>
      match parseTransfer id r with
      | some t => .ok (.transfer t)
      | none => .error (.html (<span class="error">"Invalid transfer."</span>).render 400)
    | _, _ => .error (.text "not found\n" 404)
  encode out :=
    let response := Http.Response.html (OutcomeView out.outcome).render
    -- A completed transfer tells the page to reload the balances.
    some (out.req, match out.outcome with
      | .accepted => response.withHeader "hx-trigger" "transferred"
      | _ => response)

end Examples.BankWeb

open Lanes Examples.Bank Examples.BankWeb in
def main (args : List String) : IO Unit := do
  let port := (args.head? >>= String.toNat?).getD 8080
  let server ← (Http.serve (bank Acct 100) bridge { port := port.toUInt16 }).block
  IO.println s!"Lanes Bank listening on http://127.0.0.1:{server.port.getD 0}"
  (← IO.getStdout).flush
  server.wait.block
