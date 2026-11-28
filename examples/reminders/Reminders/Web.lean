/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Reminders.App

/-!
# The reminders over HTTP

Three routes: the list, a form that asks for a reminder, and a cancel. The time a request
arrived is written into it by the server's `arrive` (`Reminders.Web.stamp`): a reminder is due
that long after it.
-/

namespace Reminders.Web

open Lanes Lanes.Http Lanes.Db.Jobs
open scoped Lanes.Html

namespace Routes

def home : Route Unit := .get .root
def remind : Route Unit := .post (.seg "remind")
def cancel : Route Nat := .post (.pre "cancel" .nat)

end Routes

def arrivedHeader : String := "x-reminders-arrived-ms"

/-- The time a request arrived, in milliseconds since the epoch. -/
def stamp (now_ms : Nat) (r : Request) : Request :=
  { r with headers := r.headers.filter (·.1 != arrivedHeader) ++ [(arrivedHeader, toString now_ms)] }

def statusText : Status → String
  | .pending => "waiting"
  | .done => "sent"
  | .failed => "failed"
  | .cancelled => "cancelled"

def Row (j : Job String) : Html :=
  <li>
    {s!"#{j.id} at {j.due_ms} ms: {j.work} ({statusText j.status})"}
    {if j.status = .pending then
      <form method="post" action={Routes.cancel.link j.id.toInt.toNat} style="display:inline">
        <button type="submit">"Cancel"</button>
      </form>
      else Html.empty}
  </li>

def Page (reminders : List (Job String)) (notice : String) : Html :=
  <html lang="en">
    <head>
      <meta charset="utf-8"/>
      <title>"Reminders"</title>
    </head>
    <body>
      <h1>"Reminders"</h1>
      <p id="notice">{notice}</p>
      <form method="post" action={Routes.remind.link ()}>
        <label>"Remind me of " <input name="text" required/></label>
        <label>" in " <input name="in" type="number" min="0" value="60" required/>" s"</label>
        <button type="submit">"Remind"</button>
      </form>
      <ul id="reminders">{Html.fragment (reminders.map Row)}</ul>
    </body>
  </html>

def remindIn (id : ReqId) (r : Request) : Except Response In := do
  let some now_ms := (r.header? arrivedHeader).bind String.toNat?
    | .error (.text "no arrival time\n" 500)
  let some text := r.field? "text" | .error (.text "a reminder needs a text\n" 400)
  let some in_s := (r.field? "in").bind String.toNat? | .error (.text "in how many seconds?\n" 400)
  return .request id (.remind text (Int64.ofNat (now_ms + in_s * 1000)))

def decode (id : ReqId) (r : Request) : Except Response In :=
  (dispatch [
    Routes.home.handle fun () _ => .ok (.request id .list),
    Routes.remind.handle fun () r => remindIn id r,
    Routes.cancel.handle fun n _ => .ok (.request id (.cancel (Int64.ofNat n)))
  ] r).getD (.error (.text "not found\n" 404))

def bridge : Bridge sig where
  decode := decode
  encode
    | .answered n a => some (n, .html (Page a.reminders a.notice).document)
    | .failed n => some (n, .text "The reminders are not available; try again.\n" 503)
    | .call _ => none

end Reminders.Web
