/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Reminders.App

/-!
# The reminders over HTTP

Three routes: the list, a form that schedules a reminder, and a cancel. The time a request
arrived is written into it by the server's `arrive` (`Reminders.stamp`), so that it is in the
journal and the same on replay; the scheduler learns the time from it.
-/

namespace Reminders.Web

open Lanes Lanes.Http
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

def stageText : Stage → String
  | .waiting => "waiting"
  | .sent => "sent"
  | .failed => "failed"
  | .cancelled => "cancelled"

def Row (r : Reminder) : Html :=
  <li>
    {s!"#{r.id} at {r.at_ms} ms: {r.text} ({stageText r.stage})"}
    {if r.stage = .waiting then
      <form method="post" action={Routes.cancel.link r.id} style="display:inline">
        <button type="submit">"Cancel"</button>
      </form>
      else Html.empty}
  </li>

def Page (reminders : List Reminder) (notice : String) : Html :=
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

def remindIn (id : ReqId) (r : Request) : Except Response (SchedIn ⊕ In) := do
  let some now_ms := (r.header? arrivedHeader).bind String.toNat?
    | .error (.text "no arrival time\n" 500)
  let some text := r.field? "text" | .error (.text "a reminder needs a text\n" 400)
  let some in_s := (r.field? "in").bind String.toNat? | .error (.text "in how many seconds?\n" 400)
  return .inr (.remind id now_ms text in_s)

def decode (id : ReqId) (r : Request) : Except Response (SchedIn ⊕ In) :=
  (dispatch [
    Routes.home.handle fun () _ => .ok (.inr (.list id)),
    Routes.remind.handle fun () r => remindIn id r,
    Routes.cancel.handle fun n _ => .ok (.inr (.cancel id n))
  ] r).getD (.error (.text "not found\n" 404))

def bridge : Bridge (joinSig (Schedule.sig Key Task Answer) sig) where
  decode := decode
  encode
    | .inr (.reply req reminders notice) => some (req, .html (Page reminders notice).document)
    | _ => none

/-! ## Saving -/

def actors (config : Config) : Kernel.Image.Codecs (system config) where
  id := Codec.of (Unit ⊕ Unit)
  state
    | .inl () => Codec.of (Schedule.State Key Task)
    | .inr () => Codec.of State
  msg
    | .inl () => Codec.of (Schedule.Msg Key Task Answer)
    | .inr () => Codec.of In

end Reminders.Web
