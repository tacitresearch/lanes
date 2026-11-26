/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Html.Basic
public import Lanes.Http.Route

/-!
The htmx attributes and headers as typed values. A view says what it means, `Hx.request route
value`, and the attribute name and the URL both come from the route, so a view cannot `hx-post`
to a route that only answers `GET` or link to a path no route has. Attribute spellings live
here and nowhere else.

Written against htmx 2. Splice the values among a tag's attributes: `<button {Hx.request
Routes.transfer ()} {Hx.target "#result"}>`.
-/

@[expose] public section

namespace Lanes.Hx

open Lanes.Http

def verbAttr : Verb → String
  | .get => "hx-get"
  | .post => "hx-post"
  | .put => "hx-put"
  | .patch => "hx-patch"
  | .delete => "hx-delete"

def request {α : Type} (route : Route α) (a : α) : List Html.Attr :=
  [⟨verbAttr route.verb, some (route.link a)⟩]

/-- A CSS selector, or one of htmx's `this`, `closest …`, `find …`, `next …`, `previous …`. -/
def target (selector : String) : List Html.Attr :=
  [⟨"hx-target", some selector⟩]

inductive Swap where
  | innerHTML | outerHTML | textContent | beforebegin | afterbegin | beforeend | afterend
  | delete | none
  deriving DecidableEq, Repr

def Swap.name : Swap → String
  | .innerHTML => "innerHTML"
  | .outerHTML => "outerHTML"
  | .textContent => "textContent"
  | .beforebegin => "beforebegin"
  | .afterbegin => "afterbegin"
  | .beforeend => "beforeend"
  | .afterend => "afterend"
  | .delete => "delete"
  | .none => "none"

def swap (how : Swap) : List Html.Attr :=
  [⟨"hx-swap", some how.name⟩]

inductive Trigger where
  | load
  | click
  | change
  | submit
  | revealed
  /-- A named event, such as one a response sends with `Response.trigger`. -/
  | event (name : String)
  | every (seconds : Nat)
  /-- The same trigger, listening on the whole page instead of on the element. -/
  | fromBody (inner : Trigger)
  deriving Repr

def Trigger.render : Trigger → String
  | .load => "load"
  | .click => "click"
  | .change => "change"
  | .submit => "submit"
  | .revealed => "revealed"
  | .event name => name
  | .every seconds => s!"every {seconds}s"
  | .fromBody inner => inner.render ++ " from:body"

def trigger (triggers : List Trigger) : List Html.Attr :=
  [⟨"hx-trigger", some (", ".intercalate (triggers.map Trigger.render))⟩]

/-- Ask before sending. -/
def confirm (question : String) : List Html.Attr :=
  [⟨"hx-confirm", some question⟩]

/-- Links and forms inside the element load by request and swap, without a full page load. -/
def boost : List Html.Attr :=
  [⟨"hx-boost", some "true"⟩]

def pushUrl : List Html.Attr :=
  [⟨"hx-push-url", some "true"⟩]

/-- The element shown while the request is in flight. -/
def indicator (selector : String) : List Html.Attr :=
  [⟨"hx-indicator", some selector⟩]

end Lanes.Hx

namespace Lanes.Http

/-- Whether htmx made the request, so the answer should be a piece of a page, not all of it. -/
def Request.isHtmx (r : Request) : Bool :=
  r.header? "hx-request" == some "true"

/-- Fire `event` on the page when the response arrives; views listen with `Hx.Trigger.event`. -/
def Response.trigger (r : Response) (event : String) : Response :=
  r.withHeader "hx-trigger" event

/-- Make the browser go to `route`, as a redirect does for a request htmx did not make. -/
def Response.hxRedirect {α : Type} (r : Response) (route : Route α) (a : α) : Response :=
  r.withHeader "hx-redirect" (route.link a)

end Lanes.Http
