/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
The shared-cache model (`Lanes/Web/Http/SharedCache.lean`) in front of a site with a public home
page and an account page that shows whose session asked. Sent with no `Cache-Control`, the
account page may be kept, as a `200` may, and given to the next client who asks: the checker
finds it, and `SharedCache.leaks` finds it in the exchanges. Sent `no-store`, it is not kept.
-/

namespace Tests.SharedCache

open Lanes Lanes.Http.SharedCache

inductive In where
  | get (who page : Nat)
  deriving DecidableEq, Repr, Hashable

inductive Out where
  | respond (who page : Nat) (r : Http.Response)
  deriving DecidableEq, Repr, Hashable

abbrev sig : Signature where
  Id := Unit
  Msg _ := In
  In := In
  Out := Out

def request (who page : Nat) : Http.Request :=
  { method := .get, path := if page == 0 then [] else ["account"]
    headers := [("cookie", s!"session={who}")] }

/-- `private_` off seeds the bug: the account page says nothing of caches. -/
def render (private_ : Bool) (who page : Nat) : Http.Response :=
  if page == 0 then Http.Response.text "home\n" |>.withHeader "cache-control" "public, max-age=60"
  else
    let r := Http.Response.text s!"the account of {who}\n"
    if private_ then r.noStore else r

abbrev site (private_ : Bool) : System sig where
  State _ := Unit
  actor _ :=
    { init := ()
      step := fun _ msg => match msg with
        | .get who page => ((), [.emit (.respond who page (render private_ who page))])
      recover := fun _ => ((), []) }
  accept x := ⟨(), x⟩

instance : sig.Inspect := {}
instance (private_ : Bool) : (site private_).Inspect := {}

def port : Out → Option (Http.Request × Http.Response)
  | .respond who page r => some (request who page, r)

def clients : Outside sig (List (Nat × Nat)) where
  init := []
  allow d
    | .get who page => if (who, page) ∈ d ∨ 2 ≤ who ∨ 2 ≤ page then none else some ((who, page) :: d)

def pages : List (Nat × Nat) := [(0, 0), (0, 1), (1, 0), (1, 1)]

def check (private_ : Bool) :=
  Check.system (site private_)
    { driver := (clients.both (Http.SharedCache.outside port) fun _ => true).driver fun _ =>
        pages.map fun (who, page) => .get who page }
    [ .always "no client may be served a page made for another" fun w =>
        pages.all fun (who, page) =>
          (Store.serve? w.driver.2 (request who page)).all (· == render private_ who page),
      .sometimes "the home page is kept" fun w => (Store.serve? w.driver.2 (request 1 0)).isSome ]

def exchanges (private_ : Bool) : List (Http.Request × Http.Response) :=
  pages.map fun (who, page) => (request who page, render private_ who page)

def steps {S L : Type} : Option (Check.Failure S L) → Nat
  | some (.violated _ t) => t.steps.length
  | _ => 0

def tests : List (String × Bool) :=
  let buggy := check false
  let fixed := check true
  [ (s!"shared cache: an account page with no Cache-Control is served to another client "
        ++ s!"({steps buggy.failure} steps)",
      match buggy.failure with
      | some (.violated "no client may be served a page made for another" _) => true
      | _ => false),
    (s!"shared cache: sent no-store it is not kept ({fixed.states} states)", fixed.ok && fixed.complete),
    ("shared cache: the leaks check finds the first and not the second",
      (leaks (exchanges false)).length == 2 && leaks (exchanges true) == []),
    ("shared cache: private, no-store, no-cache, Vary: * and a POST are not kept; Vary: Cookie keys by the cookie",
      let ok := Http.Response.text "x"
      storable (request 0 1) ok
        && !storable (request 0 1) (ok.withHeader "Cache-Control" "private")
        && !storable (request 0 1) (ok.withHeader "cache-control" "max-age=60, no-store")
        && !storable (request 0 1) (ok.withHeader "cache-control" "no-cache")
        && !storable (request 0 1) (ok.withHeader "vary" "*")
        && !storable { request 0 1 with method := .post } ok
        && !reuses (request 0 1) (ok.withHeader "Vary" "Accept, Cookie") (request 1 1)
        && reuses (request 0 1) (ok.withHeader "Vary" "Accept, Cookie") (request 0 1)),
    ("shared cache: a redirect or a 403 is not kept unless it says so; with Authorization, only if public",
      let auth := { request 0 1 with headers := [("authorization", "Bearer t")] }
      !storable (request 0 1) (Http.Response.redirect "/")
        && storable (request 0 1) ((Http.Response.redirect "/").withHeader "cache-control" "max-age=5")
        && !storable (request 0 1) (Http.Response.text "no" 403)
        && !storable auth (Http.Response.text "x")
        && storable auth ((Http.Response.text "x").withHeader "cache-control" "public")) ]

end Tests.SharedCache
