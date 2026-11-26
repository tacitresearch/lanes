/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Examples.BankWeb

/-! Tests of HTML templates, rendering and HTTP request decoding. -/

namespace Tests.Html

open Lanes
open scoped Lanes.Html

def Row (label : String) (count : Nat) : Html :=
  <li class="row" data-count={count}>{label}</li>

def Card (title : String) (children : List Html) : Html :=
  <section class="card"><h2>{title}</h2>{children}</section>

def cart (items : List (String × Nat)) : Html :=
  <div id="cart">
    <Card title="Your cart">
      <ul>{items.map fun (label, count) => <Row label={label} count={count}/>}</ul>
    </Card>
    <button hx-post="/checkout" disabled={items.isEmpty}>"Checkout"</button>
    <br/>
  </div>

/-- Comparisons still parse next to templates: `<` followed by a space is never a tag. -/
def badge (count limit : Nat) : Html :=
  if count < limit then <span class="ok">{count}</span> else <span class="full">"full"</span>

def tests : List (String × Bool) :=
  [ ("html: elements, components, spliced lists and attributes render",
      (cart [("apple", 2)]).render ==
        "<div id=\"cart\"><section class=\"card\"><h2>Your cart</h2>"
          ++ "<ul><li class=\"row\" data-count=\"2\">apple</li></ul></section>"
          ++ "<button hx-post=\"/checkout\">Checkout</button><br></div>"),
    ("html: a true boolean attribute is a bare name",
      (cart []).render.contains "<button hx-post=\"/checkout\" disabled>"),
    ("html: text is escaped",
      (<p>{"<script>alert('x')</script> & more"}</p> : Html).render ==
        "<p>&lt;script&gt;alert(&#39;x&#39;)&lt;/script&gt; &amp; more</p>"),
    ("html: attribute values are escaped",
      (<a href={"\"><script>"}>"x"</a> : Html).render ==
        "<a href=\"&quot;&gt;&lt;script&gt;\">x</a>"),
    ("html: a tag name built at run time cannot inject markup",
      (Html.element "div><script" [] []).render == "<divscript></divscript>"),
    ("html: a comparison before a template is still a comparison",
      (badge 1 2).render == "<span class=\"ok\">1</span>"
        && (badge 2 2).render == "<span class=\"full\">full</span>"),
    ("html: a javascript: URL in a URL attribute is blocked, however it is disguised",
      (<a href={"javascript:alert(1)"}>"x"</a> : Html).render
          == "<a href=\"about:invalid#blocked\">x</a>"
        && Html.safeUrl " JaVa\tScRiPt:alert(1)" == Html.blockedUrl
        && Html.safeUrl "data:text/html,<script>" == Html.blockedUrl
        && (Html.element "form" [⟨"ACTION", some "javascript:x"⟩] []).render
          == "<form ACTION=\"about:invalid#blocked\"></form>"),
    ("html: ordinary URLs pass through URL attributes unchanged",
      ["/accounts/1?x=a:b", "https://example.org/a", "mailto:a@example.org", "#top", "a/b:c",
        "//example.org/x"].all fun url => Html.safeUrl url == url),
    ("html: a script is loaded by src and has no children",
      (<script src="/app.js"></script> : Html).render == "<script src=\"/app.js\"></script>"),
    ("html: document adds the doctype",
      (<html></html> : Html).document == "<!DOCTYPE html><html></html>"),
    ("html: a fragment renders its children with nothing around them",
      (<><b>"a"</b>"b"</>).render == "<b>a</b>b"),
    ("html: a class list keeps the names whose condition holds",
      (<a class={Html.classes [("btn", true), ("active", false), ("wide", true)]}/>).render
        == "<a class=\"btn wide\"></a>"),
    ("htmx: the attribute name and the URL both come from the route",
      let transfer : Http.Route Nat := .post ("transfer" /> .nat)
      (<form {Hx.request transfer 7} {Hx.target "#result"} {Hx.swap .outerHTML}/>).render
        == "<form hx-post=\"/transfer/7\" hx-target=\"#result\" hx-swap=\"outerHTML\"></form>"),
    ("htmx: triggers render in htmx's syntax",
      (<td {Hx.trigger [.load, .fromBody (.event "saved"), .every 5]}/>).render
        == "<td hx-trigger=\"load, saved from:body, every 5s\"></td>"),
    ("htmx: an event name cannot carry a script filter",
      (<td {Hx.trigger [.event "saved[alert(1)]", .every 0]}/>).render
        == "<td hx-trigger=\"savedalert1, every 1s\"></td>"),
    ("route: dispatch answers with the first route that matches",
      let account : Http.Route Nat := .get ("accounts" /> .nat)
      let home : Http.Route Unit := .get .root
      let handlers := [home.handle fun () _ => "home", account.handle fun n _ => s!"account {n}"]
      Http.dispatch handlers { method := .get, path := ["accounts", "3"] } == some "account 3"
        && Http.dispatch handlers { method := .get, path := [] } == some "home"
        && Http.dispatch handlers { method := .post, path := [] } == none),
    ("bank web: every request the page can make is decoded to the message it means",
      let get (path : List String) : Http.Request := { method := .get, path }
      let form : Http.Request :=
        { method := .post, path := ["transfer"], body := "src=0&dst=1&amount=10".toUTF8 }
      open Examples.BankWeb Examples.Bank in
      (match bridge.decode 7 (get ["accounts", "2"]) with
        | .ok (.balance 7 account) => account == 2
        | _ => false)
      && (match bridge.decode 8 form with
        | .ok (.transfer t) => t.req == 8 && t.src == 0 && t.dst == 1 && t.amount == 10
        | _ => false)
      && (match bridge.decode 9 (get ["accounts", "3"]) with
        | .error response => response.status == 404
        | _ => false)
      && (match bridge.decode 9 (get []) with
        | .error response => response.status == 200
        | _ => false)),
    ("bank web: the page asks for balances and posts transfers at its own routes",
      let page := Examples.BankWeb.Page.render
      page.contains "hx-get=\"/accounts/2\" hx-trigger=\"load, transferred from:body\""
        && page.contains "<form hx-post=\"/transfer\" hx-target=\"#result\">"),
    ("route: a link is matched by its own route and by no other",
      let account : Http.Route Nat := .get ("accounts" /> .nat)
      let transfer : Http.Route Unit := .post (.seg "transfer")
      let request : Http.Request := { method := .get, path := ["accounts", "42"] }
      account.link 42 == "/accounts/42" && account.match? request == some 42
        && transfer.match? request == none
        && account.match? { request with path := ["accounts", "42", "x"] } == none
        && account.match? { request with path := ["accounts", "x"] } == none
        && account.match? { request with method := .post } == none),
    ("route: a link escapes what a segment may not carry",
      let file : Http.Route Http.Slug := .get ("files" /> .slug)
      (Http.Slug.ofString? "a/b c%é~").map file.link == some "/files/a%2Fb%20c%25%C3%A9~"
        && Http.percentDecode (Http.percentEncode "a/b c%é~") == some "a/b c%é~"),
    ("route: an empty or dot segment is not a slug, so no link can name another host",
      ["", ".", ".."].all (fun s => (Http.Slug.ofString? s).isNone)
        && (Http.Route.get ("files" /> .slug)).match?
            { method := .get, path := ["files", ".."] } == none),
    ("route: a number has one spelling",
      let account : Http.Route Nat := .get ("accounts" /> .nat)
      account.match? { method := .get, path := ["accounts", "7"] } == some 7
        && account.match? { method := .get, path := ["accounts", "007"] } == none
        && account.match? { method := .get, path := ["accounts", "1_000"] } == none),
    ("http: form data decodes percent escapes and plus",
      Http.parseForm "name=Ada+Lovelace&q=a%26b%3Dc&flag" ==
        [("name", "Ada Lovelace"), ("q", "a&b=c"), ("flag", "")]),
    ("http: a malformed escape is dropped, not guessed",
      Http.parseForm "a=%zz&b=1" == [("b", "1")]),
    ("http: percent decoding handles UTF-8",
      Http.percentDecode "caf%C3%A9" == some "café") ]

end Tests.Html
