/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-! Tests of HTML templates, rendering and HTTP request decoding. -/

namespace Tests.Html

open Lanes

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
    ("html: document adds the doctype",
      (<html></html> : Html).document == "<!DOCTYPE html><html></html>"),
    ("http: form data decodes percent escapes and plus",
      Http.parseForm "name=Ada+Lovelace&q=a%26b%3Dc&flag" ==
        [("name", "Ada Lovelace"), ("q", "a&b=c"), ("flag", "")]),
    ("http: a malformed escape is dropped, not guessed",
      Http.parseForm "a=%zz&b=1" == [("b", "1")]),
    ("http: percent decoding handles UTF-8",
      Http.percentDecode "caf%C3%A9" == some "café") ]

end Tests.Html
