# D22. Routes are values with a proof; htmx attributes come from them

`Lanes/Http/Route.lean`, `Lanes/Html/Htmx.lean`. A `Path α` is a printer and a parser with a
proof that parsing what was printed gives the value back. `Route.match?_link` follows for every
route. Views take URLs and htmx attributes from routes (`Hx.request route value`), and a
request is decoded with `Http.dispatch` over the same routes.

Why: a view that hard-codes `hx-post="/transfer"` and a decoder that matches `["transfers"]`
is a bug no type catches. With one value for both, a link to a missing route does not compile,
and `POST` to a `GET` route cannot be written.

Templ features taken: components, fragments (`<>…</>`), attribute splices (`{attrs}`),
conditional classes (`Html.classes`). Not taken: bare text children. Lean's tokenizer would
split arbitrary text into Lean tokens, so text is a string literal.

A `Path` also carries a proof that no segment it prints is empty, `.` or `..`. Those do not
survive a URL: an empty first segment makes `//host`, which a browser reads as another site, and
browsers remove dot segments however they are escaped. Free text in a path is therefore a
`Slug`, which cannot be one of them, and a number matches only in its canonical spelling.
