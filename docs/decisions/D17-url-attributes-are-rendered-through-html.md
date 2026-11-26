# D17. URL attributes are rendered through `Html.safeUrl`

`href`, `src`, `action`, `formaction` and `xlink:href` keep relative URLs and the schemes
`http`, `https`, `mailto` and `tel`. Anything else renders as `about:invalid#blocked`. The check
is in `Attr.render`, so it covers values built without the template macro too. `<script>` and
`<style>` take no children in templates.

Why: escaping stops text becoming markup but does not stop `javascript:` in a link. Checking at
render time needs no extra types in views. The price is that `data:` and other schemes cannot be
used in those attributes yet.
