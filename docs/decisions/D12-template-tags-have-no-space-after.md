# D12. Template tags have no space after `<`

Status: Accepted

`<div>` is a tag; `a < b` is a comparison. The grammar requires the tag name to follow `<`
directly.

Why: found by building the generated app. Without the rule, `if count < limit then (…)` in any
file importing Lanes parsed `<limit then` as the start of a tag and failed.

*Since extended:* the syntax is scoped (`open scoped Lanes.Html`), so files that are not views
are unaffected, including `a<b` written without spaces.
