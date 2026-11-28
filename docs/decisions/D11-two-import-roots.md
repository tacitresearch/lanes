# D11. Two import roots: `Lanes` and `Lanes.Semantics`

Status: Accepted

`import Lanes` is the runtime layer (Std only). `import Lanes.Semantics` adds the proof layer
(CSLib, Mathlib). Executable code imports the first; proof files import the second.

Why: measured. A test binary that imported the proof layer was 157 MB; the same binary on the
runtime layer is 8 MB. Mathlib also defines the token `<i`, which breaks `<input>` in templates.
`lanes lint` enforces the split (`layering`).

*Still open:* an app that never proves anything still downloads Mathlib, because Lanes is one
package. DESIGN accepts that cost ("a download, not hours of compiling"). If it hurts adoption,
the fix is a second package for the proof layer, which is a packaging change only.
