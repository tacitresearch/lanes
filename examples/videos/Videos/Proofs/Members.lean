/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Videos.System
import Videos.Proofs.Run

/-!
# A member's actor runs the spec's functions

A member's actor takes an input about its member with `Site.handle`, does nothing with any other,
and starts with `Site.recover`. So what every input and start keeps of a site, every member's
actor keeps in every state it reaches (`Videos.site_invariant`), and so does the system, under
every environment model (`Videos.members_invariant`).
-/

namespace Videos

open Lanes

theorem handleAt_cases (config : Config) {m : Member} {s : Site} {i : Input} {P : Site × List Out → Prop}
    (hsame : P (s, [])) (hhandle : P (s.handle config i)) : P (handleAt config m s i) := by
  unfold handleAt
  split
  · exact hhandle
  · exact hsame

/-- What every input and start keeps of a site, a member's actor keeps. -/
theorem site_invariant (config : Config) {P : Site → Prop} (hinit : P {})
    (hstep : ∀ s i, P s → P (s.handle config i).1) (hrecover : ∀ s, P s → P s.recover.1)
    (m : Member) : (site config m).Invariant P :=
  Actor.Inductive.invariant
    { init := hinit
      step := fun s i h => by
        show P (handleAt config m s i).1
        exact handleAt_cases (P := fun r => P r.1) config h (hstep s i h)
      recover := fun s h => hrecover s h }

/-- What every input and start keeps of a site holds of every member's site, in every state of
the system under every environment model. -/
theorem members_invariant (config : Config) {P : Site → Prop} (hinit : P {})
    (hstep : ∀ s i, P s → P (s.handle config i).1) (hrecover : ∀ s, P s → P s.recover.1)
    (env : EnvModel fullSig) (m : Member) :
    (system config).Invariant env fun c => P (c.state (.inr m) : Site) :=
  System.invariant_of_actor (system config) (.inr m)
    (Actor.Invariant.mapEff _ (site_invariant config hinit hstep hrecover m)) env

end Videos
