/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Videos.System
import Videos.Proofs.Shows

/-!
# A private video is its owner's alone

Of every input and every site, an output that shows a private video answers a request made with
a live session of its owner (`Site.handle_private`); a start shows nothing. The system emits only
such outputs, so in every run of it, under every environment model, every output that shows a
private video is addressed to its owner (`private_to_owner`). The bridge sends an answer only to
the connection that made the request (`Http.served`), and a request names a member only through
a session cookie the bridge verified (tested, `Videos.EndToEnd`).
-/

set_option linter.unusedSectionVars false

namespace Videos

open Lanes

/-- An output that shows a private video answers a request made with a live session of its
owner. -/
theorem Site.handle_private (config : Config) (s : Site) (i : Input) :
    ∀ o ∈ (s.handle config i).2, ∀ c ∈ o.cards, c.visibility = .private →
      ∃ req sid r, o = .reply req (some (c.owner, sid)) r ∧ s.live c.owner sid = true := by
  intro o ho c hc hp
  obtain ⟨w, -, rfl, -, hpriv⟩ := s.shows_handle config i o ho c hc
  exact hpriv hp

theorem Out.private_ok_of_shows {s : Site} {o : Out} (h : s.Shows o) : o.private_ok := by
  intro c hc hp
  obtain ⟨w, -, rfl, -, hpriv⟩ := h c hc
  obtain ⟨req, sid, r, rfl, -⟩ := hpriv hp
  rfl

theorem emits_private (config : Config) : (system config).Emits Out.private_ok := by
  refine ⟨fun _ s i out hout => ?_, fun _ s out hout => ?_⟩
  · have : out ∈ (s.handle config i).2 := by simpa [site] using hout
    exact Out.private_ok_of_shows (s.shows_handle config i out this)
  · have : out ∈ (s.recover config).2 := by simpa [site] using hout
    exact Out.private_ok_of_shows (s.shows_recover config out this)

/-- A private video is its owner's alone: in every run of the system, under every environment
model, every output that shows a private video is addressed to its owner. -/
theorem private_to_owner (config : Config) (env : EnvModel sig) {events : List (Event sig)}
    {c : SysState (system config)}
    (hrun : (SysState.init (system config) env).run env events = some c) :
    ∀ out, Event.output out ∈ events → ∀ card ∈ out.cards, card.visibility = .private →
      out.viewer = some card.owner :=
  fun out hout => (emits_private config).outputs hrun out hout

end Videos
