/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Videos.System
import Videos.Proofs.Shows

/-!
# A private video is its owner's alone

Of every input and every site, an output that shows a private video answers a request made with
a session of its owner that let it in when it arrived, open and not past its lifetime
(`Site.handle_private`); a start shows nothing. The site beside its scheduler emits only such
outputs, so in every run of the two, under every environment model, every output that shows a
private video is addressed to its owner (`private_to_owner`). The bridge sends an answer only to
the connection that made the request (the gate, `Gate.step`), and a request names a member only through
a session cookie the bridge verified (tested, `Videos.EndToEnd`).
-/

set_option linter.unusedSectionVars false

namespace Videos

open Lanes

/-- An output that shows a private video answers a request made with a session of its owner
that let the request in when it arrived. -/
theorem Site.handle_private (config : Config) (s : Site) (i : Input) :
    ∀ o ∈ (s.handle config i).2, ∀ c ∈ o.cards, c.visibility = .private →
      ∃ req sid r, o = .reply req (some (c.owner, sid)) r
        ∧ s.accepts config.lifetime i.at_s c.owner sid = true := by
  intro o ho c hc hp
  obtain ⟨w, -, rfl, -, hpriv⟩ := s.shows_handle config i o ho c hc
  exact hpriv hp

theorem Out.private_ok_of_shows {s : Site} {life : Auth.Lifetime} {at_s : Nat} {o : Out}
    (h : s.Shows life at_s o) : o.private_ok := by
  intro c hc hp
  obtain ⟨w, -, rfl, -, hpriv⟩ := h c hc
  obtain ⟨req, sid, r, rfl, -⟩ := hpriv hp
  rfl

/-- What the system may put out: an answer that shows a private video only to its owner. The
scheduler's attempts and abandons show no video. -/
def Shown : SchedOut ⊕ Out → Prop
  | .inl _ => True
  | .inr o => o.private_ok

/-- An output the site's actor puts out beside the scheduler is one of the site's own. -/
theorem emit_right {config : Config} {effs : List (Effect sig ())} {out : SchedOut ⊕ Out}
    (h : Effect.emit out ∈ effs.flatMap fun eff =>
      [use.wiring.right (Schedule.system (K := Key) (P := Unit) (A := Answer) config.scheduler) eff]) :
    ∃ o, Effect.emit o ∈ effs ∧ out = .inr o := by
  obtain ⟨eff, heff, h⟩ := List.mem_flatMap.mp h
  cases eff with
  | emit o =>
    simp only [Wiring.right, List.mem_singleton] at h
    split at h
    · cases h
    · exact ⟨o, heff, Effect.emit.inj h⟩
  | _ => simp [Wiring.right] at h

theorem emits_private (config : Config) : (system config).Emits Shown := by
  refine ⟨fun i s msg out hout => ?_, fun i s out hout => ?_⟩
  · rcases i with ⟨⟩ | ⟨⟩
    · obtain ⟨eff, -, h⟩ := List.mem_flatMap.mp hout
      cases eff <;> simp only [Wiring.left, List.mem_singleton] at h <;> try cases h
      split at h
      · cases h
      · cases h; trivial
    · obtain ⟨o, ho, rfl⟩ := emit_right hout
      have : o ∈ (s.handle config msg).2 := by simpa [site] using ho
      exact Out.private_ok_of_shows (s.shows_handle config msg o this)
  · rcases i with ⟨⟩ | ⟨⟩
    · obtain ⟨eff, heff, h⟩ := List.mem_flatMap.mp hout
      cases eff <;> simp only [Wiring.left, List.mem_singleton] at h <;> try cases h
      split at h
      · cases h
      · cases h; trivial
    · obtain ⟨o, ho, rfl⟩ := emit_right hout
      have : o ∈ s.recover.2 := by simpa [site] using ho
      exact Out.private_ok_of_shows (s.shows_recover config 0 o this)

/-- A private video is its owner's alone: in every run of the site and its scheduler, under
every environment model, every output that shows a private video is addressed to its owner. -/
theorem private_to_owner (config : Config) (env : EnvModel fullSig) {events : List (Event fullSig)}
    {c : SysState (system config)}
    (hrun : (SysState.init (system config) env).run env events = some c) :
    ∀ out : Out, Event.output (Sum.inr out) ∈ events → ∀ card ∈ out.cards, card.visibility = .private →
      out.viewer = some card.owner :=
  fun out hout => (emits_private config).outputs hrun (Sum.inr out) hout

end Videos
