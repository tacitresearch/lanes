/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Videos.System
import Videos.Proofs.Shows

/-!
# A private video is its owner's alone

Only a read shows a video. Of every read and every site, an output that shows a private video
answers a request made with a session of its owner that the site let in at the read's time,
open and not past its lifetime (`Site.read_private`); a read over the members' sites sees each
member's sessions in that member's site only (`Site.union`). No output of the system shows a
video at all: in every run of it, under every environment model, every output that shows a
private video is addressed to its owner, since none does (`private_to_owner`). The bridge sends
an answer only to the connection that made the request (the gate, `Gate.step`), and a request
names a member only through a session cookie the bridge verified (tested, `Videos.EndToEnd`).
-/

set_option linter.unusedSectionVars false

namespace Videos

open Lanes

/-- An output of a read that shows a private video answers a request made with a session of its
owner that the site lets in at the read's time. -/
theorem Site.read_private (config : Config) (s : Site) (r : Read) (at_s : Nat) :
    ∀ o ∈ s.read config r at_s, ∀ c ∈ o.cards, c.visibility = .private →
      ∃ req sid r, o = .reply req (some (c.owner, sid)) r
        ∧ s.accepts config.lifetime at_s c.owner sid = true := by
  intro o ho c hc hp
  obtain ⟨w, -, rfl, -, hpriv⟩ := s.shows_read config r at_s o ho c hc
  exact hpriv hp

/-- What the system may put out: nothing that shows a video. The scheduler's attempts and
abandons show none. -/
def Shown : SchedOut ⊕ Out → Prop
  | .inl _ => True
  | .inr o => o.cards = []

/-- An output a member's actor puts out is one of the site's own, and no visit. -/
theorem emit_right {config : Config} {m : Member} {outs : List Out} {out : SchedOut ⊕ Out}
    (h : Effect.emit out ∈ (outs.map (Out.effect m)).flatMap fun eff =>
      [(Schedule.Use.wiringBy Member use).right
        (Schedule.systemBy (K := Key) (P := Unit) (A := Answer) config.scheduler Key.owner) eff]) :
    ∃ o ∈ outs, out = .inr o := by
  obtain ⟨eff, heff, h⟩ := List.mem_flatMap.mp h
  obtain ⟨o, ho, rfl⟩ := List.mem_map.mp heff
  cases o with
  | visit to v => simp [Out.effect, Wiring.right] at h
  | _ =>
    simp only [Out.effect, Wiring.right, List.mem_singleton] at h
    split at h
    · cases h
    · exact ⟨_, ho, Effect.emit.inj h⟩

theorem emits_quiet (config : Config) : (system config).Emits Shown := by
  refine ⟨fun i s msg out hout => ?_, fun i s out hout => ?_⟩
  · rcases i with e | m
    · obtain ⟨eff, -, h⟩ := List.mem_flatMap.mp hout
      cases eff <;> simp only [Wiring.left, List.mem_singleton] at h <;> try cases h
      split at h
      · cases h
      · cases h; trivial
    · obtain ⟨o, ho, rfl⟩ := emit_right hout
      have : o ∈ (handleAt config m s msg).2 := ho
      unfold handleAt at this
      split at this
      · exact Site.quiet_handle config s msg o this
      · cases this
  · rcases i with e | m
    · obtain ⟨eff, -, h⟩ := List.mem_flatMap.mp hout
      cases eff <;> simp only [Wiring.left, List.mem_singleton] at h <;> try cases h
      split at h
      · cases h
      · cases h; trivial
    · obtain ⟨o, ho, rfl⟩ := emit_right hout
      exact Site.quiet_recover s o ho

/-- A private video is its owner's alone: in every run of the system, under every environment
model, every output that shows a private video is addressed to its owner. No output shows a
video: reads do, and `Site.read_private` and `Videos.Web.view_answers` are about them. -/
theorem private_to_owner (config : Config) (env : EnvModel fullSig) {events : List (Event fullSig)}
    {c : SysState (system config)}
    (hrun : (SysState.init (system config) env).run env events = some c) :
    ∀ out : Out, Event.output (Sum.inr out) ∈ events → ∀ card ∈ out.cards, card.visibility = .private →
      out.viewer = some card.owner := by
  intro out hout card hcard
  have hq : out.cards = [] := (emits_quiet config).outputs hrun (Sum.inr out) hout
  simp [hq] at hcard

end Videos
