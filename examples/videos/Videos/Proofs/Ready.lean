/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Semantics
import Videos.Proofs.Members

/-!
# A round the worker reports ends

A report of a round, signed by the worker, leaves no video of that round transcoding: it is
ready, or failed (`Site.report_leaves`). A report goes to the actor of the owner of the video
its round names. In a fair run in which that actor is not crashed and the link from outside to
it loses nothing, it handles every such report it is sent, so a round the worker reports is over
at a later position (`report_settles`): a confirmed upload is ready or failed once an honest
worker reports, the premise that the worker eventually does being the run's input. The report
reaches the actor by `System.Run.Fair.handled_right` (D89).

Not proved: that an honest worker reports. That is the worker's, as `Lanes.Transcode` models it;
the checker checks the whole, a worker that may fail to answer or report among it
(`Videos.Check`).
-/

set_option linter.unusedSectionVars false

namespace Videos

open Lanes

theorem Report.next_settled {r : Report} {st st' : Status} (h : r.next st = some st') :
    ∀ size n, st' ≠ .transcoding size n := by
  intro size n he
  subst he
  cases st <;> cases r <;> simp [Report.next] at h

namespace Site

/-- A report of a round leaves no video of that round transcoding. -/
theorem settle_leaves (s : Site) (r : Report) :
    ∀ w ∈ (s.settle r).videos, w.id = r.round.video →
      ∀ size, w.status ≠ .transcoding size r.round.n := by
  intro w hw hid size hst
  simp only [settle, List.mem_map] at hw
  obtain ⟨w', -, rfl⟩ := hw
  rw [Report.move_id] at hid
  unfold Report.move at hst
  simp only [hid, ↓reduceIte] at hst
  split at hst
  · next st hnext => exact Report.next_settled hnext size _ hst
  · next hnone => simp [hst, Report.next] at hnone

variable (config : Config)

/-- A report signed by the worker leaves no video of its round transcoding: ready, or failed. -/
theorem report_leaves (s : Site) (req : ReqId) (r : Report) (signature : String) (at_s : Nat)
    (hsigned : r.signed config.workerKey signature = true) :
    ∀ w ∈ (s.handle config (.request (.report req r signature) at_s)).1.videos,
      w.id = r.round.video → ∀ size, w.status ≠ .transcoding size r.round.n := by
  simp only [handle, request, report, hsigned, Bool.or_true, ite_true]
  exact settle_leaves s r

end Site

theorem isStop_effect (m : Member) (outs : List Out) :
    (outs.map (Out.effect m)).any Effect.isStop = false := by
  induction outs with
  | nil => rfl
  | cons o outs ih =>
    simp only [List.map_cons, List.any_cons, ih, Bool.or_false]
    cases o <;> rfl

/-- A round the worker reports ends: in a fair run in which the actor of the owner of the
round's video is not crashed and the link from outside to it loses nothing, a report of a round
that the worker signed, sent at position `m`, is followed by a position where no video of that
round is transcoding in the owner's site: each is ready, or failed. So once an honest worker
reports a round, a confirmed upload is ready or failed, whatever the store, the schedulers and
the other inputs do. -/
theorem report_settles (config : Config) {env : EnvModel fullSig} {req : ReqId} {rep : Report}
    {signature : String} {at_s : Nat}
    (hcrash : env.mayCrash (.inr rep.round.video.owner) = false)
    (hlossless : (env.link none (.inr rep.round.video.owner)).lossy = false)
    {r : (system config).Run env} (hfair : r.Fair) {m : ℕ}
    (hsigned : rep.signed config.workerKey signature = true)
    (hinput : r.event m = some (.input (.inr (.request (.report req rep signature) at_s)))) :
    ∃ p, m < p ∧ ∀ w ∈ ((r.state p).state (.inr rep.round.video.owner) : Site).videos,
      w.id = rep.round.video → ∀ size, w.status ≠ .transcoding size rep.round.n := by
  have hstep := System.Run.step_some (r := r) hinput
  rw [SysState.step_input] at hstep
  have he : (⟨none, .inr rep.round.video.owner, Input.request (.report req rep signature) at_s⟩ :
      Envelope fullSig) ∈ (r.state (m + 1)).net := by
    rw [hstep]
    simp [Input.member, Command.member]
  obtain ⟨p, hp, hev⟩ := hfair.handled_right hlossless hcrash
    (fun s msg => by simp only [site]; exact isStop_effect _ _)
    (fun s => by simp only [site]; exact isStop_effect _ _) he
  refine ⟨p + 1, by omega, ?_⟩
  have hs : ((r.state (p + 1)).state (.inr rep.round.video.owner) : Site) =
      (((r.state p).state (.inr rep.round.video.owner) : Site).handle config
        (.request (.report req rep signature) at_s)).1 := by
    rcases hev with hev | hev
    · obtain ⟨-, -, h⟩ := SysState.step_deliver.mp (System.Run.step_some (r := r) hev)
      rw [h, SysState.handle_state]
      simp [Actor.mapEff, site, handleAt, Input.member, Command.member]
    · obtain ⟨-, -, -, h⟩ := SysState.step_duplicate.mp (System.Run.step_some (r := r) hev)
      rw [h, SysState.handle_state]
      simp [Actor.mapEff, site, handleAt, Input.member, Command.member]
  rw [hs]
  exact Site.report_leaves config _ req rep signature at_s hsigned

end Videos
