/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Core.Run

/-!
# More loss, no fewer states

`EnvModel.lossy env` is `env` with every link lossy as well. Whatever a system reaches under
`env` it reaches under `env.lossy` (`System.Reachable.lossy`): a crash or a stop then keeps the
messages it would have lost, and they are dropped one by one right after.

So what is proved for every environment may be used under one in which stopping loses nothing,
where the order in which actors stop and others send to them no longer shows.
-/

@[expose] public section

namespace Lanes

variable {σ : Signature}

def EnvModel.lossy (env : EnvModel σ) : EnvModel σ :=
  { env with link := fun src dst => { env.link src dst with lossy := true } }

end Lanes

end

public section

namespace Lanes

variable {σ : Signature} {sys : System σ} {env : EnvModel σ}

namespace SysState

private theorem run_drops (c : SysState sys) (keep : Envelope σ → Bool)
    (pre l : List (Envelope σ)) (hpre : ∀ e ∈ pre, keep e = true) :
    ({ c with net := pre ++ l } : SysState sys).run env.lossy
        ((l.filter (!keep ·)).map .drop)
      = some { c with net := pre ++ l.filter keep } := by
  induction l generalizing pre with
  | nil => simp [run]
  | cons e l ih =>
    cases he : keep e with
    | true =>
      have h := ih (pre ++ [e]) (by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hpre x hx
        · simp only [List.mem_singleton] at hx
          exact hx ▸ he)
      simpa [he, List.append_assoc] using h
    | false =>
      have hnot : e ∉ pre := fun h => by simp [hpre e h] at he
      simp only [List.filter_cons, he, Bool.not_false, ↓reduceIte, List.map_cons, run]
      rw [step_drop.mpr ⟨rfl, by simp, rfl⟩]
      simp only [Option.bind_some, List.erase_append_right _ hnot, List.erase_cons_head]
      simpa [he] using ih pre hpre

/-- Taking an actor down where nothing is lost, then dropping what would have been. -/
theorem down_lossy (c : SysState sys) (i : σ.Id) :
    ∃ drops : List (Envelope σ),
      (c.down env.lossy i).run env.lossy (drops.map .drop) = some (c.down env i) := by
  have hall : c.net.filter (fun e => decide (e.dst ≠ i) || (env.lossy.link e.src e.dst).lossy)
      = c.net := List.filter_eq_self.mpr fun e _ => by simp [EnvModel.lossy]
  have h := run_drops (env := env) { c with up := update c.up i false, timers := update c.timers i [] }
    (fun e => decide (e.dst ≠ i) || (env.link e.src e.dst).lossy) [] c.net (by simp)
  have hdown : c.down env.lossy i
      = { c with up := update c.up i false, timers := update c.timers i [] } := by
    simp only [down, hall]
  rw [hdown]
  exact ⟨_, h⟩

theorem settle_lossy (c : SysState sys) (i : σ.Id) (r : sys.State i × List (Effect σ i)) :
    ∃ drops : List (Envelope σ),
      (c.settle env.lossy i r).run env.lossy (drops.map .drop) = some (c.settle env i r) := by
  unfold settle
  split
  · exact down_lossy _ i
  · exact ⟨[], rfl⟩

/-- An actor's start does not look at the messages in flight: those dropped after it could as
well be dropped before. -/
private theorem startActor_drops (i : σ.Id) :
    ∀ (drops : List (Envelope σ)) {a c : SysState sys},
      a.run env.lossy (drops.map .drop) = some c →
      (a.startActor env.lossy i).run env.lossy (drops.map .drop)
        = some (c.startActor env.lossy i)
  | [], a, c, h => by
    simp only [List.map_nil, run, Option.some.injEq] at h ⊢
    rw [h]
  | d :: drops, a, c, h => by
    simp only [List.map_cons, run] at h ⊢
    cases hstep : a.step env.lossy (.drop d) with
    | none => simp [hstep] at h
    | some a₁ =>
      obtain ⟨hlossy, hmem, rfl⟩ := step_drop.mp hstep
      obtain ⟨hkept, heq⟩ := settle_erase (env := env.lossy) { a with up := update a.up i true } i
        ((sys.actor i).recover (a.state i)) hmem hlossy
      have hstep' : (a.startActor env.lossy i).step env.lossy (.drop d)
          = some (({ a with net := a.net.erase d } : SysState sys).startActor env.lossy i) :=
        step_drop.mpr ⟨hlossy, hkept, heq⟩
      rw [hstep']
      exact startActor_drops i drops (by simpa [hstep] using h)

theorem init_lossy (sys : System σ) (env : EnvModel σ) :
    ∃ drops : List (Envelope σ),
      (init sys env.lossy).run env.lossy (drops.map .drop) = some (init sys env) := by
  suffices h : ∀ (l : List σ.Id) (a c : SysState sys) (drops : List (Envelope σ)),
      a.run env.lossy (drops.map .drop) = some c →
      ∃ drops' : List (Envelope σ),
        (l.foldl (fun c i => c.startActor env.lossy i) a).run env.lossy (drops'.map .drop)
          = some (l.foldl (fun c i => c.startActor env i) c) from h sys.boot _ _ [] rfl
  intro l
  induction l with
  | nil => exact fun a c drops h => ⟨drops, h⟩
  | cons i l ih =>
    intro a c drops h
    obtain ⟨more, hmore⟩ := settle_lossy (env := env) { c with up := update c.up i true } i
      ((sys.actor i).recover (c.state i))
    exact ih _ _ (drops ++ more) (by
      rw [List.map_append, run_append, startActor_drops i drops h]
      exact hmore)

/-- One event without the extra loss is the same event with it, then drops. -/
theorem step_lossy {c c' : SysState sys} {ev : Event σ} (h : c.step env ev = some c') :
    ∃ drops : List (Envelope σ), c.run env.lossy (ev :: drops.map .drop) = some c' := by
  have after : ∀ {x x' : SysState sys}, c.step env.lossy ev = some x →
      (∃ drops : List (Envelope σ), x.run env.lossy (drops.map .drop) = some x') →
      ∃ drops : List (Envelope σ), c.run env.lossy (ev :: drops.map .drop) = some x' := by
    rintro x x' hx ⟨drops, hrun⟩
    exact ⟨drops, by simp [run, hx, hrun]⟩
  cases ev with
  | input x =>
    obtain rfl := step_input.mp h
    exact after (step_input.mpr rfl) ⟨[], rfl⟩
  | deliver e =>
    obtain ⟨hup, hdel, rfl⟩ := step_deliver.mp h
    exact after (step_deliver.mpr ⟨hup, hdel, rfl⟩) (settle_lossy _ _ _)
  | duplicate e =>
    obtain ⟨hup, hdup, hdel, rfl⟩ := step_duplicate.mp h
    exact after (step_duplicate.mpr ⟨hup, hdup, hdel, rfl⟩) (settle_lossy _ _ _)
  | drop e =>
    obtain ⟨_, hmem, rfl⟩ := step_drop.mp h
    exact after (step_drop.mpr ⟨rfl, hmem, rfl⟩) ⟨[], rfl⟩
  | timeout i msg =>
    obtain ⟨hup, hmem, rfl⟩ := step_timeout.mp h
    exact after (step_timeout.mpr ⟨hup, hmem, rfl⟩) (settle_lossy _ _ _)
  | output out =>
    obtain ⟨hmem, rfl⟩ := step_output.mp h
    exact after (step_output.mpr ⟨hmem, rfl⟩) ⟨[], rfl⟩
  | crash i =>
    obtain ⟨hup, hcrash, rfl⟩ := step_crash.mp h
    exact after (step_crash.mpr ⟨hup, hcrash, rfl⟩) (down_lossy c i)
  | start i =>
    obtain ⟨hup, hmail, rfl⟩ := step_start.mp h
    exact after (step_start.mpr ⟨hup, hmail, rfl⟩) (settle_lossy _ _ _)
  | restart =>
    obtain ⟨hmay, rfl⟩ := step_restart.mp h
    exact after (step_restart.mpr ⟨hmay, rfl⟩) (init_lossy sys env)

end SysState

/-- Whatever a system reaches, it reaches when every link may also lose messages. -/
theorem System.Reachable.lossy {c : SysState sys} (h : sys.Reachable env c) :
    sys.Reachable env.lossy c := by
  induction h with
  | init =>
    obtain ⟨drops, hrun⟩ := SysState.init_lossy sys env
    exact System.Reachable.init.run hrun
  | step ev _ hstep ih =>
    obtain ⟨drops, hrun⟩ := SysState.step_lossy hstep
    exact ih.run hrun

end Lanes
