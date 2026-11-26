/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Semantics

/-!
How the leads-to rule is used. For a delivery, a start or an output it has three premises:
nothing restarts those, and `quiet` is filled in. For a timer it has the fourth. Built by
`lake build`, not linked into the test executable.
-/

namespace Tests.Liveness

open Lanes

variable {σ : Signature} {sys : System σ} {env : EnvModel σ} {P Q : SysState sys → Prop}

example (e : Envelope σ)
    (step : ∀ c ev c', P c → ¬Q c → c.step env ev = some c' → P c' ∨ Q c')
    (due : ∀ c, P c → ¬Q c → (Obligation.deliver e).Due env c)
    (progress : ∀ c c', P c → ¬Q c → c.step env (.deliver e) = some c' → Q c') :
    sys.LeadsTo env P Q :=
  .ensures (.deliver e) step due progress

example (i : σ.Id)
    (step : ∀ c ev c', P c → ¬Q c → c.step env ev = some c' → P c' ∨ Q c')
    (due : ∀ c, P c → ¬Q c → (Obligation.start i).Due env c)
    (progress : ∀ c c', P c → ¬Q c → c.step env (.start i) = some c' → Q c') :
    sys.LeadsTo env P Q :=
  .ensures (.start i) step due progress

example (out : σ.Out) {I : SysState sys → Prop} (hI : sys.Invariant env I)
    (step : ∀ c ev c', I c → P c → ¬Q c → c.step env ev = some c' → P c' ∨ Q c')
    (due : ∀ c, I c → P c → ¬Q c → (Obligation.output out).Due env c)
    (progress : ∀ c c', I c → P c → ¬Q c → c.step env (.output out) = some c' → Q c') :
    sys.LeadsTo env P Q :=
  .ensures_of_invariant hI (.output out) step due progress

example (i : σ.Id) (msg : σ.Msg i)
    (step : ∀ c ev c', P c → ¬Q c → c.step env ev = some c' → P c' ∨ Q c')
    (due : ∀ c, P c → ¬Q c → (Obligation.timeout i msg).Due env c)
    (progress : ∀ c c', P c → ¬Q c → c.step env (.timeout i msg) = some c' → Q c')
    (quiet : ∀ c ev c', P c → ¬Q c → c.step env ev = some c' →
      Event.timeout i msg ∈ c.arms ev → Q c') :
    sys.LeadsTo env P Q :=
  .ensures (.timeout i msg) step due progress quiet

/-- error: a step that arms this timer restarts it: give the premise `quiet` -/
#guard_msgs (substring := true) in
example (i : σ.Id) (msg : σ.Msg i)
    (step : ∀ c ev c', P c → ¬Q c → c.step env ev = some c' → P c' ∨ Q c')
    (due : ∀ c, P c → ¬Q c → (Obligation.timeout i msg).Due env c)
    (progress : ∀ c c', P c → ¬Q c → c.step env (.timeout i msg) = some c' → Q c') :
    sys.LeadsTo env P Q :=
  .ensures (.timeout i msg) step due progress

end Tests.Liveness
