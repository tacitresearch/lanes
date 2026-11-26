/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Actors.Monotone

/-!
# Where messages and timers come from

Every message in flight is an input the system accepted or a message that some actor's step or
recovery sends, from some state; every armed timer is one that some step or recovery arms. This
is an invariant of every system in every environment (`System.traced`), so a proof by cases on
the message an actor handles cases on where it came from (`System.Sent`, `System.Armed`), and
computes what the step that sent it sends, instead of proving an invariant of its own about the
shapes of messages and timers.

## Main definitions

- `System.Sent`: the messages a system can put in flight.
- `System.Armed`: the timers a system can arm.

## Main statements

- `System.traced`: every message in flight is `Sent` and every timer `Armed`.
-/

@[expose] public section

namespace Lanes

variable {σ : Signature}

namespace System

/-- The messages a system can put in flight: an input it accepts, or what an actor's step or
recovery sends from some state. -/
inductive Sent (sys : System σ) : Envelope σ → Prop
  /-- An input, on its way to the actor that accepts it. -/
  | accept (x : σ.In) : sys.Sent ⟨none, (sys.accept x).1, (sys.accept x).2⟩
  /-- A message an actor's step sends. -/
  | step {i : σ.Id} (s : sys.State i) (msg : σ.Msg i) {e : Envelope σ} :
    e ∈ Effect.sends i ((sys.actor i).step s msg).2 → sys.Sent e
  /-- A message an actor sends as it recovers. -/
  | recover {i : σ.Id} (s : sys.State i) {e : Envelope σ} :
    e ∈ Effect.sends i ((sys.actor i).recover s).2 → sys.Sent e

/-- The timers a system can arm: those an actor's step or recovery arms from some state. -/
inductive Armed (sys : System σ) : (i : σ.Id) → σ.Msg i → Prop
  /-- A timer an actor's step arms. -/
  | step {i : σ.Id} (s : sys.State i) (msg : σ.Msg i) {delay_ms : Nat} {m : σ.Msg i} :
    .after delay_ms m ∈ ((sys.actor i).step s msg).2 → sys.Armed i m
  /-- A timer an actor arms as it recovers. -/
  | recover {i : σ.Id} (s : sys.State i) {delay_ms : Nat} {m : σ.Msg i} :
    .after delay_ms m ∈ ((sys.actor i).recover s).2 → sys.Armed i m

/-- Every message in flight is `Sent` and every timer `Armed`. -/
structure Traced (sys : System σ) (c : SysState sys) : Prop where
  /-- Every message in flight is `Sent`. -/
  net : ∀ e ∈ c.net, sys.Sent e
  /-- Every timer is `Armed`. -/
  timers : ∀ i m, m ∈ c.timers i → sys.Armed i m

/-- `Traced` is kept by every step, whatever is lost. -/
theorem Monotone.traced (sys : System σ) : sys.Monotone sys.Traced := by
  refine ((Monotone.timers sys (T := sys.Armed) (fun _ s msg _ _ h => .step s msg h)
    (fun _ s _ _ h => .recover s h)).and_net (Q := fun c => ∀ e ∈ c.net, sys.Sent e)
    (fun _ h => nomatch h) ?_ ?_ ?_).of_iff fun _ => ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  · intro c _ _ _ _ h hnet e he
    rcases hnet e he with he | ⟨x, rfl⟩
    · exact h e he
    · exact .accept x
  · intro c i msg _ _ h _ e he
    rcases List.mem_append.mp he with he | he
    · exact h e he
    · exact .step _ _ he
  · intro c i _ _ h e he
    rcases List.mem_append.mp he with he | he
    · exact h e he
    · exact .recover _ he

/-- Every message in flight is one the system accepted or an actor sent, and every timer one
an actor armed, in every environment. -/
theorem traced (sys : System σ) (env : EnvModel σ) : sys.Invariant env sys.Traced :=
  (Monotone.traced sys).invariant env

end System

end Lanes
