/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Core.Run

/-!
# The messages on one link, in order

A protocol that rests on an ordered link reads what is on it as a list: the messages from one
sender to one receiver, oldest first (`linkMsgs`). This file says what each event does to that
list: a send adds at the end, delivering the oldest on an ordered link takes the head, a loss
takes out the first copy of a message, and a crash of the receiver empties the link unless it
is lossy. A simulation can then state what it reads of a link as an equation about that list.

## Main definitions

- `Envelope.on`: the message an envelope carries on a link, if it is on that link.
- `linkMsgs`: the messages on a link, oldest first.

## Main statements

- `linkMsgs_of_deliverable`: the message delivered on an ordered link is the head of its list.
- `linkMsgs_erase_self`: losing a message takes its first copy out of the list.
- `linkMsgs_down`: a crash of the receiver empties a link that does not lose.
-/

@[expose] public section

namespace Lanes

variable {σ : Signature}

/-- The message `e` carries on the link from `src` to `dst`, if it is on that link. -/
def Envelope.on (src : Option σ.Id) (dst : σ.Id) (e : Envelope σ) : Option (σ.Msg dst) :=
  if h : e.src = src ∧ e.dst = dst then some (h.2 ▸ e.msg) else none

/-- The messages on the link from `src` to `dst` in `net`, oldest first. -/
def linkMsgs (src : Option σ.Id) (dst : σ.Id) (net : List (Envelope σ)) : List (σ.Msg dst) :=
  net.filterMap (Envelope.on src dst)

variable {src : Option σ.Id} {dst : σ.Id}

/-- An envelope on the link carries its message. -/
@[simp] theorem Envelope.on_self (m : σ.Msg dst) : Envelope.on src dst ⟨src, dst, m⟩ = some m := by
  simp [Envelope.on]

/-- An envelope on another link carries nothing on this one. -/
theorem Envelope.on_of_ne {e : Envelope σ} (h : ¬(e.src = src ∧ e.dst = dst)) :
    Envelope.on src dst e = none := by
  simp only [Envelope.on, h, dite_false]

/-- An envelope that carries something on the link is on it. -/
theorem Envelope.on_isSome {e : Envelope σ} (h : (Envelope.on src dst e).isSome = true) :
    e.src = src ∧ e.dst = dst := by
  unfold Envelope.on at h
  split at h
  · assumption
  · simp at h

/-- Nothing in flight, nothing on the link. -/
@[simp] theorem linkMsgs_nil : linkMsgs src dst ([] : List (Envelope σ)) = [] := rfl

/-- What is sent after `a` comes after it on the link. -/
@[simp] theorem linkMsgs_append (a b : List (Envelope σ)) :
    linkMsgs src dst (a ++ b) = linkMsgs src dst a ++ linkMsgs src dst b :=
  List.filterMap_append

/-- An envelope on the link is the oldest of its list. -/
@[simp] theorem linkMsgs_cons_self (m : σ.Msg dst) (net : List (Envelope σ)) :
    linkMsgs src dst (⟨src, dst, m⟩ :: net) = m :: linkMsgs src dst net := by
  simp [linkMsgs]

/-- An envelope on another link is not on this one. -/
@[simp] theorem linkMsgs_cons_of_ne {e : Envelope σ} (h : ¬(e.src = src ∧ e.dst = dst))
    (net : List (Envelope σ)) : linkMsgs src dst (e :: net) = linkMsgs src dst net := by
  simp [linkMsgs, Envelope.on_of_ne h]

/-- Taking a message of another link off the network leaves this one as it was. -/
theorem linkMsgs_erase_of_ne {e : Envelope σ} (h : ¬(e.src = src ∧ e.dst = dst))
    (net : List (Envelope σ)) : linkMsgs src dst (net.erase e) = linkMsgs src dst net :=
  filterMap_erase_of_none (Envelope.on_of_ne h) net

/-- Losing a message on the link takes its first copy out of the list. -/
theorem linkMsgs_erase_self (m : σ.Msg dst) (net : List (Envelope σ)) :
    linkMsgs src dst (net.erase ⟨src, dst, m⟩) = (linkMsgs src dst net).erase m := by
  induction net with
  | nil => rfl
  | cons e net ih =>
    obtain ⟨s, d, m'⟩ := e
    by_cases hl : s = src ∧ d = dst
    · obtain ⟨rfl, rfl⟩ := hl
      by_cases hm : m' = m
      · subst hm
        simp
      · rw [List.erase_cons_tail (by simpa using hm), linkMsgs_cons_self, linkMsgs_cons_self,
          List.erase_cons_tail (by simpa using hm), ih]
    · rw [List.erase_cons_tail (by simp only [beq_iff_eq, Envelope.mk.injEq]; exact fun h => hl ⟨h.1, h.2.1⟩),
        linkMsgs_cons_of_ne hl, linkMsgs_cons_of_ne hl, ih]

/-- Messages sent by another actor are not on a link from `src`. -/
theorem linkMsgs_sends_of_ne {i : σ.Id} (h : src ≠ some i) (effs : List (Effect σ i)) :
    linkMsgs src dst (Effect.sends i effs) = [] :=
  List.filterMap_eq_nil_iff.mpr fun _ he =>
    Envelope.on_of_ne fun hl => h (hl.1.symm.trans (Effect.mem_sends.mp he).1)

/-- On an ordered link the message delivered is the oldest one. -/
theorem linkMsgs_of_deliverable {sys : System σ} {env : EnvModel σ} {c : SysState sys}
    {m : σ.Msg dst} (hord : (env.link src dst).ordered = true)
    (hd : c.deliverable env ⟨src, dst, m⟩ = true) :
    linkMsgs src dst c.net = m :: linkMsgs src dst (c.net.erase ⟨src, dst, m⟩) := by
  have hfind : c.net.find? (Envelope.sameLink ⟨src, dst, m⟩) = some ⟨src, dst, m⟩ := by
    simpa [SysState.deliverable, hord] using hd
  refine filterMap_eq_cons_of_find? (fun e he => ?_) hfind (Envelope.on_self m)
  obtain ⟨hs, hd⟩ := Envelope.on_isSome he
  simp [Envelope.sameLink, hs, hd]

/-- A crash of `i` empties each link to it that does not lose, and leaves the others. -/
theorem linkMsgs_down {sys : System σ} (env : EnvModel σ) (c : SysState sys) (i : σ.Id) :
    linkMsgs src dst (c.down env i).net =
      if decide (dst ≠ i) || (env.link src dst).lossy then linkMsgs src dst c.net else [] := by
  simp only [SysState.down, linkMsgs]
  split
  · next hkeep =>
    refine filterMap_filter_of_none (fun e he => Envelope.on_of_ne fun ⟨hs, hd⟩ => ?_) _
    simp only [hs, hd, Bool.or_eq_false_iff, decide_eq_false_iff_not, Decidable.not_not] at he
    obtain ⟨rfl, hlossy⟩ := he
    simp [hlossy] at hkeep
  · next hlost =>
    refine List.filterMap_eq_nil_iff.mpr fun e he => Envelope.on_of_ne fun ⟨hs, hd⟩ => ?_
    simp only [List.mem_filter, hs, hd] at he
    exact hlost he.2

end Lanes
