/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Semantics
import Examples.KV

/-!
# The store behind its front ends is a map

Without caching, for all keys, values and front ends, the system implements its five-line spec
in every environment whose links do not hand a message over twice (`implements`): messages may
be lost and reordered and actors may crash. `Tests/KV.lean` checks that each link the system
uses must not duplicate: every handling of a message answers a client or sends on.

The simulation (`Sim`) reads the store's data as the spec's value. A request is pending in the
spec while it is on its way to a front end or from a front end to the store (`pend`), and the
answer to a read is owed in the spec's outbox while it is on its way back (`owed`). Both are
bounds, not equalities: a message lost stays pending or owed in the spec for ever, which the spec
allows. A request takes effect when the store handles it.

With caching the system does not implement the spec in any environment, for any instance with a
key, a value and a front end (`caching_not_implements`): the run the checker finds, a read
served from the cache after an acknowledged write, is a run of every such instance.
-/

namespace Examples.KV

open Lanes

variable {K V F : Type} [DecidableEq K] [DecidableEq V] [DecidableEq F]

def sender : Option (Id F) → Option F
  | some (.front f) => some f
  | _ => none

def pend : Envelope (sig K V F) → Option (Request K V F)
  | ⟨_, .front f, .request r⟩ => some ⟨r.req, f, r.op⟩
  | ⟨src, .store, .put req key value⟩ => (sender src).map fun f => ⟨req, f, .put key value⟩
  | ⟨_, .store, .get req key replyTo⟩ => some ⟨req, replyTo, .get key⟩
  | _ => none

def owed : Envelope (sig K V F) → Option (Response V)
  | ⟨_, .front _, .got req _ value⟩ => some ⟨req, .value value⟩
  | _ => none

/-- No timer is armed, and what goes to the store comes from a front end. -/
def Tame (c : SysState (system K V F false)) : Prop :=
  (∀ i m, m ∈ c.timers i → False) ∧ ∀ e ∈ c.net, e.dst = .store → ∃ f, e.src = some (.front f)

theorem tame_invariant (env : EnvModel (sig K V F)) :
    (system K V F false).Invariant env Tame := by
  have htimers := System.Monotone.timers (system K V F false) (T := fun _ _ => False)
    (fun i s msg delay m h => by
      cases i <;> cases msg <;> simp [system, front, store] at h; split at h <;> simp at h)
    (fun i s delay m h => by cases i <;> simp [system, front, store] at h)
  refine (htimers.and_net (Q := fun c : SysState (system K V F false) =>
    ∀ e ∈ c.net, e.dst = Id.store → ∃ f, e.src = some (Id.front f))
    (fun _ h => nomatch h) ?_ ?_ ?_).invariant env
  · intro c up net timers outbox h hnet e he hdst
    rcases hnet e he with he | ⟨x, rfl⟩
    · exact h e he hdst
    · cases hdst
  · intro c i msg _ _ h _ e he hdst
    rcases SysState.mem_grow_net.mp he with he | ⟨hsrc, he⟩
    · exact h e he hdst
    · obtain ⟨src, dst, m⟩ := e
      cases hdst
      cases i with
      | front f => exact ⟨f, hsrc⟩
      | store => cases msg <;> simp [system, store] at he
  · intro c i _ _ h e he hdst
    rcases SysState.mem_grow_net.mp he with he | ⟨_, he⟩
    · exact h e he hdst
    · cases i <;> simp [system, front, store] at he

abbrev Abs (K V F : Type) [DecidableEq K] [DecidableEq V] [DecidableEq F] :=
  Service.Abs (sig K V F) (K → Option V)

structure Sim (c : SysState (system K V F false)) (t : Abs K V F) : Prop where
  value : t.value = c.state .store
  pending : (↑(c.net.filterMap pend) : Multiset (Request K V F)) ≤ t.pending
  outbox : (↑c.outbox : Multiset (Response V)) + ↑(c.net.filterMap owed) ≤ t.outbox

namespace Sim

variable {c c' : SysState (system K V F false)} {t : Abs K V F}

theorem mono (h : Sim c t) (hvalue : c'.state .store = c.state .store)
    (hpending : (↑(c'.net.filterMap pend) : Multiset (Request K V F)) ≤ ↑(c.net.filterMap pend))
    (houtbox : (↑c'.outbox : Multiset (Response V)) + ↑(c'.net.filterMap owed) ≤
      ↑c.outbox + ↑(c.net.filterMap owed)) : Sim c' t :=
  ⟨h.value.trans hvalue.symm, hpending.trans h.pending, houtbox.trans h.outbox⟩

theorem loses (h : Sim c t) (hl : c'.Loses c) : Sim c' t :=
  h.mono (by rw [hl.state]) (Multiset.coe_le.mpr (hl.net.filterMap _).subperm)
    (by rw [hl.outbox]; exact add_le_add_right (Multiset.coe_le.mpr (hl.net.filterMap _).subperm) _)

/-- A front end handles `e`: what it sends and emits is what `e` was on its way to do. -/
theorem forward (h : Sim c t) {e : Envelope (sig K V F)} (he : e ∈ c.net)
    {sent : List (Envelope (sig K V F))} {emitted : List (Response V)}
    (hvalue : c'.state .store = c.state .store) (hnet : c'.net = c.net.erase e ++ sent)
    (hout : c'.outbox = c.outbox ++ emitted) (hpend : sent.filterMap pend = (pend e).toList)
    (howed : emitted ++ sent.filterMap owed = (owed e).toList) : Sim c' t := by
  refine h.mono hvalue (le_of_eq ?_) (le_of_eq ?_)
  · rw [hnet, Multiset.coe_eq_coe.mpr (filterMap_perm_erase he), List.filterMap_append, hpend]
    exact Multiset.coe_eq_coe.mpr List.perm_append_comm
  · rw [hout, hnet, Multiset.coe_eq_coe.mpr (filterMap_perm_erase he), ← howed]
    simp only [List.filterMap_append, ← Multiset.coe_add]
    abel

/-- The store handles `e`, which is `x` taking effect. -/
theorem take (h : Sim c t) {e : Envelope (sig K V F)} (he : e ∈ c.net) {x : Request K V F}
    {sent : List (Envelope (sig K V F))} {emitted : List (Response V)} (hx : pend e = some x)
    (hnone : owed e = none)
    (hvalue : c'.state .store = ((spec K V F).step (c.state .store) x).1)
    (hnet : c'.net = c.net.erase e ++ sent) (hout : c'.outbox = c.outbox ++ emitted)
    (hpend : sent.filterMap pend = [])
    (howed : emitted ++ sent.filterMap owed = ((spec K V F).step (c.state .store) x).2) :
    ∃ t', (spec K V F).spec.lts.τSTr t t' ∧ Sim c' t' := by
  have hle : x ::ₘ (↑(c'.net.filterMap pend) : Multiset (Request K V F)) ≤ t.pending := by
    have := h.pending
    rw [Multiset.coe_eq_coe.mpr (filterMap_perm_erase he), hx] at this
    rw [hnet, List.filterMap_append, hpend, List.append_nil]
    simpa using this
  refine ⟨⟨((spec K V F).step t.value x).1, t.pending.erase x,
    t.outbox + ((spec K V F).step t.value x).2⟩,
    .single ⟨x, Multiset.mem_of_le hle (Multiset.mem_cons_self _ _), rfl⟩, ?_, ?_, ?_⟩
  · rw [hvalue, h.value]
  · simpa using Multiset.erase_le_erase x hle
  · have := h.outbox
    rw [Multiset.coe_eq_coe.mpr (filterMap_perm_erase he), hnone] at this
    rw [hout, hnet, h.value, ← howed]
    simp only [List.filterMap_append, ← Multiset.coe_add]
    calc _ = (↑c.outbox + ↑((c.net.erase e).filterMap owed)) +
          ((↑emitted : Multiset (Response V)) + ↑(sent.filterMap owed)) := by abel
      _ ≤ _ := add_le_add_left (by simpa using this) _

end Sim

theorem implements (env : EnvModel (sig K V F))
    (henv : ∀ src dst, (env.link src dst).duplicating = false) :
    (system K V F false).Implements env (spec K V F) := by
  refine System.Refines.of_steps (tame_invariant env) Sim
    ⟨⟨fun _ => none, 0, 0⟩, rfl, rfl, by simp [SysState.init, SysState.blank],
      by simp [SysState.init, SysState.blank]⟩ (fun _ _ _ h hl => h.loses hl)
    ?_ ?_ ?_ ?_ ?_ ?_
  · intro c t x _ h
    refine ⟨{ t with pending := x ::ₘ t.pending }, .single rfl, h.value, ?_, ?_⟩
    · show (↑((c.net ++ [(⟨none, .front x.via, .request x⟩ : Envelope (sig K V F))]).filterMap
        pend) : Multiset (Request K V F)) ≤ _
      rw [filterMap_concat, ← Multiset.coe_add]
      simpa [add_comm, pend] using Multiset.cons_le_cons x h.pending
    · show _ + (↑((c.net ++ [(⟨none, .front x.via, .request x⟩ : Envelope (sig K V F))]).filterMap
        owed) : Multiset (Response V)) ≤ _
      rw [filterMap_concat]
      simpa [owed] using h.outbox
  · intro c t out _ h hmem
    have hin : out ∈ t.outbox :=
      Multiset.mem_of_le h.outbox (Multiset.mem_add.mpr (.inl (Multiset.mem_coe.mpr hmem)))
    refine ⟨{ t with outbox := t.outbox.erase out }, .single ⟨hin, rfl⟩, h.value, h.pending, ?_⟩
    have := Multiset.erase_le_erase out h.outbox
    rwa [Multiset.erase_add_left_pos _ (Multiset.mem_coe.mpr hmem), Multiset.coe_erase] at this
  · rintro c t ⟨src, dst, msg⟩ ⟨_, hstore⟩ h hmem
    cases dst with
    | front f =>
      cases msg with
      | request r =>
        obtain ⟨req, via, op⟩ := r
        cases op <;> exact ⟨t, .refl, h.forward hmem (by simp) rfl rfl rfl rfl⟩
      | got req key value => exact ⟨t, .refl, h.forward hmem (by simp) rfl rfl rfl rfl⟩
    | store =>
      cases msg with
      | put req key value =>
        obtain ⟨f, rfl⟩ := hstore _ hmem rfl
        exact h.take hmem (x := ⟨req, f, .put key value⟩) rfl rfl (by simp; rfl) rfl rfl rfl rfl
      | get req key replyTo =>
        exact h.take hmem (x := ⟨req, replyTo, .get key⟩) rfl rfl (by simp; rfl) rfl rfl rfl rfl
  · intro c t e _ _ _ hdup
    simp [henv] at hdup
  · intro c t i msg ⟨htimers, _⟩ _ hmem
    exact (htimers i msg hmem).elim
  · intro c t i _ h
    refine ⟨t, .refl, h.mono ?_ ?_ ?_⟩ <;> cases i <;>
      simp [SysState.grow, system, front, store, Effect.sends, Effect.emits]

/-! ## Caching -/

section Stale

variable (k : K) (v : V) (f : F)

/-- Only the first read has arrived. -/
def Read (a : Abs K V F) : Prop :=
  (∀ x ∈ a.pending, x = ⟨1, f, .get k⟩) ∧ ∀ o ∈ a.outbox, o.req = 1

/-- The write has arrived too; once it is acknowledged it has taken effect. -/
def Written (a : Abs K V F) : Prop :=
  (∀ x ∈ a.pending, x = ⟨1, f, .get k⟩ ∨ x = ⟨2, f, .put k v⟩) ∧
    a.pending.count ⟨2, f, .put k v⟩ ≤ 1 ∧
    ∀ o ∈ a.outbox, o.req = 1 ∨ (o.req = 2 ∧ ⟨2, f, .put k v⟩ ∉ a.pending ∧ a.value k = some v)

/-- The write has taken effect and only reads are left: the second read can only see it. -/
def Seen (a : Abs K V F) : Prop :=
  a.value k = some v ∧ (∀ x ∈ a.pending, x = ⟨1, f, .get k⟩ ∨ x = ⟨3, f, .get k⟩) ∧
    ∀ o ∈ a.outbox, o.req = 3 → o.res = .value (some v)

theorem read_stable : (spec K V F).Stable (Read k f) := by
  rintro a x hx ⟨hpending, houtbox⟩
  obtain rfl := hpending x hx
  refine ⟨fun y hy => hpending y (Multiset.mem_of_mem_erase hy), fun o ho => ?_⟩
  rcases Multiset.mem_add.mp ho with ho | ho
  · exact houtbox o ho
  · simp_all [spec]

theorem written_stable : (spec K V F).Stable (Written k v f) := by
  rintro a x hx ⟨hpending, hcount, houtbox⟩
  refine ⟨fun y hy => hpending y (Multiset.mem_of_mem_erase hy),
    (Multiset.count_le_of_le _ (Multiset.erase_le _ _)).trans hcount, ?_⟩
  rcases hpending x hx with rfl | rfl
  · intro o ho
    rcases Multiset.mem_add.mp ho with ho | ho
    · exact (houtbox o ho).imp_right fun ⟨hreq, hnot, hvalue⟩ =>
        ⟨hreq, fun h => hnot (Multiset.mem_of_mem_erase h), hvalue⟩
    · simp_all [spec]
  · have hgone : (⟨2, f, .put k v⟩ : Request K V F) ∉ a.pending.erase ⟨2, f, .put k v⟩ := by
      rw [← Multiset.count_eq_zero, Multiset.count_erase_self]
      omega
    intro o ho
    rcases Multiset.mem_add.mp ho with ho | ho
    · exact (houtbox o ho).imp_right fun ⟨hreq, _, _⟩ => ⟨hreq, hgone, by simp [spec]⟩
    · simp_all [spec]

theorem seen_stable : (spec K V F).Stable (Seen k v f) := by
  rintro a x hx ⟨hvalue, hpending, houtbox⟩
  refine ⟨?_, fun y hy => hpending y (Multiset.mem_of_mem_erase hy), fun o ho => ?_⟩
  · rcases hpending x hx with rfl | rfl <;> exact hvalue
  · rcases Multiset.mem_add.mp ho with ho | ho
    · exact houtbox o ho
    · rcases hpending x hx with rfl | rfl <;> simp_all [spec]

/-- The map spec does not allow the stale read: after the write is acknowledged, a read that
arrives later sees it. -/
theorem stale_not_trace {a : Abs K V F} :
    ¬ (spec K V F).spec.lts.SMTr ⟨fun _ => none, 0, 0⟩
      (((staleRead k v f).filterMap Event.visible).map some) a := by
  intro h
  obtain _ | ⟨h₁, _ | ⟨h₂, _ | ⟨h₃, _ | ⟨h₄, _ | ⟨h₅, -⟩⟩⟩⟩⟩ := h
  have hfalse : (spec K V F).Stable fun _ => False := fun _ _ _ h => h
  have hstart : (spec K V F).Stable fun a : Abs K V F => a.pending = 0 ∧ a.outbox = 0 :=
    fun a x hx h => by simp [h.1] at hx
  refine (seen_stable k v f).sTr hfalse ?_ h₅ ?_
  · rintro a b ⟨-, -, houtbox⟩ ⟨hmem, -⟩
    simpa using houtbox _ hmem rfl
  refine (seen_stable k v f).sTr (seen_stable k v f) ?_ h₄ ?_
  · rintro a b ⟨hvalue, hpending, houtbox⟩ rfl
    refine ⟨hvalue, fun x hx => ?_, houtbox⟩
    rcases Multiset.mem_cons.mp hx with rfl | hx
    · exact .inr rfl
    · exact hpending x hx
  refine (written_stable k v f).sTr (seen_stable k v f) ?_ h₃ ?_
  · rintro a b ⟨hpending, -, houtbox⟩ ⟨hmem, rfl⟩
    obtain ⟨-, hgone, hvalue⟩ := (houtbox _ hmem).resolve_left (by simp)
    refine ⟨hvalue, fun x hx => ?_, fun o ho hreq => ?_⟩
    · rcases hpending x hx with rfl | rfl
      · exact .inl rfl
      · exact absurd hx hgone
    · rcases houtbox o (Multiset.mem_of_mem_erase ho) with h | ⟨h, -⟩ <;> simp [hreq] at h
  refine (read_stable k f).sTr (written_stable k v f) ?_ h₂ ?_
  · rintro a b ⟨hpending, houtbox⟩ rfl
    have hnot : (⟨2, f, .put k v⟩ : Request K V F) ∉ a.pending := fun h => by
      simpa using hpending _ h
    refine ⟨fun x hx => ?_, by simp [Multiset.count_eq_zero_of_notMem hnot], fun o ho => ?_⟩
    · rcases Multiset.mem_cons.mp hx with rfl | hx
      · exact .inr rfl
      · exact .inl (hpending x hx)
    · exact .inl (houtbox o ho)
  refine hstart.sTr (read_stable k f) ?_ h₁ ⟨rfl, rfl⟩
  rintro a b ⟨hpending, houtbox⟩ rfl
  exact ⟨by simp [hpending], by simp [houtbox]⟩

theorem staleRead_runs (env : EnvModel (sig K V F)) :
    ∃ c, (SysState.init (system K V F true) env).run env (staleRead k v f) = some c := by
  simp [staleRead, SysState.run, SysState.step, SysState.init, SysState.blank,
    SysState.deliverable, SysState.hasMail, SysState.startActor, SysState.handle,
    SysState.settle_eq, system, front, store, Envelope.sameLink, Effect.isStop, Effect.sends,
    Effect.emits, Effect.retime, update]

end Stale

theorem caching_not_implements (env : EnvModel (sig K V F)) (k : K) (v : V) (f : F) :
    ¬ (system K V F true).Implements env (spec K V F) := fun h => by
  obtain ⟨c, hrun⟩ := staleRead_runs k v f env
  obtain ⟨_, a, rfl, htrace⟩ := System.Refines.traces_of_run h hrun
  exact stale_not_trace k v f htrace

end Examples.KV
