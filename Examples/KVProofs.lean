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

The simulation is the standard one (`Lanes.Account`): the store's data is the spec's value, a
request is pending in the spec while it is on its way to a front end or from a front end to the
store (`pend`), and the answer to a read is owed while it is on its way back (`owed`). A front
end passes on what it was handed (`Moves.forward`); a request takes effect when the store
handles it (`Moves.take`).

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
  Service.Abs (Request K V F) (Response V) (K → Option V)

def account : Account (system K V F false) (K → Option V) Unit where
  pend := pend
  owe := owed
  value state _ _ v := v = state .store

theorem implements (env : EnvModel (sig K V F))
    (henv : ∀ src dst, (env.link src dst).duplicating = false) :
    (system K V F false).Implements env (spec K V F) := by
  refine account.implements (tame_invariant env)
    ⟨(), rfl, by simp [Account.pending, SysState.init, SysState.blank, account],
      by simp [Account.owed, SysState.init, SysState.blank, account]⟩
    (fun _ => ⟨rfl, rfl⟩) (fun _ _ _ _ _ h => h) ?_ (fun _ _ _ _ hdup => by simp [henv] at hdup)
    (fun _ _ _ _ _ => .of_loses ⟨rfl, List.erase_sublist, fun _ _ h => h, rfl⟩ fun _ _ h => h)
    (fun c i _ => .of_loses (SysState.Loses.down env c i) fun _ _ h => h)
    (fun _ i msg ⟨htimers, _⟩ hmem => (htimers i msg hmem).elim)
    (fun _ i _ => by cases i <;> exact .quiet (fun _ _ h => by simpa [account] using h) rfl rfl)
  rintro c ⟨src, dst, msg⟩ ⟨_, hstore⟩ hd
  have hmem := SysState.mem_of_deliverable hd
  cases dst with
  | front f =>
    cases msg with
    | request r =>
      obtain ⟨req, via, op⟩ := r
      cases op <;> exact .forward hmem (fun _ _ h => by simpa [account] using h) rfl rfl
    | got req key value => exact .forward hmem (fun _ _ h => by simpa [account] using h) rfl rfl
  | store =>
    cases msg with
    | put req key value =>
      obtain ⟨f, rfl⟩ := hstore _ hmem rfl
      exact .take hmem (x := ⟨req, f, .put key value⟩) rfl rfl
        (fun _ _ h => by subst h; simp [account]; rfl) rfl fun _ _ _ => rfl
    | get req key replyTo =>
      exact .take hmem (x := ⟨req, replyTo, .get key⟩) rfl rfl
        (fun _ _ h => by subst h; simp [account]; rfl) rfl fun _ _ h => by subst h; rfl

/-! ## Caching -/

section Stale

variable (k : K) (v : V) (f : F)

/-- Only the first read has arrived. -/
def Read : Abs K V F → Prop :=
  Service.Only (· = ⟨1, f, .get k⟩) (fun _ => True) (·.req = 1)

/-- The write has arrived too; once it is answered it has taken effect. -/
def Written (a : Abs K V F) : Prop :=
  Service.Only (fun x => x = ⟨1, f, .get k⟩ ∨ x = ⟨2, f, .put k v⟩) (fun _ => True)
    (fun o => o.req = 1 ∨ o.req = 2) a ∧
  Service.Took Request.req Response.req ⟨2, f, .put k v⟩ (· k = some v) a

/-- The write has taken effect and only reads are left: the second read can only see it. -/
def Seen : Abs K V F → Prop :=
  Service.Only (fun x => x = ⟨1, f, .get k⟩ ∨ x = ⟨3, f, .get k⟩) (· k = some v)
    (fun o => o.req = 3 → o.res = .value (some v))

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
  have hread : (spec K V F).Stable (Read k f) :=
    Service.Only.stable fun _ x hx _ => ⟨trivial, by subst hx; simp [spec]⟩
  have hseen : (spec K V F).Stable (Seen k v f) := Service.Only.stable fun _ x hx hv => by
    rcases hx with rfl | rfl <;> simp [spec, hv]
  have hwritten : (spec K V F).Stable (Written k v f) := Service.Took.stable
    (fun _ x hx _ => ⟨trivial, by rcases hx with rfl | rfl <;> simp [spec]⟩)
    (fun _ ⟨req, via, op⟩ o ho => by cases op <;> simp_all [spec])
    (fun x hx hreq => hx.resolve_left fun h => by simp [h] at hreq) (fun _ => by simp [spec])
    (fun _ x hx hne hv => by rcases hx with rfl | rfl <;> simp_all [spec])
  refine hseen.sTr hfalse ?_ h₅ ?_
  · rintro _ _ h ⟨hmem, -⟩
    simpa using h.2.2 _ hmem rfl
  refine hseen.sTr hseen ?_ h₄ ?_
  · rintro a b ⟨hpending, hvalue, houtbox⟩ rfl
    exact ⟨fun x hx => (Multiset.mem_cons.mp hx).elim .inr (hpending x), hvalue, houtbox⟩
  refine hwritten.sTr hseen ?_ h₃ ?_
  · rintro a b ⟨⟨hpending, -, houtbox⟩, -, htook⟩ ⟨hmem, rfl⟩
    obtain ⟨hgone, hvalue⟩ := htook _ hmem rfl
    refine ⟨fun x hx => ?_, hvalue, fun o ho hreq => ?_⟩
    · rcases hpending x hx with rfl | rfl
      · exact .inl rfl
      · exact absurd hx hgone
    · rcases houtbox o (Multiset.mem_of_mem_erase ho) with h | h <;> simp [hreq] at h
  refine hread.sTr hwritten ?_ h₂ ?_
  · rintro a b ⟨hpending, -, houtbox⟩ rfl
    have hnot : (⟨2, f, .put k v⟩ : Request K V F) ∉ a.pending := fun h => by
      simpa using hpending _ h
    refine ⟨⟨fun x hx => ?_, trivial, fun o ho => .inl (houtbox o ho)⟩,
      by simp [Multiset.count_eq_zero_of_notMem hnot], fun o ho hreq => ?_⟩
    · rcases Multiset.mem_cons.mp hx with rfl | hx
      · exact .inr rfl
      · exact .inl (hpending x hx)
    · simp [houtbox o ho] at hreq
  refine hstart.sTr hread ?_ h₁ ⟨rfl, rfl⟩
  rintro a b ⟨hpending, houtbox⟩ rfl
  exact ⟨by simp [hpending], trivial, by simp [houtbox]⟩

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
