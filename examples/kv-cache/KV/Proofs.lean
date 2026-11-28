/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Semantics
import KV

/-!
# The store behind its front ends is a map

Without caching, for all keys, values and front ends, the system implements its five-line spec
in every environment whose links do not hand a message over twice and where the process does not
restart (`implements`): messages may be lost and reordered and actors may crash. A restart puts
the store back to empty while the spec keeps its map, so it is not allowed. `Tests/KV.lean` checks that each link the system
uses must not duplicate: every handling of a message answers a client or sends on.

The simulation is the standard one (`Lanes.Account`): the store's data is the spec's value, a
request is pending in the spec while it is on its way to a front end or from a front end to the
store (`pend`), and the answer to a read is owed while it is on its way back (`owed`). A front
end passes on what it was handed (`Moves.forward`); a request takes effect when the store
handles it (`Moves.take`).

Behind `Once.actor` (`onceSystem`) the store implements `once` of the spec in every
environment without restarts, links duplicating included (`implements_once`). A restart forgets
the memo, so a request repeated after it takes effect again. Its simulation (`OnceSim`) reads
the network as a set: every request in flight has arrived, every answer owed has been given.

With caching the system does not implement the spec in any environment, for any instance with a
key, a value and a front end (`caching_not_implements`): the run the checker finds, a read
served from the cache after an acknowledged write, is a run of every such instance.
-/

namespace KV

open Lanes Service

variable {K V F : Type} [DecidableEq K] [DecidableEq V] [DecidableEq F]

def pend : Envelope (sig K V F) → Option (Request K V F)
  | ⟨_, .front f, .request r⟩ => some ⟨r.req, f, r.op⟩
  | ⟨_, .store, .put req key value via⟩ => some ⟨req, via, .put key value⟩
  | ⟨_, .store, .get req key replyTo⟩ => some ⟨req, replyTo, .get key⟩
  | _ => none

def owed : Envelope (sig K V F) → Option (Response V)
  | ⟨_, .front _, .got req _ value⟩ => some ⟨req, .value value⟩
  | _ => none

abbrev Abs (K V F : Type) [DecidableEq K] [DecidableEq V] [DecidableEq F] :=
  Service.Abs (Request K V F) (Response V) (K → Option V)

theorem unarmed {i : Id F} {m : (sig K V F).Msg i} (h : (system K V F false).Armed i m) : False := by
  cases h with
  | step _ s msg h => cases i <;> cases msg <;> simp [system, front, store] at h; split at h <;> simp at h
  | recover _ s h => cases i <;> simp [system, front, store] at h

def account : Account (system K V F false) (K → Option V) Unit where
  pend := pend
  owe := owed
  value state _ _ v := v = state .store

theorem implements (env : EnvModel (sig K V F))
    (henv : ∀ src dst, (env.link src dst).duplicating = false)
    (hrestart : env.mayRestart = false) :
    (system K V F false).Implements env (spec K V F) := by
  refine account.implements (inv := fun _ => True) (fun _ _ => trivial)
    ⟨(), rfl, by simp [Account.pending, SysState.init, SysState.blank, account],
      by simp [Account.owed, SysState.init, SysState.blank, account]⟩
    (fun _ => ⟨rfl, rfl⟩) (fun _ _ _ _ _ h => h) ?_ (fun _ _ _ _ _ hdup => by simp [henv] at hdup)
    (fun _ _ _ _ _ _ => .of_loses ⟨rfl, List.erase_sublist, fun _ _ h => h, rfl⟩ fun _ _ h => h)
    (fun c i _ => .of_loses (SysState.Loses.down env c i) fun _ _ h => h)
    (fun _ _ _ _ h _ => (unarmed h).elim)
    (fun _ i _ => by cases i <;> exact .quiet (fun _ _ h => by simpa [account] using h) rfl rfl)
    (fun h => absurd h (by simp [hrestart]))
  rintro c ⟨src, dst, msg⟩ _ _ hd
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
    | put req key value via =>
      exact .take hmem (x := ⟨req, via, .put key value⟩) rfl rfl
        (fun _ _ h => by subst h; simp [account]; rfl) rfl fun _ _ _ => rfl
    | get req key replyTo =>
      exact .take hmem (x := ⟨req, replyTo, .get key⟩) rfl rfl
        (fun _ _ h => by subst h; simp [account]; rfl) rfl fun _ _ h => by subst h; rfl

/-! ## Requests named by their client -/

section Once

abbrev OnceAbs (K V F : Type) [DecidableEq K] [DecidableEq V] [DecidableEq F] :=
  Service.Once (Request K V F) (Response V) (K → Option V) (F × ReqId)

/-- What `e` is on its way to do is accounted for: its request has arrived, its answer is
given. -/
def Covered (t : OnceAbs K V F) (e : Envelope (sig K V F)) : Prop :=
  (∀ x ∈ pend e, t.arrived x) ∧ ∀ o ∈ owed e, t.answered o

def EffCovered (t : OnceAbs K V F) {i : Id F} : Effect (sig K V F) i → Prop
  | .send dst msg => Covered t ⟨some i, dst, msg⟩
  | .emit out => t.answered out
  | .after .. => False
  | _ => True

theorem Covered.mono {t t' : OnceAbs K V F} {e : Envelope (sig K V F)} (h : Covered t e)
    (hg : t.Grows t') : Covered t' e :=
  ⟨fun x hx => hg.arrived (h.1 x hx), fun o ho => hg.answered (h.2 o ho)⟩

theorem EffCovered.mono {t t' : OnceAbs K V F} {i : Id F} {eff : Effect (sig K V F) i}
    (h : EffCovered t eff) (hg : t.Grows t') : EffCovered t' eff := by
  cases eff with
  | send dst msg => exact Covered.mono h hg
  | emit out => exact hg.answered h
  | after => exact h.elim
  | cancel => trivial
  | stop => trivial

/-- The store's data is the spec's value, everything in flight or waiting to go out is
accounted for, no timer is armed, and the memo agrees with the keys taken. -/
structure OnceSim (c : SysState (onceSystem K V F)) (t : OnceAbs K V F) : Prop where
  value : t.value = (c.state .store).1
  net : ∀ e ∈ c.net, Covered t e
  outbox : ∀ o ∈ c.outbox, t.answered o
  timers : ∀ i (m : Msg K V F i), m ∉ c.timers i
  memo : (c.state .store).2.Agrees t.taken (EffCovered t)

/-- The store does not read the step's context. -/
theorem store_stepAt (ctx : Ctx (Id F)) (data : K → Option V) (msg : StoreMsg K V F) :
    store.stepAt ctx data msg = store.step data msg :=
  rfl

/-- The store acting on `msg` is the spec's step on the request it carries. -/
theorem store_step (data : K → Option V) {src : Option (Id F)} {msg : StoreMsg K V F}
    {x : Request K V F} (hx : pend ⟨src, .store, msg⟩ = some x) :
    storeKey msg = some (requestKey x) ∧
      (store.step data msg).1 = ((spec K V F).step data x).1 ∧
      ∀ t : OnceAbs K V F, (∀ o ∈ ((spec K V F).step data x).2, t.answered o) →
        ∀ eff ∈ (store.step data msg).2, EffCovered t eff := by
  cases msg <;> simp only [pend, Option.some.injEq] at hx <;> subst hx <;>
    simp [storeKey, requestKey, store, spec, EffCovered, Covered, pend, owed]

namespace OnceSim

variable {c : SysState (onceSystem K V F)} {t t' : OnceAbs K V F}

theorem loses {c' : SysState (onceSystem K V F)} (h : OnceSim c t) (hl : c'.Loses c) :
    OnceSim c' t where
  value := by rw [hl.state]; exact h.value
  net e he := h.net e (hl.net.subset he)
  outbox o ho := h.outbox o (hl.outbox ▸ ho)
  timers i m hm := h.timers i m (hl.timers i m hm)
  memo := by rw [hl.state]; exact h.memo

theorem grow (h : OnceSim c t) (hg : t.Grows t') {net : List (Envelope (sig K V F))}
    (hnet : net.Sublist c.net) {i : Id F}
    {r : (onceSystem K V F).State i × List (Effect (sig K V F) i)}
    (hvalue : t'.value = ((({ c with net }).grow i r).state .store).1)
    (hmemo : ((({ c with net }).grow i r).state .store).2.Agrees t'.taken (EffCovered t'))
    (heffs : ∀ eff ∈ r.2, EffCovered t' eff) : OnceSim (({ c with net }).grow i r) t' := by
  refine ⟨hvalue, fun e he => ?_, fun o ho => ?_, fun j m hm => ?_, hmemo⟩
  · rcases SysState.mem_grow_net.mp he with he | ⟨hsrc, hsend⟩
    · exact (h.net e (hnet.subset he)).mono hg
    · obtain ⟨src, dst, msg⟩ := e
      obtain rfl : src = some i := hsrc
      exact heffs _ hsend
  · simp only [SysState.grow, List.mem_append] at ho
    rcases ho with ho | ho
    · exact hg.answered (h.outbox o ho)
    · exact heffs _ (Effect.mem_emits.mp ho)
  · rcases SysState.mem_grow_timers.mp hm with hm | ⟨rfl, delay, hafter⟩
    · exact h.timers j m hm
    · simpa [EffCovered] using heffs _ hafter

theorem onFront (h : OnceSim c t) {net : List (Envelope (sig K V F))} (hnet : net.Sublist c.net)
    {f : F} {msg : FrontMsg K V F}
    (hmem : ∃ src, (⟨src, .front f, msg⟩ : Envelope (sig K V F)) ∈ c.net) :
    OnceSim (({ c with net }).grow (.front f) ((front false f).step (c.state (.front f)) msg)) t := by
  obtain ⟨src, hmem⟩ := hmem
  have hcov := h.net _ hmem
  refine h.grow (.refl _) hnet (by simp [h.value]) (by simpa using h.memo) ?_
  cases msg with
  | request r =>
    obtain ⟨req, via, op⟩ := r
    cases op <;> simpa [front, EffCovered, Covered, pend, owed] using hcov
  | got req key value => simpa [front, EffCovered, Covered, pend, owed] using hcov

theorem onStore (h : OnceSim c t) {net : List (Envelope (sig K V F))} (hnet : net.Sublist c.net)
    {msg : StoreMsg K V F}
    (hmem : ∃ src, (⟨src, .store, msg⟩ : Envelope (sig K V F)) ∈ c.net) :
    ∃ t', ((spec K V F).once requestKey).lts.τSTr t t' ∧ OnceSim (({ c with net }).grow .store
      ((Once.actor store storeKey).stepAt {} (c.state .store) msg)) t' := by
  obtain ⟨src, hmem⟩ := hmem
  obtain ⟨x, hx⟩ : ∃ x, pend ⟨src, .store, msg⟩ = some x := by cases msg <;> exact ⟨_, rfl⟩
  have harrived : t.arrived x := (h.net _ hmem).1 x hx
  obtain ⟨hkey, hvalue, hcovers⟩ := store_step (c.state .store).1 hx
  have hval := h.value
  have hmemo := h.memo
  rw [← Prod.eta (c.state .store)]
  rw [← Prod.eta (c.state .store)] at hval hmemo
  generalize (c.state .store).1 = data at hval hmemo hvalue hcovers ⊢
  generalize (c.state .store).2 = memo at hval hmemo ⊢
  cases hs : memo.seen x.via x.req with
  | fresh =>
    have hstep := once_take (svc := spec K V F) (key := requestKey) harrived (hmemo.fresh hs)
    have hg := once_grows_τSTr hstep
    have heffs : ∀ eff ∈ (store.step data msg).2,
        EffCovered (t.take (spec K V F) requestKey x) eff :=
      hcovers _ fun o ho => Or.inr (by rw [hval]; exact ho)
    refine ⟨_, hstep, ?_⟩
    rw [Once.step_of_fresh _ _ _ _ _ hkey hs, store_stepAt]
    refine h.grow hg hnet ?_ ?_ heffs
    · simp [Service.Once.take, hval, hvalue]
    · simp only [SysState.grow_state_self]
      exact (hmemo.mono fun _ he => he.mono hg).record hs heffs
  | again effs =>
    refine ⟨t, .refl, ?_⟩
    rw [Once.step_of_again _ _ _ _ _ hkey hs]
    exact h.grow (.refl _) hnet (by simpa using hval) (by simpa using hmemo) (hmemo.again hs)
  | stale =>
    refine ⟨t, .refl, ?_⟩
    rw [Once.step_of_stale _ _ _ _ _ hkey hs]
    exact h.grow (.refl _) hnet (by simpa using hval) (by simpa using hmemo) (by simp)

end OnceSim

/--
The store that remembers is a map to clients that name their requests, in every environment:
links may lose, reorder and hand over twice every message, and every actor may crash. A request
takes effect at most once per front end and number, between its arrival and its answer, and its
answer may be handed over more than once.
-/
theorem implements_once (env : EnvModel (sig K V F)) (hrestart : env.mayRestart = false) :
    (onceSystem K V F).ImplementsOnce env (spec K V F) requestKey := by
  refine System.Refines.of_handles (inv := fun _ => True) (fun _ _ => trivial) OnceSim
    ⟨⟨fun _ => none, fun _ => False, fun _ => False, fun _ => False⟩, rfl, ⟨rfl, by simp [SysState.init, SysState.blank],
      by simp [SysState.init, SysState.blank], by simp [SysState.init, SysState.blank],
      Once.Memo.Agrees.empty⟩⟩
    (fun _ _ _ h hl => h.loses hl) ?_ ?_ ?_ ?_ (fun h => absurd h (by simp [hrestart]))
  · intro c t x _ h
    have hg : t.Grows { t with arrived := fun y => y = x ∨ t.arrived y } :=
      ⟨fun _ h => .inr h, fun _ h => h, fun _ h => h⟩
    refine ⟨_, .single rfl, h.value, fun e he => ?_, h.outbox, h.timers,
      h.memo.mono fun _ he => he.mono hg⟩
    rcases List.mem_append.mp he with he | he
    · exact (h.net e he).mono hg
    · obtain rfl := List.mem_singleton.mp he
      exact ⟨fun y hy => by simp [pend] at hy; subst hy; exact .inl rfl,
        fun o ho => by simp [owed] at ho⟩
  · intro c t out _ h hmem
    exact ⟨t, .single ⟨h.outbox out hmem, rfl⟩, h.value, h.net,
      fun o ho => h.outbox o (List.mem_of_mem_erase ho), h.timers, h.memo⟩
  · intro c t net i msg _ _ h hnet hpend
    have hpend := hpend.resolve_right (h.timers i msg)
    cases i with
    | front f => exact ⟨t, .refl, h.onFront hnet hpend⟩
    | store => exact h.onStore hnet hpend
  · intro c t i _ h
    refine ⟨t, .refl, ?_⟩
    cases i with
    | front f =>
      exact h.grow (net := c.net) (.refl _) (.refl _) (by simp [h.value]) (by simpa using h.memo)
        (by simp [KV.front])
    | store =>
      exact h.grow (net := c.net) (.refl _) (.refl _) (by simp [h.value, Once.recover_eq, KV.store])
        (by simpa [Once.recover_eq, KV.store] using h.memo) (by simp [Once.recover_eq, KV.store])

end Once

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
    exact ⟨fun x hx => (Bag.mem_cons.mp hx).elim .inr (hpending x), hvalue, houtbox⟩
  refine hwritten.sTr hseen ?_ h₃ ?_
  · rintro a b ⟨⟨hpending, -, houtbox⟩, -, htook⟩ ⟨hmem, rfl⟩
    obtain ⟨hgone, hvalue⟩ := htook _ hmem rfl
    refine ⟨fun x hx => ?_, hvalue, fun o ho hreq => ?_⟩
    · rcases hpending x hx with rfl | rfl
      · exact .inl rfl
      · exact absurd hx hgone
    · rcases houtbox o (Bag.mem_of_mem_erase ho) with h | h <;> simp [hreq] at h
  refine hread.sTr hwritten ?_ h₂ ?_
  · rintro a b ⟨hpending, -, houtbox⟩ rfl
    have hnot : (⟨2, f, .put k v⟩ : Request K V F) ∉ a.pending := fun h => by
      simpa using hpending _ h
    refine ⟨⟨fun x hx => ?_, trivial, fun o ho => .inl (houtbox o ho)⟩,
      by simp [Bag.count_eq_zero_of_notMem hnot], fun o ho hreq => ?_⟩
    · rcases Bag.mem_cons.mp hx with rfl | hx
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

end KV
