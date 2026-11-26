import Lanes.Semantics
import Ledger.Proofs.Actors

/-!
# The ledger is its spec

With no timers (`Config.lockout_ms` and `session_ms` both `none`), for every configuration and
every environment in which each user's link to the ledger is reliable and no request is handed
to a user twice, the system implements its spec (`implements`): requests may be lost and
reordered on the way in, and any actor may crash.

The simulation is the standard one (`Lanes.Account`). A request takes effect when the ledger
handles what its user told it, but the user decided it, and moved its record, when the request
reached it; a log-in that evicts a session cannot be undone from the message. So the witness
is the list of requests decided and not yet served, and the value relation says that the spec's
record of each user, with that user's requests in the list decided in order, gives the user's
record and the messages on the user's link to the ledger (`decideAll`). The ledger takes the
first of them: the link is ordered. A crash of the ledger loses them all; the requests whose
answer the user had decided take effect then (`answered`), and the others never do.

With timers the system does not implement the spec with deadlines: a view decided before a
session ends and served after it can see a payment asked after the end (`Check.lean`).
-/

namespace Ledger

open Lanes

variable {N C : Type}

def Verdict.msg (self : N) (req : ReqId) : Verdict N → LedgerMsg N
  | .reply r => .answer req r
  | .serve op => .serve req self op

def Request.ofAsk (name : N) (req : ReqId) : Ask C → Request N C
  | .signUp c => .signUp req name c
  | .logIn c => .logIn req name c
  | .act session op => .act req name session op

theorem Request.ofAsk_eq (x : Request N C) : Request.ofAsk x.name x.req x.ask = x := by
  cases x <;> rfl

@[simp] theorem Request.name_ofAsk (name : N) (req : ReqId) (ask : Ask C) :
    (Request.ofAsk name req ask).name = name := by
  cases ask <;> rfl

@[simp] theorem Request.req_ofAsk (name : N) (req : ReqId) (ask : Ask C) :
    (Request.ofAsk name req ask).req = req := by
  cases ask <;> rfl

@[simp] theorem Request.ask_ofAsk (name : N) (req : ReqId) (ask : Ask C) :
    (Request.ofAsk name req ask).ask = ask := by
  cases ask <;> rfl

variable [DecidableEq N] [DecidableEq C]

/-- What user `n` decides of `xs` in order from the record `u`: the record after, and what it
tells the ledger. -/
def decideAll (config : Config N) (n : N) :
    Option (Profile C) → List (Request N C) → Option (Profile C) × List (LedgerMsg N)
  | u, [] => (u, [])
  | u, x :: xs =>
    ((decideAll config n (User.decide config n x.req u x.ask).1 xs).1,
      (User.decide config n x.req u x.ask).2.1.msg n x.req ::
        (decideAll config n (User.decide config n x.req u x.ask).1 xs).2)

omit [DecidableEq N] in
theorem decideAll_concat (config : Config N) (n : N) (u : Option (Profile C))
    (xs : List (Request N C)) (x : Request N C) :
    decideAll config n u (xs ++ [x]) =
      ((User.decide config n x.req (decideAll config n u xs).1 x.ask).1,
        (decideAll config n u xs).2 ++
          [(User.decide config n x.req (decideAll config n u xs).1 x.ask).2.1.msg n x.req]) := by
  induction xs generalizing u with
  | nil => rfl
  | cons y xs ih => simp [decideAll, ih]

/-- What a message in flight tells the ledger from user `n`. -/
def told (n : N) : Envelope (sig N C) → Option (LedgerMsg N)
  | ⟨some (.user m), .ledger, msg⟩ => if m = n then some msg else none
  | _ => none

/-- The request a message in flight to a user carries. -/
def asked : Envelope (sig N C) → Option (Request N C)
  | ⟨_, .user n, .ask req ask⟩ => some (.ofAsk n req ask)
  | _ => none

/-- Requests come from outside to a user, and users tell the ledger. -/
def Shaped : Envelope (sig N C) → Prop
  | ⟨none, .user _, .ask _ _⟩ => True
  | ⟨some (.user _), .ledger, _⟩ => True
  | _ => False

/-- No timers. -/
def Untimed (config : Config N) : Prop :=
  config.lockout_ms = none ∧ config.session_ms = none

variable {config : Config N}

theorem timerEffects_untimed (hc : Untimed config) (self : N) (timers : Timers) :
    timerEffects (C := C) config self timers =
      timers.closed.map fun session => .cancel (.expire session) := by
  simp [timerEffects, hc.1, hc.2]

theorem rearm_untimed (hc : Untimed config) (self : N) (u : Option (Profile C)) :
    rearm config self u = [] := by
  cases u <;> simp [rearm, timerEffects, hc.1, hc.2]

theorem tell_viaLedger (self : N) (req : ReqId) (v : Verdict N) :
    tell (C := C) .viaLedger self req v = .send .ledger (v.msg self req) := by
  cases v <;> rfl

/-- No timer is armed, and every message in flight is `Shaped`. -/
def Tame (c : SysState (system N C config)) : Prop :=
  (∀ i m, m ∈ c.timers i → False) ∧ ∀ e ∈ c.net, Shaped e

theorem tame_invariant (hc : Untimed config) (env : EnvModel (sig N C)) :
    (system N C config).Invariant env Tame := by
  have htimers := System.Monotone.timers (system N C config) (T := fun _ _ => False)
    (fun i s msg delay m h => by
      cases i with
      | ledger => cases msg <;> simp [system, ledger] at h
      | user n =>
        cases msg <;> simp [system, user, timerEffects_untimed hc, tell_viaLedger] at h)
    (fun i s delay m h => by
      cases i <;> simp [system, user, ledger, rearm_untimed hc] at h)
  refine (htimers.and_net (Q := fun c : SysState (system N C config) => ∀ e ∈ c.net, Shaped e)
    (fun _ h => nomatch h) ?_ ?_ ?_).invariant env
  · intro c up net timers outbox h hnet e he
    rcases hnet e he with he | ⟨x, rfl⟩
    · exact h e he
    · trivial
  · intro c i msg _ _ h _ e he
    rcases SysState.mem_grow_net.mp he with he | ⟨hsrc, he⟩
    · exact h e he
    · obtain ⟨src, dst, m⟩ := e
      simp only at hsrc
      subst hsrc
      cases i with
      | ledger => cases msg <;> simp [system, ledger] at he
      | user n =>
        cases msg with
        | ask req ask =>
          simp [system, user, timerEffects_untimed hc, tell_viaLedger] at he
          obtain ⟨rfl, -⟩ := he
          trivial
        | _ => simp [system, user] at he
  · intro c i _ _ h e he
    rcases SysState.mem_grow_net.mp he with he | ⟨_, he⟩
    · exact h e he
    · cases i <;> simp [system, user, ledger, rearm_untimed hc] at he

/-- The standard simulation, with the requests decided and not served as the witness. -/
def account (config : Config N) :
    Lanes.Account (system N C config) (SpecState N C) (List (Request N C)) where
  pend := asked
  held _ xs := ↑xs
  value state net xs v := v.book = state .ledger ∧ ∀ n,
    decideAll config n (v.users n) (xs.filter (·.name = n)) =
      (state (.user n), net.filterMap (told n))

theorem told_eq_none {e : Envelope (sig N C)} (n : N) (h : e.dst ≠ .ledger) : told n e = none := by
  obtain ⟨src, dst, msg⟩ := e
  cases dst with
  | ledger => exact absurd rfl h
  | user k => rcases src with _ | _ | _ <;> rfl

theorem asked_ledger (src : Option (Id N)) (m : LedgerMsg N) :
    asked (C := C) ⟨src, .ledger, m⟩ = none := by
  rcases src with _ | _ | _ <;> rfl

theorem told_isSome {e : Envelope (sig N C)} {n : N} (h : (told n e).isSome = true) :
    e.src = some (.user n) ∧ e.dst = .ledger := by
  obtain ⟨src, dst, msg⟩ := e
  cases dst with
  | user k => simp [told_eq_none] at h
  | ledger =>
    cases src with
    | none => simp [told] at h
    | some i =>
      cases i with
      | ledger => simp [told] at h
      | user m =>
        by_cases hm : m = n
        · subst hm
          exact ⟨rfl, rfl⟩
        · simp [told, hm] at h

theorem user_step (hc : Untimed config) (n : N) (s : Option (Profile C)) (req : ReqId)
    (ask : Ask C) : ((system N C config).actor (.user n)).step s (.ask req ask) =
      ((User.decide config n req s ask).1,
        .send .ledger ((User.decide config n req s ask).2.1.msg n req) ::
          (User.decide config n req s ask).2.2.closed.map fun session =>
            .cancel (.expire session)) := by
  simp [system, user, timerEffects_untimed hc, tell_viaLedger]

theorem sends_tell (n : N) (m : LedgerMsg N) (closed : List Sid) :
    Effect.sends (Id.user n) (.send Id.ledger m ::
      closed.map fun session => (.cancel (.expire session) : Effect (sig N C) (Id.user n))) =
      [(⟨some (Id.user n), Id.ledger, m⟩ : Envelope (sig N C))] := by
  induction closed with
  | nil => rfl
  | cons s closed ih => simp [Effect.sends]

theorem emits_tell (n : N) (m : LedgerMsg N) (closed : List Sid) :
    Effect.emits (.send Id.ledger m ::
      closed.map fun session => (.cancel (.expire session) : Effect (sig N C) (Id.user n))) =
      [] := by
  induction closed with
  | nil => rfl
  | cons s closed ih => simp [Effect.emits]

/-- The spec's step is the user's decision and then the ledger's step on what it was told. -/
theorem step_eq (v : SpecState N C) (x : Request N C) :
    SpecState.step config v x =
      (⟨update v.users x.name (User.decide config x.name x.req (v.users x.name) x.ask).1,
        ((ledger (C := C) config).step v.book
          ((User.decide config x.name x.req (v.users x.name) x.ask).2.1.msg x.name x.req)).1⟩,
        Effect.emits ((ledger (C := C) config).step v.book
          ((User.decide config x.name x.req (v.users x.name) x.ask).2.1.msg x.name x.req)).2) := by
  simp only [SpecState.step]
  generalize User.decide config x.name x.req (v.users x.name) x.ask = d
  obtain ⟨u, verdict, _⟩ := d
  cases verdict with
  | reply r => rfl
  | serve op =>
    simp only [Verdict.msg, ledger]
    generalize v.book.serve config x.name x.req op = r
    obtain ⟨b, reply⟩ := r
    rfl

theorem ledger_sends (b : Book N) (m : LedgerMsg N) :
    Effect.sends (σ := sig N C) Id.ledger ((ledger (C := C) config).step b m).2 = [] := by
  cases m <;> rfl

variable {env : EnvModel (sig N C)}

/-- A user decides a request: it joins the witness, and the user's link to the ledger carries
what the user decided. -/
theorem moves_decide (hc : Untimed config) {c : SysState (system N C config)} {n : N}
    {req : ReqId} {ask : Ask C}
    (hmem : (⟨none, .user n, .ask req ask⟩ : Envelope (sig N C)) ∈ c.net) :
    (account config).Moves (spec N C config) c
      (({ c with net := c.net.erase ⟨none, .user n, .ask req ask⟩ }).grow (.user n)
        (((system N C config).actor (.user n)).step (c.state (.user n)) (.ask req ask))) := by
  rw [user_step hc]
  rintro xs v ⟨hbook, husers⟩
  refine ⟨xs ++ [.ofAsk n req ask], [], ⟨?_, fun k => ?_⟩, le_of_eq ?_, le_of_eq ?_⟩
  · simpa [SysState.grow] using hbook
  · simp only [Service.run_nil, SysState.grow, sends_tell, List.filter_append,
      List.filterMap_append,
      filterMap_erase_of_none (rfl : told k ⟨none, .user n, .ask req ask⟩ = none)]
    by_cases hk : n = k
    · subst hk
      simp [decideAll_concat, husers, told]
    · simp [hk, husers, told, Ne.symm hk]
  · have hx : asked (⟨none, .user n, .ask req ask⟩ : Envelope (sig N C)) =
        some (.ofAsk n req ask) := rfl
    simp only [Account.pending, account, SysState.grow, sends_tell, List.filterMap_append,
      Multiset.coe_eq_coe.mpr (filterMap_perm_erase hmem), hx, List.filterMap_cons, asked_ledger,
      List.filterMap_nil, List.append_nil, Option.toList_some, Multiset.coe_nil, ← Multiset.coe_add]
    abel
  · simp [Account.owed, account, SysState.grow, emits_tell]

/-- The ledger serves the oldest message on a user's link: the first request of the user's in
the witness takes effect. -/
theorem moves_serve (hlink : ∀ n, env.link (some (.user n)) .ledger = .reliable)
    {c : SysState (system N C config)} {n : N} {m : LedgerMsg N}
    (hd : c.deliverable env ⟨some (.user n), .ledger, m⟩ = true) :
    (account config).Moves (spec N C config) c
      (({ c with net := c.net.erase ⟨some (.user n), .ledger, m⟩ }).grow .ledger
        ((ledger config).step (c.state .ledger) m)) := by
  rintro xs v ⟨hbook, husers⟩
  have hfind : c.net.find? (Envelope.sameLink ⟨some (Id.user n), Id.ledger, m⟩) =
      some ⟨some (Id.user n), Id.ledger, m⟩ := by
    simpa [SysState.deliverable, hlink n, Link.reliable] using hd
  have htold := filterMap_eq_cons_of_find? (f := told n) (fun e he => by
    obtain ⟨hsrc, hdst⟩ := told_isSome he
    simp [Envelope.sameLink, hsrc, hdst]) hfind (b := m) (by simp [told])
  have hn := husers n
  rw [htold] at hn
  generalize hys : xs.filter (·.name = n) = ys at hn
  obtain _ | ⟨x, ys⟩ := ys
  · simp [decideAll] at hn
  have hx : x ∈ xs ∧ x.name = n := by
    have := List.mem_filter.mp (hys ▸ List.mem_cons_self)
    exact ⟨this.1, of_decide_eq_true this.2⟩
  simp only [decideAll, Prod.mk.injEq, List.cons.injEq] at hn
  obtain ⟨hstate, hmsg, hrest⟩ := hn
  obtain ⟨hxs, rfl⟩ := hx
  refine ⟨xs.erase x, [x], ⟨?_, fun k => ?_⟩, le_of_eq ?_, le_of_eq ?_⟩
  · simp [spec, step_eq, SysState.grow, hmsg, hbook]
  · simp only [Service.run_singleton, spec, step_eq, SysState.grow, ledger_sends, List.append_nil]
    by_cases hk : k = x.name
    · subst hk
      rw [filter_erase_of_pos _ _ (by simp), hys, List.erase_cons_head, update_self,
        update_of_ne _ _ (by simp)]
      exact Prod.ext hstate hrest
    · rw [filter_erase_of_neg _ _ (by simpa using Ne.symm hk), update_of_ne _ _ hk,
        update_of_ne _ _ (by simp), filterMap_erase_of_none (by simp [told, Ne.symm hk])]
      exact husers k
  · simp only [Account.pending, account, SysState.grow, ledger_sends, List.append_nil,
      filterMap_erase_of_none (asked_ledger _ _)]
    rw [← Multiset.coe_erase, Multiset.coe_singleton, add_assoc]
    congr 1
    rw [add_comm, Multiset.singleton_add]
    exact Multiset.cons_erase (Multiset.mem_coe.mpr hxs)
  · simp [Account.owed, account, SysState.grow, spec, step_eq, hmsg, hbook]

omit [DecidableEq N] in
/-- A decision the book serves leaves the user's record as it was. -/
theorem decide_serve {n : N} {req : ReqId} {u : Option (Profile C)} {ask : Ask C} {op : Op}
    (h : (User.decide config n req u ask).2.1 = .serve op) :
    (User.decide config n req u ask).1 = u := by
  cases u with
  | none => cases ask <;> simp [User.decide] at h
  | some p =>
    cases ask with
    | signUp => simp [User.decide] at h
    | logIn => simp [User.decide] at h
    | act session op' =>
      by_cases hl : p.sessions.live session = true
      · cases op' <;> simp_all [User.decide, User.act]
      · simp [User.decide, hl] at h

/-- The requests of `xs` that their users answered without the book, decided in order from
`users`. When the ledger crashes it loses what the users told it; these take effect then, and
the rest never do. -/
def answered (config : Config N) :
    (N → Option (Profile C)) → List (Request N C) → List (Request N C)
  | _, [] => []
  | users, x :: xs =>
    match (User.decide config x.name x.req (users x.name) x.ask).2.1 with
    | .reply _ =>
      x :: answered config
        (update users x.name (User.decide config x.name x.req (users x.name) x.ask).1) xs
    | .serve _ => answered config users xs

theorem answered_sublist (users : N → Option (Profile C)) (xs : List (Request N C)) :
    (answered config users xs).Sublist xs := by
  induction xs generalizing users with
  | nil => exact .slnil
  | cons x xs ih =>
    simp only [answered]
    split
    · exact (ih _).cons_cons x
    · exact (ih _).cons x

/-- The answered requests taking effect leave the book, and give each user the record it has
after deciding all of its requests. -/
theorem run_answered (v : SpecState N C) (xs : List (Request N C)) :
    ((spec N C config).run v (answered config v.users xs)).1.book = v.book ∧
      ∀ n, ((spec N C config).run v (answered config v.users xs)).1.users n =
        (decideAll config n (v.users n) (xs.filter (·.name = n))).1 := by
  induction xs generalizing v with
  | nil => exact ⟨rfl, fun _ => rfl⟩
  | cons x xs ih =>
    simp only [answered]
    split
    · next r hr =>
      have hstep : (spec N C config).step v x =
          (⟨update v.users x.name (User.decide config x.name x.req (v.users x.name) x.ask).1,
            v.book⟩, [⟨x.req, r⟩]) := by
        simp [spec, step_eq, hr, Verdict.msg, ledger, Effect.emits]
      obtain ⟨hbook, husers⟩ := ih ⟨update v.users x.name _, v.book⟩
      refine ⟨by simpa [Service.run, hstep] using hbook, fun n => ?_⟩
      simp only [Service.run, hstep, husers, List.filter_cons]
      by_cases hn : x.name = n
      · subst hn
        simp [decideAll]
      · simp [hn, Ne.symm hn]
    · next op hop =>
      obtain ⟨hbook, husers⟩ := ih v
      refine ⟨hbook, fun n => ?_⟩
      rw [husers, List.filter_cons]
      by_cases hn : x.name = n
      · subst hn
        simp [decideAll, decide_serve hop]
      · simp [hn]

/-- The ledger crashes and loses what the users told it: the requests they answered take
effect, and the witness is empty. -/
theorem moves_crash (hlink : ∀ n, env.link (some (.user n)) .ledger = .reliable)
    (c : SysState (system N C config)) :
    (account config).Moves (spec N C config) c (c.down env .ledger) := by
  rintro xs v ⟨hbook, husers⟩
  obtain ⟨hbook', husers'⟩ := run_answered (config := config) v xs
  have hsub := Multiset.coe_le.mpr (answered_sublist (config := config) v.users xs).subperm
  refine ⟨[], answered config v.users xs, ⟨hbook'.trans hbook, fun n => ?_⟩, ?_, ?_⟩
  · simp only [List.filter_nil, decideAll, husers', husers n, SysState.down, Prod.mk.injEq,
      true_and]
    refine (List.filterMap_eq_nil_iff.mpr fun e he => ?_).symm
    cases h : told n e with
    | none => rfl
    | some _ =>
      obtain ⟨hsrc, hdst⟩ := told_isSome (e := e) (n := n) (by simp [h])
      have := (List.mem_filter.mp he).2
      simp [hsrc, hdst, hlink, Link.reliable] at this
  · simp only [Account.pending, account, SysState.down, Multiset.coe_nil, add_zero]
    exact add_le_add (Multiset.coe_le.mpr ((List.filter_sublist).filterMap _).subperm) hsub
  · simpa [Account.owed, account, SysState.down] using (List.sublist_append_left _ _).subperm

theorem implements (hc : Untimed config) (env : EnvModel (sig N C))
    (hlink : ∀ n, env.link (some (.user n)) .ledger = .reliable)
    (hin : ∀ n, (env.link none (.user n)).duplicating = false) :
    (system N C config).Implements env (spec N C config) := by
  refine (account config).implements (tame_invariant hc env)
    ⟨[], ⟨rfl, fun _ => rfl⟩, by simp [Account.pending, account, SysState.init, SysState.blank],
      by simp [Account.owed, account, SysState.init, SysState.blank]⟩
    (fun x => ⟨congrArg some (Request.ofAsk_eq x), rfl⟩)
    (fun c xs v x _ ⟨hbook, husers⟩ => ⟨hbook, fun n => by
      rw [filterMap_concat, told_eq_none n (by simp)]
      simpa using husers n⟩)
    ?_ ?_ ?_ ?_ (fun _ i msg ⟨htimers, _⟩ hmem => (htimers i msg hmem).elim) ?_
  · rintro c ⟨src, dst, msg⟩ ⟨_, hshape⟩ hd
    have hmem := SysState.mem_of_deliverable hd
    have := hshape _ hmem
    cases dst with
    | user n =>
      rcases src with _ | _ | _ <;> cases msg <;> simp [Shaped] at this
      exact moves_decide hc hmem
    | ledger =>
      rcases src with _ | _ | n <;> simp [Shaped] at this
      exact moves_serve hlink hd
  · rintro c ⟨src, dst, msg⟩ ⟨_, hshape⟩ hd hdup
    have := hshape _ (SysState.mem_of_deliverable hd)
    cases dst with
    | user n =>
      rcases src with _ | _ | _ <;> cases msg <;> simp [Shaped] at this
      simp [hin] at hdup
    | ledger =>
      rcases src with _ | _ | n <;> simp [Shaped] at this
      simp [hlink, Link.reliable] at hdup
  · rintro c e ⟨_, hshape⟩ hmem hlossy
    refine .of_loses ⟨rfl, List.erase_sublist, fun _ _ h => h, rfl⟩ fun xs v ⟨hbook, husers⟩ =>
      ⟨hbook, fun n => ?_⟩
    have hnone : told n e = none := by
      obtain ⟨src, dst, msg⟩ := e
      have := hshape _ hmem
      cases dst with
      | user k => exact told_eq_none n nofun
      | ledger =>
        rcases src with _ | _ | k <;> simp [Shaped] at this
        simp [hlink, Link.reliable] at hlossy
    rw [filterMap_erase_of_none hnone]
    exact husers n
  · intro c i hi
    cases i with
    | ledger => exact moves_crash hlink c
    | user n =>
      refine .of_loses (SysState.Loses.down env c _) fun xs v ⟨hbook, husers⟩ =>
        ⟨hbook, fun k => ?_⟩
      rw [SysState.down, filterMap_filter_of_none fun e he => told_eq_none k fun h => by
        simp [h] at he]
      exact husers k
  · intro c i _
    cases i with
    | user n =>
      exact .quiet (fun _ _ h => by simpa using h) (by rw [rearm_untimed hc]; rfl)
        (by rw [rearm_untimed hc]; rfl)
    | ledger => exact .quiet (fun _ _ h => by simpa using h) rfl rfl

end Ledger
