import Lanes.Semantics
import Ledger.Proofs.Actors

/-!
# The ledger is its spec

With no timers (`Config.lockout_ms` and `session_ms` both `none`), for every configuration and
every environment in which each user's link to the ledger is ordered and does not duplicate,
and no request is handed to a user twice, the system implements its spec (`implements`):
messages may be lost on every link and reordered on the way in, and any actor may crash.

The simulation is the standard one (`Lanes.Account`). A request takes effect when the ledger
handles what its user told it, but the user decided it, and moved its record, when the request
reached it; a log-in that evicts a session cannot be undone from the message. So the witness is
the list of requests decided and not yet served, each marked with whether what its user told
the ledger is still on the link, and the value relation says that the spec's record of each
user, with that user's requests in the list decided in order, gives the user's record and the
messages on the user's link to the ledger (`decideAll`). A loss, or a crash of the ledger,
unmarks. The ledger serves the oldest message on the link; the requests before it whose
message was lost take effect then if the user answered them (`answered`), and never if the
book was to serve them, which leaves the user's record as it was.

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

variable [DecidableEq N] [DecidableEq C]

/-- User `n`'s record after deciding `xs` in order from `u`. -/
def record (config : Config N) (n : N) (u : Option (Profile C)) (xs : List (Request N C)) :
    Option (Profile C) :=
  xs.foldl (fun u x => (User.decide config n x.req u x.ask).1) u

/-- What user `n` decides of `xs` in order from the record `u`: the record after, and what it
told the ledger of the requests whose message is still on the link (marked `true`). -/
def decideAll (config : Config N) (n : N) :
    Option (Profile C) → List (Request N C × Bool) → Option (Profile C) × List (LedgerMsg N)
  | u, [] => (u, [])
  | u, (x, b) :: xs =>
    ((decideAll config n (User.decide config n x.req u x.ask).1 xs).1,
      (if b then [(User.decide config n x.req u x.ask).2.1.msg n x.req] else []) ++
        (decideAll config n (User.decide config n x.req u x.ask).1 xs).2)

variable {config : Config N} {n : N}

omit [DecidableEq N] in
theorem decideAll_concat (u : Option (Profile C)) (ys : List (Request N C × Bool))
    (x : Request N C) :
    decideAll config n u (ys ++ [(x, true)]) =
      ((User.decide config n x.req (decideAll config n u ys).1 x.ask).1,
        (decideAll config n u ys).2 ++
          [(User.decide config n x.req (decideAll config n u ys).1 x.ask).2.1.msg n x.req]) := by
  induction ys generalizing u with
  | nil => simp [decideAll]
  | cons y ys ih => simp [decideAll, ih]

omit [DecidableEq N] in
/-- Unmarking every request when `b` is false leaves the record and tells nothing. -/
theorem decideAll_mark (b : Bool) (u : Option (Profile C)) (ys : List (Request N C × Bool)) :
    decideAll config n u (ys.map fun p => (p.1, p.2 && b)) =
      ((decideAll config n u ys).1, if b then (decideAll config n u ys).2 else []) := by
  induction ys generalizing u with
  | nil => cases b <;> rfl
  | cons y ys ih => cases b <;> simp_all [decideAll]

/-- Losing a message from the link unmarks the request it was for. -/
theorem decideAll_erase (m : LedgerMsg N) (u : Option (Profile C))
    (ys : List (Request N C × Bool)) : ∃ ys', ys'.map Prod.fst = ys.map Prod.fst ∧
      decideAll config n u ys' = ((decideAll config n u ys).1, (decideAll config n u ys).2.erase m) := by
  induction ys generalizing u with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons y ys ih =>
    obtain ⟨x, b⟩ := y
    by_cases hm : b = true ∧ (User.decide config n x.req u x.ask).2.1.msg n x.req = m
    · obtain ⟨rfl, hm⟩ := hm
      exact ⟨(x, false) :: ys, rfl, by simp [decideAll, hm]⟩
    · obtain ⟨ys', hmap, hys'⟩ := ih (User.decide config n x.req u x.ask).1
      refine ⟨(x, b) :: ys', by simp [hmap], ?_⟩
      simp only [decideAll, hys', Prod.mk.injEq, true_and]
      cases b
      · rfl
      · simp only [↓reduceIte, List.singleton_append]
        rw [List.erase_cons_tail (by simpa using fun h => hm ⟨rfl, h⟩)]

omit [DecidableEq N] in
/-- The first message on the link is told for the first marked request: those before it have
lost theirs. -/
theorem decideAll_eq_cons {u : Option (Profile C)} {ys : List (Request N C × Bool)}
    {s : Option (Profile C)} {m : LedgerMsg N} {rest : List (LedgerMsg N)}
    (h : decideAll config n u ys = (s, m :: rest)) :
    ∃ pre x post, ys = pre ++ (x, true) :: post ∧ (∀ p ∈ pre, p.2 = false) ∧
      (User.decide config n x.req (record config n u (pre.map Prod.fst)) x.ask).2.1.msg n x.req
        = m ∧
      decideAll config n
        (User.decide config n x.req (record config n u (pre.map Prod.fst)) x.ask).1 post =
        (s, rest) := by
  induction ys generalizing u with
  | nil => simp [decideAll] at h
  | cons y ys ih =>
    obtain ⟨x, b⟩ := y
    cases b with
    | true =>
      simp only [decideAll, ↓reduceIte, List.singleton_append, Prod.mk.injEq, List.cons.injEq] at h
      exact ⟨[], x, ys, rfl, nofun, h.2.1, Prod.ext h.1 h.2.2⟩
    | false =>
      obtain ⟨pre, x', post, rfl, hpre, hmsg, hpost⟩ := ih (by simpa [decideAll] using h)
      exact ⟨(x, false) :: pre, x', post, rfl, by simpa using hpre, hmsg, hpost⟩

/-- What a message in flight to a user asks. -/
def asked : Envelope (sig N C) → Option (Request N C)
  | ⟨_, .user n, .ask req ask⟩ => some (.ofAsk n req ask)
  | _ => none

theorem asked_ledger (src : Option (Id N)) (m : LedgerMsg N) :
    asked (C := C) ⟨src, .ledger, m⟩ = none := by
  rcases src with _ | _ | _ <;> rfl

/-- No timers. -/
def Untimed (config : Config N) : Prop :=
  config.lockout_ms = none ∧ config.session_ms = none

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

theorem user_step (hc : Untimed config) (s : Option (Profile C)) (req : ReqId) (ask : Ask C) :
    (user config .viaLedger n).step s (.ask req ask) =
      ((User.decide config n req s ask).1,
        .send .ledger ((User.decide config n req s ask).2.1.msg n req) ::
          (User.decide config n req s ask).2.2.closed.map fun session =>
            .cancel (.expire session)) := by
  simp [user, timerEffects_untimed hc, tell_viaLedger]

theorem ledger_sends (b : Book N) (m : LedgerMsg N) :
    Effect.sends (σ := sig N C) Id.ledger ((ledger (C := C) config).step b m).2 = [] := by
  cases m <;> rfl

theorem unarmed (hc : Untimed config) {i : Id N} {m : (sig N C).Msg i}
    (h : (system N C config).Armed i m) : False := by
  cases h with
  | step s msg h =>
    cases i with
    | ledger => cases msg <;> simp [system, ledger] at h
    | user n =>
      cases msg with
      | ask => simp [system, user, timerEffects_untimed hc, tell_viaLedger] at h
      | unlock | expire =>
        simp only [system, user] at h
        split at h <;> simp [notice] at h
  | recover s h => cases i <;> simp [system, user, ledger, rearm_untimed hc] at h

/-- The standard simulation, with the requests decided and not served as the witness. -/
def account (config : Config N) :
    Lanes.Account (system N C config) (SpecState N C) (List (Request N C × Bool)) where
  pend := asked
  held _ w := ↑(w.map Prod.fst)
  value state net w v := v.book = state .ledger ∧ ∀ n,
    decideAll config n (v.users n) (w.filter (·.1.name = n)) =
      (state (.user n), linkMsgs (some (Id.user n)) Id.ledger net)

omit [DecidableEq C] in
/-- The witness with user `n`'s requests replaced by `ys`. -/
theorem filter_regroup (w ys : List (Request N C × Bool)) (hys : ∀ p ∈ ys, p.1.name = n)
    (k : N) : (w.filter (·.1.name ≠ n) ++ ys).filter (·.1.name = k) =
      if k = n then ys else w.filter (·.1.name = k) := by
  split
  · next hk =>
    subst hk
    have hself : ys.filter (·.1.name = k) = ys := List.filter_eq_self.mpr fun p hp => by
      simp [hys p hp]
    rw [List.filter_append, hself, List.filter_filter]
    simp
  · next hk =>
    have hnil : ys.filter (·.1.name = k) = [] :=
      List.filter_eq_nil_iff.mpr fun p hp => by simpa [hys p hp] using Ne.symm hk
    rw [List.filter_append, hnil, List.append_nil, List.filter_filter]
    exact List.filter_congr fun p _ => by by_cases h : p.1.name = k <;> simp [h, hk]

omit [DecidableEq C] in
theorem held_regroup (w ys : List (Request N C × Bool)) :
    (↑((w.filter (·.1.name ≠ n) ++ ys).map Prod.fst) : Multiset (Request N C)) +
        ↑((w.filter (·.1.name = n)).map Prod.fst) = ↑(w.map Prod.fst) + ↑(ys.map Prod.fst) := by
  have hw : (w.filter (·.1.name ≠ n) ++ w.filter (·.1.name = n)).Perm w := by
    simpa using List.perm_append_comm.trans
      (List.filter_append_perm (fun p : Request N C × Bool => decide (p.1.name = n)) w)
  rw [← Multiset.coe_eq_coe.mpr (hw.map Prod.fst)]
  simp only [List.map_append, ← Multiset.coe_add]
  abel

omit [DecidableEq N] in
/-- A decision the book serves leaves the user's record as it was. -/
theorem decide_serve {req : ReqId} {u : Option (Profile C)} {ask : Ask C} {op : Op}
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
`users`. Those before the message the ledger serves whose own message was lost take effect
then; the rest never do. -/
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

theorem spec_step : (spec N C config).step = SpecState.step config := rfl

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

/-- The answered requests taking effect leave the book, and give each user the record it has
after deciding all of its requests. -/
theorem run_answered (v : SpecState N C) (xs : List (Request N C)) :
    ((spec N C config).run v (answered config v.users xs)).1.book = v.book ∧
      ∀ k, ((spec N C config).run v (answered config v.users xs)).1.users k =
        record config k (v.users k) (xs.filter (·.name = k)) := by
  induction xs generalizing v with
  | nil => exact ⟨rfl, fun _ => rfl⟩
  | cons x xs ih =>
    simp only [answered]
    split
    · next r hr =>
      have hstep : (spec N C config).step v x =
          (⟨update v.users x.name (User.decide config x.name x.req (v.users x.name) x.ask).1,
            v.book⟩, [⟨x.req, r⟩]) := by
        simp [spec, step_eq, hr, Verdict.msg, ledger]
      obtain ⟨hbook, husers⟩ := ih ⟨update v.users x.name _, v.book⟩
      refine ⟨by simpa [Service.run, hstep] using hbook, fun k => ?_⟩
      simp only [Service.run, hstep, husers, List.filter_cons]
      by_cases hk : x.name = k
      · subst hk
        simp [record]
      · simp [hk, Ne.symm hk]
    · next op hop =>
      obtain ⟨hbook, husers⟩ := ih v
      refine ⟨hbook, fun k => ?_⟩
      rw [husers, List.filter_cons]
      by_cases hk : x.name = k
      · subst hk
        simp [record, decide_serve hop]
      · simp [hk]

variable {env : EnvModel (sig N C)}

/-- A user decides a request: it joins the witness, and the user's link to the ledger carries
what the user decided. -/
theorem moves_decide (hc : Untimed config) {c : SysState (system N C config)} (x : Request N C)
    (hmem : (⟨none, .user x.name, .ask x.req x.ask⟩ : Envelope (sig N C)) ∈ c.net) :
    (account config).Moves (spec N C config) c
      (({ c with net := c.net.erase ⟨none, .user x.name, .ask x.req x.ask⟩ }).grow (.user x.name)
        (((system N C config).actor (.user x.name)).step (c.state (.user x.name))
          (.ask x.req x.ask))) := by
  refine .handle hmem fun w v ⟨hbook, husers⟩ =>
    ⟨w ++ [(x, true)], [], ⟨by simpa using hbook, fun k => ?_⟩, ?_, ?_⟩
  · rw [linkMsgs_append, linkMsgs_erase_of_ne (by simp), user_step hc]
    by_cases hk : k = x.name
    · subst hk
      simp [decideAll_concat, husers]
    · simp [hk, Ne.symm hk, husers]
  · refine le_of_eq ?_
    simp [user_step hc, account, asked, Request.ofAsk_eq, add_comm,
      ← Multiset.coe_add]
  · simp [user_step hc, account]

/-- The ledger serves the oldest message on a user's link: the first request of the user's in
the witness whose message is still on the link takes effect, after those before it that their
user answered. -/
theorem moves_serve (hord : (env.link (some (.user n)) .ledger).ordered = true)
    {c : SysState (system N C config)} {m : LedgerMsg N}
    (hd : c.deliverable env ⟨some (.user n), .ledger, m⟩ = true) :
    (account config).Moves (spec N C config) c
      (({ c with net := c.net.erase ⟨some (.user n), .ledger, m⟩ }).grow .ledger
        ((ledger config).step (c.state .ledger) m)) := by
  refine .handle (SysState.mem_of_deliverable hd) fun w v ⟨hbook, husers⟩ => ?_
  have hn := husers n
  rw [linkMsgs_of_deliverable hord hd] at hn
  obtain ⟨pre, x, post, hys, hpre, hmsg, hpost⟩ := decideAll_eq_cons hn
  have hname : ∀ p ∈ pre ++ (x, true) :: post, p.1.name = n := fun p hp => by
    rw [← hys] at hp
    simpa using (List.mem_filter.mp hp).2
  obtain rfl : x.name = n := hname (x, true) (by simp)
  obtain ⟨hbook', husers'⟩ := run_answered (config := config) v (pre.map Prod.fst)
  have hfilter : ∀ k, (pre.map Prod.fst).filter (·.name = k) =
      if k = x.name then pre.map Prod.fst else [] := fun k => by
    have hpre : ∀ p ∈ pre.map Prod.fst, p.name = x.name := fun p hp => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact hname q (by simp [hq])
    split
    · next hk => exact List.filter_eq_self.mpr fun p hp => by simp [hk, hpre p hp]
    · next hk => exact List.filter_eq_nil_iff.mpr fun p hp => by simpa [hpre p hp] using Ne.symm hk
  refine ⟨w.filter (·.1.name ≠ x.name) ++ post, answered config v.users (pre.map Prod.fst) ++ [x],
    ⟨?_, fun k => ?_⟩, ?_, ?_⟩
  · simp [Service.run_append, spec_step, step_eq, husers', hfilter, hmsg, hbook', hbook]
  · rw [filter_regroup w post (fun p hp => hname p (by simp [hp])) k]
    simp only [Service.run_append, Service.run_singleton, spec_step, step_eq, ledger_sends,
      List.append_nil]
    split
    · next hk =>
      subst hk
      simp only [update_self, husers', hfilter, ↓reduceIte]
      rw [update_of_ne _ _ (by simp)]
      exact hpost
    · next hk =>
      rw [update_of_ne _ _ hk, update_of_ne _ _ (by simp), husers', hfilter,
        linkMsgs_erase_of_ne (by simpa using Ne.symm hk)]
      simpa [hk, record] using husers k
  · have hreg := held_regroup (n := x.name) w post
    rw [hys] at hreg
    have hsub := Multiset.coe_le.mpr
      (answered_sublist (config := config) v.users (pre.map Prod.fst)).subperm
    simp only [account, ledger_sends, List.filterMap_nil, asked_ledger, Option.toList_none,
      Multiset.coe_nil, zero_add]
    simp only [List.map_append, List.map_cons, ← Multiset.coe_add, ← Multiset.cons_coe,
      ← Multiset.singleton_add, Multiset.coe_nil, add_zero] at hreg ⊢
    refine (add_le_add le_rfl (add_le_add hsub le_rfl)).trans_eq
      (add_right_cancel (b := ↑(post.map Prod.fst)) ?_)
    rw [← hreg]
    abel
  · simp [account, ledger_sends, Service.run_append, spec_step, step_eq, husers', hfilter, hmsg,
      hbook', hbook, ← Multiset.coe_add]

/-- A message lost from a user's link unmarks the request it was for. -/
theorem moves_drop {c : SysState (system N C config)} {m : LedgerMsg N} :
    (account config).Moves (spec N C config) c
      { c with net := c.net.erase ⟨some (.user n), .ledger, m⟩ } := by
  refine .of_le fun w v ⟨hbook, husers⟩ => ?_
  obtain ⟨ys, hmap, hys⟩ := decideAll_erase (config := config) (n := n) m (v.users n)
    (w.filter (·.1.name = n))
  have hname : ∀ p ∈ ys, p.1.name = n := fun p hp => by
    obtain ⟨q, hq, hpq⟩ := List.mem_map.mp (hmap ▸ List.mem_map_of_mem hp : p.1 ∈ _)
    simpa [hpq] using (List.mem_filter.mp hq).2
  refine ⟨w.filter (·.1.name ≠ n) ++ ys, ⟨hbook, fun k => ?_⟩, ?_, ?_⟩
  · rw [filter_regroup w ys hname k]
    split
    · next hk =>
      subst hk
      rw [hys, husers k, linkMsgs_erase_self]
    · next hk =>
      rw [linkMsgs_erase_of_ne (by simpa using Ne.symm hk)]
      exact husers k
  · have hreg := held_regroup (n := n) w ys
    rw [hmap] at hreg
    exact add_le_add (Multiset.coe_le.mpr (List.erase_sublist.filterMap _).subperm)
      (le_of_eq (add_right_cancel hreg))
  · simp [Account.owed, account]

/-- The ledger crashes: what is on a link that does not lose is gone, and its requests are
unmarked. -/
theorem moves_crash (c : SysState (system N C config)) :
    (account config).Moves (spec N C config) c (c.down env .ledger) := by
  refine .of_le fun w v ⟨hbook, husers⟩ =>
    ⟨w.map fun p => (p.1, p.2 && (env.link (some (.user p.1.name)) .ledger).lossy),
      ⟨hbook, fun k => ?_⟩, ?_, ?_⟩
  · have hmap : (w.filter (·.1.name = k)).map
        (fun p => (p.1, p.2 && (env.link (some (.user p.1.name)) .ledger).lossy)) =
        (w.filter (·.1.name = k)).map
          (fun p => (p.1, p.2 && (env.link (some (.user k)) .ledger).lossy)) :=
      List.map_congr_left fun p hp => by simp [of_decide_eq_true (List.mem_filter.mp hp).2]
    simp only [List.filter_map, Function.comp_def]
    rw [hmap, decideAll_mark, husers k, linkMsgs_down]
    simp [SysState.down]
  · simp only [Account.pending, account, SysState.down, List.map_map, Function.comp_def]
    exact add_le_add (Multiset.coe_le.mpr (List.filter_sublist.filterMap _).subperm) le_rfl
  · simp [Account.owed, account, SysState.down]

/-- What is in flight is a request on its way to its user, or what a user tells the ledger. -/
theorem sent_cases (hc : Untimed config) {e : Envelope (sig N C)}
    (h : (system N C config).Sent e) :
    (∃ x : Request N C, e = ⟨none, .user x.name, .ask x.req x.ask⟩) ∨
      ∃ n m, e = ⟨some (.user n), .ledger, m⟩ := by
  cases h with
  | accept x => exact .inl ⟨x, rfl⟩
  | @step i s msg _ he =>
    cases i with
    | user n =>
      cases msg with
      | ask =>
        simp [system, user, tell_viaLedger, timerEffects_untimed hc] at he
        exact .inr ⟨n, _, he⟩
      | unlock | expire =>
        simp only [system, user] at he
        split at he <;> simp [notice] at he
        exact .inr ⟨n, _, he⟩
    | ledger => cases msg <;> simp [system, ledger] at he
  | @recover i s _ he => cases i <;> simp [system, user, ledger, rearm_untimed hc] at he

theorem implements (hc : Untimed config) (env : EnvModel (sig N C))
    (hlink : ∀ n, (env.link (some (.user n)) .ledger).ordered = true ∧
      (env.link (some (.user n)) .ledger).duplicating = false)
    (hin : ∀ n, (env.link none (.user n)).duplicating = false) :
    (system N C config).Implements env (spec N C config) := by
  refine (account config).implements (inv := fun _ => True) (fun _ _ => trivial)
    ⟨[], ⟨rfl, fun _ => rfl⟩, by simp [Account.pending, account, SysState.init, SysState.blank],
      by simp [Account.owed, account, SysState.init, SysState.blank]⟩
    (fun x => ⟨congrArg some (Request.ofAsk_eq x), rfl⟩)
    (fun c w v x _ ⟨hbook, husers⟩ => ⟨hbook, fun n => by simpa using husers n⟩)
    ?_ ?_ ?_ ?_ (fun _ _ _ _ h _ => (unarmed hc h).elim) ?_
  · intro c e _ hsent hd
    rcases sent_cases hc hsent with ⟨x, rfl⟩ | ⟨n, m, rfl⟩
    · exact moves_decide hc x (SysState.mem_of_deliverable hd)
    · exact moves_serve (hlink n).1 hd
  · intro c e _ hsent _ hdup
    rcases sent_cases hc hsent with ⟨x, rfl⟩ | ⟨n, m, rfl⟩
    · simp [hin] at hdup
    · simp [(hlink n).2] at hdup
  · intro c e _ hsent _ _
    rcases sent_cases hc hsent with ⟨x, rfl⟩ | ⟨n, m, rfl⟩
    · exact .of_loses ⟨rfl, List.erase_sublist, fun _ _ h => h, rfl⟩
        fun w v ⟨hbook, husers⟩ => ⟨hbook, fun n => by
          rw [linkMsgs_erase_of_ne (by simp)]
          exact husers n⟩
    · exact moves_drop
  · intro c i _
    cases i with
    | ledger => exact moves_crash c
    | user n =>
      exact .of_loses (SysState.Loses.down env c _) fun w v ⟨hbook, husers⟩ =>
        ⟨hbook, fun k => by simpa [linkMsgs_down] using husers k⟩
  · intro c i _
    cases i with
    | user n =>
      exact .quiet (fun _ _ h => by simpa using h) (by rw [rearm_untimed hc]; rfl)
        (by rw [rearm_untimed hc]; rfl)
    | ledger => exact .quiet (fun _ _ h => by simpa using h) rfl rfl

end Ledger
