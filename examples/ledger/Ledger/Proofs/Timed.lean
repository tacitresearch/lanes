import Ledger.Proofs.Refines

/-!
# The ledger is its timed spec

With timers, for every configuration and every environment in which each user's link to the
ledger is ordered and neither loses nor duplicates, no request is handed to a user twice and the
ledger does not crash, the system implements its spec with its deadlines, a lock lifting and a
session ending passing as the ledger serves the user's notice of them (`implements_timed`).
Requests may be lost and reordered on the way in, and users may crash.

The simulation is the one of `Ledger.Proofs.Refines` with the user's timers among its decisions.
The witness is what each user has decided and the ledger has not served, in order: requests,
and deadlines its timers marked (`Item`). The spec's record of a user, with that user's items
applied in order, gives the user's record and the messages on its link to the ledger (`steps`).
A timer that finds its deadline no longer armed changes nothing and tells nothing, so the
ledger reaches the next message past it. Serving a request is that request taking effect;
serving a notice is its deadline passing, armed in the spec because it was armed in the record
the user had when it sent the notice.

A notice lost would be a deadline that never passes in the spec though the user acted on it,
which is why no message on the link may be lost and the ledger may not crash
(`Check.lean` finds the run in which a crash of the ledger loses one).
-/

namespace Ledger

open Lanes

variable {N C : Type}

/-- Whose deadline it is. -/
def Deadline.name : Deadline N → N
  | .unlock n | .expire n _ => n

/-- The timer of a user that marks a deadline. -/
def Deadline.timer : Deadline N → UserMsg C
  | .unlock _ => .unlock
  | .expire _ session => .expire session

/-- What a user decides, in order: a request, or a deadline one of its timers marks. -/
inductive Item (N C : Type) where
  | ask (x : Request N C)
  | pass (d : Deadline N)

namespace Item

/-- The user who decides it. -/
def name : Item N C → N
  | .ask x => x.name
  | .pass d => d.name

/-- The request it is, if it is one. -/
def request? : Item N C → Option (Request N C)
  | .ask x => some x
  | .pass _ => none

/-- What the user handles to decide it. -/
def msg : Item N C → UserMsg C
  | .ask x => .ask x.req x.ask
  | .pass d => d.timer

end Item

variable [DecidableEq N] [DecidableEq C]

/-- The deadline is armed in its user's record `u`. -/
def Deadline.armedIn (u : Option (Profile C)) : Deadline N → Bool
  | .unlock _ => u.any (·.attempts.locked)
  | .expire _ session => u.any (·.sessions.live session)

/-- The record `u` after the deadline passes. -/
def Deadline.fireIn (u : Option (Profile C)) : Deadline N → Option (Profile C)
  | .unlock _ => User.unlock u
  | .expire _ session => User.expire session u

/-- What user `n` does with an item from its record `u`: the record after, and what it tells
the ledger. -/
def Item.apply (config : Config N) (n : N) (u : Option (Profile C)) :
    Item N C → Option (Profile C) × List (LedgerMsg N)
  | .ask x => ((User.decide config n x.req u x.ask).1,
      [(User.decide config n x.req u x.ask).2.1.msg n x.req])
  | .pass d => if d.armedIn u then (d.fireIn u, [d.notice]) else (u, [])

/-- User `n`'s record after its items in order from `u`, and what it told the ledger. -/
def steps (config : Config N) (n : N) :
    Option (Profile C) → List (Item N C) → Option (Profile C) × List (LedgerMsg N)
  | u, [] => (u, [])
  | u, it :: its =>
    ((steps config n (it.apply config n u).1 its).1,
      (it.apply config n u).2 ++ (steps config n (it.apply config n u).1 its).2)

variable {config : Config N} {n : N}

omit [DecidableEq N] in
theorem steps_concat (u : Option (Profile C)) (ys : List (Item N C)) (it : Item N C) :
    steps config n u (ys ++ [it]) =
      ((it.apply config n (steps config n u ys).1).1,
        (steps config n u ys).2 ++ (it.apply config n (steps config n u ys).1).2) := by
  induction ys generalizing u with
  | nil => simp [steps]
  | cons y ys ih => simp [steps, ih]

omit [DecidableEq N] in
/-- An item tells the ledger one message, or nothing and leaves the record as it was; a request
always tells one. -/
theorem Item.apply_cases (u : Option (Profile C)) (it : Item N C) :
    ((it.apply config n u).2 = [] ∧ (it.apply config n u).1 = u ∧ it.request? = none) ∨
      ∃ m, (it.apply config n u).2 = [m] := by
  cases it with
  | ask x => exact .inr ⟨_, rfl⟩
  | pass d =>
    by_cases h : d.armedIn u = true
    · exact .inr ⟨d.notice, by simp [Item.apply, h]⟩
    · exact .inl ⟨by simp [Item.apply, h], by simp [Item.apply, h], rfl⟩

omit [DecidableEq N] in
/-- The first message on the link is told for the first item that tells one: those before it
told nothing and left the record as it was. -/
theorem steps_eq_cons {u : Option (Profile C)} {ys : List (Item N C)} {s : Option (Profile C)}
    {m : LedgerMsg N} {rest : List (LedgerMsg N)} (h : steps config n u ys = (s, m :: rest)) :
    ∃ pre it post, ys = pre ++ it :: post ∧ (∀ p ∈ pre, p.request? = none) ∧
      (it.apply config n u).2 = [m] ∧ steps config n (it.apply config n u).1 post = (s, rest) := by
  induction ys with
  | nil => simp [steps] at h
  | cons y ys ih =>
    rcases Item.apply_cases (config := config) (n := n) u y with ⟨hnil, hu, hreq⟩ | ⟨m', hm'⟩
    · simp only [steps, hnil, hu, List.nil_append] at h
      obtain ⟨pre, it, post, rfl, hpre, hit, hpost⟩ := ih h
      exact ⟨y :: pre, it, post, rfl, by simpa [hreq] using hpre, hit, hpost⟩
    · simp only [steps, hm', List.singleton_append, Prod.mk.injEq, List.cons.injEq] at h
      obtain ⟨hs, rfl, hrest⟩ := h
      exact ⟨[], y, ys, rfl, nofun, hm', Prod.ext hs hrest⟩

omit [DecidableEq N] [DecidableEq C] in
/-- A request tells the ledger an answer or what to serve, never a notice. -/
theorem Verdict.msg_ne_notice (self : N) (req : ReqId) (v : Verdict N) (d : Deadline N) :
    v.msg self req ≠ d.notice := by
  cases v <;> cases d <;> simp [Verdict.msg, Deadline.notice]

omit [DecidableEq N] [DecidableEq C] in
theorem Deadline.notice_inj {d d' : Deadline N} (h : d.notice = d'.notice) : d = d' := by
  cases d <;> cases d' <;> simp_all [Deadline.notice]

/-- Serving a notice is its deadline passing. -/
theorem delivered_notice (d : Deadline N) :
    delivered (N := N) (C := C) .atLedger .ledger d.notice = some d := by
  cases d <;> rfl

theorem spec_armed (v : SpecState N C) (d : Deadline N) :
    (spec N C config).armed v d = d.armedIn (v.users d.name) := by
  cases d <;> rfl

theorem spec_fire (v : SpecState N C) (d : Deadline N) :
    (spec N C config).fire v d =
      (⟨update v.users d.name (d.fireIn (v.users d.name)), v.book⟩, []) := by
  cases d <;> rfl

/-! What a user's step does is what applying its item does. -/

theorem sends_timerEffects (self : N) (timers : Timers) :
    Effect.sends (σ := sig N C) (Id.user self) (timerEffects (C := C) config self timers) = [] := by
  simp only [timerEffects, Effect.sends_append]
  refine List.append_eq_nil_iff.mpr ⟨List.append_eq_nil_iff.mpr ⟨?_, ?_⟩, ?_⟩
  · split
    · cases config.lockout_ms <;> rfl
    · rfl
  · split <;> rfl
  · simp [Effect.sends, List.filterMap_map]

theorem emits_timerEffects (self : N) (timers : Timers) :
    Effect.emits (σ := sig N C) (timerEffects (C := C) config self timers) = [] := by
  simp only [timerEffects, Effect.emits_append]
  refine List.append_eq_nil_iff.mpr ⟨List.append_eq_nil_iff.mpr ⟨?_, ?_⟩, ?_⟩
  · split
    · cases config.lockout_ms <;> rfl
    · rfl
  · split <;> rfl
  · simp [Effect.emits, List.filterMap_map]

/-- The effects of `user n` handling an item: what the item tells the ledger, and timers. -/
theorem user_item (it : Item N C) (u : Option (Profile C)) :
    ((user config .viaLedger it.name).step u it.msg).1 = (it.apply config it.name u).1 ∧
      Effect.sends (σ := sig N C) (Id.user it.name) ((user config .viaLedger it.name).step u it.msg).2 =
        (it.apply config it.name u).2.map
          (fun m => (⟨some (Id.user it.name), Id.ledger, m⟩ : Envelope (sig N C))) ∧
      Effect.emits (σ := sig N C) ((user config .viaLedger it.name).step u it.msg).2 = [] := by
  cases it with
  | ask x =>
    simp [user, Item.apply, Item.msg, Item.name, tell_viaLedger, sends_timerEffects,
      emits_timerEffects]
  | pass d =>
    cases d with
    | unlock k =>
      by_cases h : u.any (·.attempts.locked) = true
      · simp [user, Item.apply, Item.msg, Item.name, Deadline.timer, Deadline.name,
          Deadline.armedIn, Deadline.fireIn, h, notice]
      · simp [user, Item.apply, Item.msg, Item.name, Deadline.timer, Deadline.name,
          Deadline.armedIn, h]
    | expire k session =>
      by_cases h : u.any (·.sessions.live session) = true
      · simp [user, Item.apply, Item.msg, Item.name, Deadline.timer, Deadline.name,
          Deadline.armedIn, Deadline.fireIn, h, notice]
      · simp [user, Item.apply, Item.msg, Item.name, Deadline.timer, Deadline.name,
          Deadline.armedIn, h]

theorem linkMsgs_map_self (k : N) (l : List (LedgerMsg N)) :
    linkMsgs (some (Id.user k)) Id.ledger
      (l.map fun m => (⟨some (Id.user k), Id.ledger, m⟩ : Envelope (sig N C))) = l := by
  induction l with
  | nil => rfl
  | cons m l ih => simp [ih]

/-- The standard simulation, with what the users decided and the ledger has not served as the
witness. -/
def timedAccount (config : Config N) :
    Lanes.Account (system N C config) (SpecState N C) (List (Item N C)) where
  pend := asked
  held _ w := ↑(w.filterMap Item.request?)
  value state net w v := v.book = state .ledger ∧ ∀ n,
    steps config n (v.users n) (w.filter (·.name = n)) =
      (state (.user n), linkMsgs (some (Id.user n)) Id.ledger net)

omit [DecidableEq C] in
/-- The witness with user `n`'s items replaced by `ys`. -/
theorem Item.filter_regroup (w ys : List (Item N C)) (hys : ∀ p ∈ ys, p.name = n) (k : N) :
    (w.filter (·.name ≠ n) ++ ys).filter (·.name = k) =
      if k = n then ys else w.filter (·.name = k) := by
  split
  · next hk =>
    subst hk
    have hself : ys.filter (·.name = k) = ys := List.filter_eq_self.mpr fun p hp => by
      simp [hys p hp]
    rw [List.filter_append, hself, List.filter_filter]
    simp
  · next hk =>
    have hnil : ys.filter (·.name = k) = [] :=
      List.filter_eq_nil_iff.mpr fun p hp => by simpa [hys p hp] using Ne.symm hk
    rw [List.filter_append, hnil, List.append_nil, List.filter_filter]
    exact List.filter_congr fun p _ => by by_cases h : p.name = k <;> simp [h, hk]

omit [DecidableEq C] in
theorem Item.held_regroup (w ys : List (Item N C)) :
    (↑((w.filter (·.name ≠ n) ++ ys).filterMap Item.request?) : Bag (Request N C)) +
        ↑((w.filter (·.name = n)).filterMap Item.request?) =
      ↑(w.filterMap Item.request?) + ↑(ys.filterMap Item.request?) := by
  have hw : (w.filter (·.name ≠ n) ++ w.filter (·.name = n)).Perm w := by
    simpa using List.perm_append_comm.trans
      (List.filter_append_perm (fun p : Item N C => decide (p.name = n)) w)
  rw [← Bag.coe_eq_coe.mpr (hw.filterMap Item.request?)]
  simp only [List.filterMap_append, ← Bag.coe_add]
  ac_rfl

variable {env : EnvModel (sig N C)}

/-- A user decides an item: it joins the witness, and the user's link carries what it told. -/
theorem value_decide {state : (i : Id N) → (system N C config).State i}
    {net net₀ : List (Envelope (sig N C))} {w : List (Item N C)} {v : SpecState N C}
    (it : Item N C) (hv : (timedAccount config).value state net w v)
    (hnet : ∀ k, linkMsgs (some (Id.user k)) Id.ledger net₀ =
      linkMsgs (some (Id.user k)) Id.ledger net) :
    (timedAccount config).value
      (update state (.user it.name) (it.apply config it.name (state (.user it.name))).1)
      (net₀ ++ (it.apply config it.name (state (.user it.name))).2.map
        fun m => (⟨some (Id.user it.name), Id.ledger, m⟩ : Envelope (sig N C))) (w ++ [it]) v := by
  obtain ⟨hbook, husers⟩ := hv
  refine ⟨by simpa using hbook, fun k => ?_⟩
  rw [linkMsgs_append, hnet]
  by_cases hk : k = it.name
  · subst hk
    rw [List.filter_append, filter_singleton]
    simp only [decide_true, Bool.cond_true]
    rw [steps_concat, husers]
    simp only [update_self, List.append_cancel_left_eq, Prod.mk.injEq, true_and]
    exact (linkMsgs_map_self (C := C) _ _).symm
  · rw [List.filter_append, filter_singleton]
    have hk' : ¬it.name = k := Ne.symm hk
    simp only [hk', decide_false, Bool.cond_false, List.append_nil]
    rw [update_of_ne _ _ (by simpa using hk), husers, linkMsgs_sends_of_ne' hk, List.append_nil]
where
  linkMsgs_sends_of_ne' {k k' : N} (h : k ≠ k') (l : List (LedgerMsg N)) :
      linkMsgs (some (Id.user k)) Id.ledger
        (l.map fun m => (⟨some (Id.user k'), Id.ledger, m⟩ : Envelope (sig N C))) = [] :=
    List.filterMap_eq_nil_iff.mpr fun e he => by
      obtain ⟨m, -, rfl⟩ := List.mem_map.mp he
      exact Envelope.on_of_ne fun hl => h (by simpa using hl.1.symm)

/-- A user decides a request: it joins the witness. -/
theorem moves_decide_timed {c : SysState (system N C config)} (x : Request N C)
    (hmem : (⟨none, .user x.name, .ask x.req x.ask⟩ : Envelope (sig N C)) ∈ c.net) :
    (timedAccount config).Moves (spec N C config) c
      (({ c with net := c.net.erase ⟨none, .user x.name, .ask x.req x.ask⟩ }).grow (.user x.name)
        (((system N C config).actor (.user x.name)).step (c.state (.user x.name))
          (.ask x.req x.ask))) := by
  obtain ⟨hstate, hsends, hemits⟩ :=
    user_item (config := config) (Item.ask x) (c.state (.user x.name))
  simp only [Item.name, Item.msg] at hstate hsends hemits
  refine .handle hmem fun w v hv => ⟨w ++ [.ask x], [], ?_, ?_, ?_⟩
  · have hv' := value_decide (Item.ask x) hv (net₀ := c.net.erase _)
      (fun k => linkMsgs_erase_of_ne
        (e := (⟨none, .user x.name, .ask x.req x.ask⟩ : Envelope (sig N C))) (by simp) _)
    simp only [Item.name] at hv'
    show (timedAccount config).value
      (update c.state (.user x.name)
        ((user config .viaLedger x.name).step (c.state (.user x.name)) (.ask x.req x.ask)).1)
      (c.net.erase _ ++ Effect.sends (σ := sig N C) (Id.user x.name)
        ((user config .viaLedger x.name).step (c.state (.user x.name)) (.ask x.req x.ask)).2)
      (w ++ [Item.ask x]) v
    rw [hstate, hsends]
    exact hv'
  · show ↑((Effect.sends (σ := sig N C) (Id.user x.name)
        ((user config .viaLedger x.name).step (c.state (Id.user x.name))
          (UserMsg.ask x.req x.ask)).2).filterMap asked) +
      (↑((w ++ [Item.ask x]).filterMap Item.request?) : Bag (Request N C)) +
        ↑([] : List (Request N C)) ≤
      ↑(asked (⟨none, Id.user x.name, UserMsg.ask x.req x.ask⟩ : Envelope (sig N C))).toList +
        ↑(w.filterMap Item.request?)
    rw [hsends]
    simp only [asked, Request.ofAsk_eq, List.filterMap_append, List.filterMap_cons,
      List.filterMap_nil, Item.request?, List.filterMap_map, Function.comp_def]
    simp
    exact Bag.le_of_eq (Bag.coe_eq_coe.mpr (List.perm_append_singleton _ _))
  · show ↑(Effect.emits (σ := sig N C)
        ((user config .viaLedger x.name).step (c.state (Id.user x.name))
          (UserMsg.ask x.req x.ask)).2) +
      ↑((Effect.sends (σ := sig N C) (Id.user x.name)
        ((user config .viaLedger x.name).step (c.state (Id.user x.name))
          (UserMsg.ask x.req x.ask)).2).filterMap fun _ => (none : Option (Response N))) +
        (0 : Bag (Response N)) ≤ _
    rw [hemits]
    simp

/-- A user's timer marks a deadline: it joins the witness, as an item that tells the ledger
nothing if the deadline is no longer armed. -/
theorem moves_timer (c : SysState (system N C config)) (d : Deadline N) :
    (timedAccount config).Moves (spec N C config) c
      (c.grow (.user d.name)
        (((system N C config).actor (.user d.name)).step (c.state (.user d.name)) d.timer)) := by
  obtain ⟨hstate, hsends, hemits⟩ :=
    user_item (config := config) (Item.pass d) (c.state (.user d.name))
  simp only [Item.name, Item.msg] at hstate hsends hemits
  refine .grow fun w v hv => ⟨w ++ [.pass d], [], ?_, ?_, ?_⟩
  · have hv' := value_decide (Item.pass d) hv (net₀ := c.net) (fun _ => rfl)
    simp only [Item.name] at hv'
    show (timedAccount config).value
      (update c.state (.user d.name)
        ((user config .viaLedger d.name).step (c.state (.user d.name)) d.timer).1)
      (c.net ++ Effect.sends (σ := sig N C) (Id.user d.name)
        ((user config .viaLedger d.name).step (c.state (.user d.name)) d.timer).2)
      (w ++ [Item.pass d]) v
    rw [hstate, hsends]
    exact hv'
  · show ↑((Effect.sends (σ := sig N C) (Id.user d.name)
        ((user config .viaLedger d.name).step (c.state (Id.user d.name)) d.timer).2).filterMap
          asked) +
      (↑((w ++ [Item.pass d]).filterMap Item.request?) : Bag (Request N C)) +
        ↑([] : List (Request N C)) ≤
      ↑(none : Option (Request N C)).toList + ↑(w.filterMap Item.request?)
    rw [hsends]
    simp [Item.request?, List.filterMap_map, asked_ledger, List.filterMap_append,
      List.filterMap_cons, Function.comp_def]
  · show ↑(Effect.emits (σ := sig N C)
        ((user config .viaLedger d.name).step (c.state (Id.user d.name)) d.timer).2) +
      ↑((Effect.sends (σ := sig N C) (Id.user d.name)
        ((user config .viaLedger d.name).step (c.state (Id.user d.name)) d.timer).2).filterMap
          fun _ => (none : Option (Response N))) + (0 : Bag (Response N)) ≤ _
    rw [hemits]
    simp

omit [DecidableEq N] [DecidableEq C] in
theorem held_pre {pre : List (Item N C)} (h : ∀ p ∈ pre, p.request? = none) :
    pre.filterMap Item.request? = [] :=
  List.filterMap_eq_nil_iff.mpr h

theorem ledger_notice (b : Book N) (d : Deadline N) :
    (ledger (C := C) config).step b d.notice = (b, []) := by
  cases d <;> rfl

/-- The ledger serves a request on a user's link: the first item of the user's that told the
ledger something is that request, and it takes effect. -/
theorem moves_serve_timed (hord : (env.link (some (.user n)) .ledger).ordered = true)
    {c : SysState (system N C config)} {m : LedgerMsg N} (hm : ∀ d : Deadline N, m ≠ d.notice)
    (hd : c.deliverable env ⟨some (.user n), .ledger, m⟩ = true) :
    (timedAccount config).Moves (spec N C config) c
      (({ c with net := c.net.erase ⟨some (.user n), .ledger, m⟩ }).grow .ledger
        ((ledger config).step (c.state .ledger) m)) := by
  refine .handle (SysState.mem_of_deliverable hd) fun w v ⟨hbook, husers⟩ => ?_
  have hn := husers n
  rw [linkMsgs_of_deliverable hord hd] at hn
  obtain ⟨pre, it, post, hys, hpre, hit, hpost⟩ := steps_eq_cons hn
  have hname : ∀ p ∈ pre ++ it :: post, p.name = n := fun p hp => by
    rw [← hys] at hp
    simpa using (List.mem_filter.mp hp).2
  cases it with
  | pass d =>
    exfalso
    simp only [Item.apply] at hit
    split at hit
    · exact hm d (List.singleton_inj.mp hit).symm
    · cases hit
  | ask x =>
    obtain rfl : x.name = n := hname (.ask x) (by simp)
    simp only [Item.apply, List.singleton_inj] at hit hpost
    subst hit
    have hsplit : (pre ++ Item.ask x :: post).filterMap Item.request? =
        x :: post.filterMap Item.request? := by
      simp [List.filterMap_append, held_pre hpre, Item.request?]
    have hheld := Item.held_regroup (n := x.name) w post
    rw [hys, hsplit, ← Bag.cons_coe, ← Bag.singleton_add] at hheld
    have key : (↑((w.filter (·.name ≠ x.name) ++ post).filterMap Item.request?) :
        Bag (Request N C)) + {x} = ↑(w.filterMap Item.request?) :=
      Bag.add_right_cancel (u := ↑(post.filterMap Item.request?)) (by rw [← hheld]; ac_rfl)
    refine ⟨w.filter (·.name ≠ x.name) ++ post, [x], ⟨?_, fun k => ?_⟩, ?_, ?_⟩
    · simp [Service.run_singleton, spec_step, step_eq, hbook]
    · rw [Item.filter_regroup w post (fun p hp => hname p (by simp [hp])) k]
      simp only [Service.run_singleton, spec_step, step_eq]
      split
      · next hk =>
        subst hk
        simp only [update_self]
        rw [update_of_ne _ _ (by simp), linkMsgs_append, ledger_sends, linkMsgs_nil,
          List.append_nil]
        exact hpost
      · next hk =>
        rw [update_of_ne _ _ hk, update_of_ne _ _ (by simp), linkMsgs_append, ledger_sends,
          linkMsgs_nil, List.append_nil, linkMsgs_erase_of_ne (by simpa using Ne.symm hk)]
        exact husers k
    · simp only [timedAccount, ledger_sends, List.filterMap_nil, Bag.coe_nil, Bag.zero_add,
        asked_ledger, Option.toList_none, Bag.coe_singleton]
      exact Bag.le_of_eq key
    · simp [timedAccount, ledger_sends, Service.run_singleton, spec_step, step_eq, hbook]

/-- The ledger serves a notice on a user's link: the first item of the user's that told the
ledger something is that deadline, armed in the spec's record, and it passes. -/
theorem fires_notice (hord : (env.link (some (.user n)) .ledger).ordered = true)
    {c : SysState (system N C config)} (d : Deadline N)
    (hd : c.deliverable env ⟨some (.user n), .ledger, d.notice⟩ = true) :
    (timedAccount config).Fires (spec N C config) d c
      (({ c with net := c.net.erase ⟨some (.user n), .ledger, d.notice⟩ }).grow .ledger
        ((ledger config).step (c.state .ledger) d.notice)) := by
  refine .handle (SysState.mem_of_deliverable hd) fun w v ⟨hbook, husers⟩ => ?_
  have hn := husers n
  rw [linkMsgs_of_deliverable hord hd] at hn
  obtain ⟨pre, it, post, hys, hpre, hit, hpost⟩ := steps_eq_cons hn
  have hname : ∀ p ∈ pre ++ it :: post, p.name = n := fun p hp => by
    rw [← hys] at hp
    simpa using (List.mem_filter.mp hp).2
  cases it with
  | ask x =>
    exfalso
    exact Verdict.msg_ne_notice _ _ _ d (List.singleton_inj.mp hit)
  | pass d' =>
    simp only [Item.apply] at hit hpost
    split at hit
    · next harmed =>
      obtain rfl : d = d' := (Deadline.notice_inj (List.singleton_inj.mp hit)).symm
      simp only [harmed, ite_true] at hpost
      obtain rfl : d.name = n := hname (.pass d) (by simp)
      have hsplit : (pre ++ Item.pass d :: post).filterMap Item.request? =
          post.filterMap Item.request? := by
        simp [List.filterMap_append, held_pre hpre, Item.request?, List.filterMap_cons]
      have hheld := Item.held_regroup (n := d.name) w post
      rw [hys, hsplit] at hheld
      have key : (↑((w.filter (·.name ≠ d.name) ++ post).filterMap Item.request?) :
          Bag (Request N C)) = ↑(w.filterMap Item.request?) :=
        Bag.add_right_cancel (u := ↑(post.filterMap Item.request?)) hheld
      refine ⟨w.filter (·.name ≠ d.name) ++ post, [], ?_, ⟨?_, fun k => ?_⟩, ?_, ?_⟩
      · simpa [spec_armed] using harmed
      · simp [spec_fire, ledger_notice, hbook]
      · rw [Item.filter_regroup w post (fun p hp => hname p (by simp [hp])) k]
        simp only [Service.run_nil, spec_fire]
        split
        · next hk =>
          subst hk
          simp only [update_self]
          rw [update_of_ne _ _ (by simp), ledger_notice, linkMsgs_append]
          simpa using hpost
        · next hk =>
          rw [update_of_ne _ _ hk, update_of_ne _ _ (by simp), ledger_notice, linkMsgs_append,
            linkMsgs_erase_of_ne (by simpa using Ne.symm hk)]
          simpa using husers k
      · simp only [timedAccount, ledger_notice, Effect.sends_nil, List.filterMap_nil,
          Bag.coe_nil, Bag.zero_add, Bag.add_zero, asked_ledger, Option.toList_none]
        exact Bag.le_of_eq key
      · simp [timedAccount, ledger_notice, spec_fire]
    · cases hit

/-! The cases of the simulation. -/

/-- What is in flight is a request on its way to its user, or what a user tells the ledger. -/
theorem sent_cases_timed {e : Envelope (sig N C)} (h : (system N C config).Sent e) :
    (∃ x : Request N C, e = ⟨none, .user x.name, .ask x.req x.ask⟩) ∨
      ∃ n m, e = ⟨some (.user n), .ledger, m⟩ := by
  cases h with
  | accept x => exact .inl ⟨x, rfl⟩
  | @step i s msg _ he =>
    cases i with
    | user n =>
      cases msg with
      | ask =>
        simp [system, user, tell_viaLedger, sends_timerEffects] at he
        exact .inr ⟨n, _, he⟩
      | unlock | expire =>
        simp only [system, user] at he
        split at he <;> simp [notice] at he
        exact .inr ⟨n, _, he⟩
    | ledger => cases msg <;> simp [system, ledger] at he
  | @recover i s _ he =>
    cases i with
    | user n => exact absurd (Effect.mem_sends.mp he).2 (not_send_rearm config n s)
    | ledger => simp [system, ledger] at he

theorem not_after_ask_timerEffects (self : N) (timers : Timers) {delay_ms : Nat} {req : ReqId}
    {ask : Ask C} : Effect.after delay_ms (UserMsg.ask req ask) ∉ timerEffects config self timers := by
  simp only [timerEffects, List.mem_append, List.mem_map, not_or]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · split
    · cases config.lockout_ms <;> simp
    · simp
  · split <;> simp
  · simp

theorem not_after_ask_rearm (self : N) (u : Option (Profile C)) {delay_ms : Nat} {req : ReqId}
    {ask : Ask C} : Effect.after delay_ms (UserMsg.ask req ask) ∉ rearm config self u := by
  cases u with
  | none => simp [rearm]
  | some p =>
    simp only [rearm, List.mem_append, not_or]
    refine ⟨not_after_ask_timerEffects self _, ?_⟩
    split <;> simp

/-- A timer of a user that marks a deadline. -/
def IsTimer : (i : Id N) → (sig N C).Msg i → Prop
  | .user _, .ask .. => False
  | .user _, _ => True
  | .ledger, _ => False

/-- A user's timers mark deadlines; no step arms a request, and the ledger has no timers. -/
theorem armed_isTimer {i : Id N} {m : (sig N C).Msg i} (h : (system N C config).Armed i m) :
    IsTimer i m := by
  cases h with
  | step s msg h =>
    cases i with
    | ledger => cases msg <;> simp [system, ledger] at h
    | user n =>
      cases m with
      | unlock | expire => trivial
      | ask req ask =>
        cases msg with
        | ask =>
          simp only [system, user, List.mem_cons] at h
          rcases h with h | h
          · rw [tell_viaLedger] at h
            cases h
          · exact not_after_ask_timerEffects n _ h
        | unlock | expire =>
          simp only [system, user] at h
          split at h <;> simp [notice] at h
  | recover s h =>
    cases i with
    | ledger => simp [system, ledger] at h
    | user n =>
      cases m with
      | unlock | expire => trivial
      | ask req ask => exact not_after_ask_rearm n s h

theorem ledger_not_stops : ¬(system N C config).Stops .ledger := by
  rintro ⟨s, h | ⟨msg, h⟩⟩
  · simp [system, ledger] at h
  · cases msg <;> simp [system, ledger, Effect.isStop] at h

theorem emits_rearm (self : N) (u : Option (Profile C)) :
    Effect.emits (σ := sig N C) (rearm config self u) = [] := by
  cases u with
  | none => rfl
  | some p =>
    simp only [rearm, Effect.emits_append, emits_timerEffects, List.nil_append]
    split <;> simp [Effect.emits_map]

theorem sends_rearm (self : N) (u : Option (Profile C)) :
    Effect.sends (σ := sig N C) (.user self) (rearm config self u) = [] :=
  List.eq_nil_iff_forall_not_mem.mpr fun _ he =>
    not_send_rearm config self u (Effect.mem_sends.mp he).2

/-- With its timers, the system implements its spec with its deadlines, each passing as the
ledger serves the user's notice of it, for every configuration and every environment in which
each user's link to the ledger is ordered and neither loses nor duplicates, no request is
handed to a user twice, and the ledger does not crash. -/
theorem implements_timed (config : Config N) (env : EnvModel (sig N C))
    (hlink : ∀ n, (env.link (some (.user n)) .ledger).ordered = true ∧
      (env.link (some (.user n)) .ledger).duplicating = false ∧
      (env.link (some (.user n)) .ledger).lossy = false)
    (hin : ∀ n, (env.link none (.user n)).duplicating = false)
    (hcrash : env.mayCrash .ledger = false) :
    (system N C config).Implements env (spec N C config) (deadlines .atLedger)
      (delivered .atLedger) := by
  refine (timedAccount config).implements_timed (inv := fun _ => True) (fun _ _ => trivial)
    ⟨[], ⟨rfl, fun _ => rfl⟩, by simp [Account.pending, timedAccount, SysState.init, SysState.blank],
      by simp [Account.owed, timedAccount, SysState.init, SysState.blank]⟩
    (fun x => ⟨congrArg some (Request.ofAsk_eq x), rfl⟩)
    (fun c w v x _ ⟨hbook, husers⟩ => ⟨hbook, fun n => by simpa using husers n⟩)
    ?_ ?_ ?_ ?_ ?_ ?_
  · intro c e _ hsent hd
    rcases sent_cases_timed hsent with ⟨x, rfl⟩ | ⟨n, m, rfl⟩
    · exact moves_decide_timed x (SysState.mem_of_deliverable hd)
    · cases m with
      | answer req r =>
        exact moves_serve_timed (hlink n).1 (fun d h => by cases d <;> cases h) hd
      | serve req owner op =>
        exact moves_serve_timed (hlink n).1 (fun d h => by cases d <;> cases h) hd
      | unlocked k => exact fires_notice (hlink n).1 (.unlock k) hd
      | ended k session => exact fires_notice (hlink n).1 (.expire k session) hd
  · intro c e _ hsent _ hdup
    rcases sent_cases_timed hsent with ⟨x, rfl⟩ | ⟨n, m, rfl⟩
    · simp [hin] at hdup
    · simp [(hlink n).2.1] at hdup
  · intro c e _ hsent _ hlossy
    rcases sent_cases_timed hsent with ⟨x, rfl⟩ | ⟨n, m, rfl⟩
    · exact .of_loses ⟨rfl, List.erase_sublist, fun _ _ h => h, rfl⟩
        fun w v ⟨hbook, husers⟩ => ⟨hbook, fun n => by
          rw [linkMsgs_erase_of_ne (by simp)]
          exact husers n⟩
    · simp [(hlink n).2.2] at hlossy
  · intro c i hi
    cases i with
    | ledger =>
      exfalso
      rcases hi with h | h
      · simp [hcrash] at h
      · exact ledger_not_stops h
    | user n =>
      exact .of_loses (SysState.Loses.down env c _) fun w v ⟨hbook, husers⟩ =>
        ⟨hbook, fun k => by simpa [linkMsgs_down] using husers k⟩
  · intro c i msg _ harmed _
    cases i with
    | ledger => exact (armed_isTimer harmed).elim
    | user n =>
      cases msg with
      | ask req a => exact (armed_isTimer harmed).elim
      | unlock => exact moves_timer c (.unlock n)
      | expire session => exact moves_timer c (.expire n session)
  · intro c i _
    cases i with
    | user n =>
      exact .quiet (fun _ _ h => by simpa using h) (sends_rearm n _) (emits_rearm n _)
    | ledger => exact .quiet (fun _ _ h => by simpa using h) rfl rfl

/-- One shard's kernel meets every premise of `implements_timed`: its links are reliable and
ordered, and no actor crashes but by stopping itself, which the ledger never does. A process that
dies is not a crash of the semantics: it starts again from its journal as the kernel the
journal's requests lead to (`Journal.recover_kernel`). -/
theorem implements_timed_kernel (config : Config N) :
    (system N C config).Implements Kernel.env (spec N C config) (deadlines .atLedger)
      (delivered .atLedger) :=
  implements_timed config Kernel.env (fun _ => ⟨rfl, rfl, rfl⟩) (fun _ => rfl) rfl

/-- Whatever a shell does with one shard's kernel, the events it reports, but for the starts that
bring actors at rest back, are a run of the system that the spec explains as a sequential
history in real-time order. -/
theorem kernel_history [Hashable (sig N C).Id] (config : Config N)
    (ops : List (Kernel.Op (sig N C))) :
    ∃ evs c, (SysState.init (system N C config) Kernel.env).run Kernel.env evs = some c ∧
      Event.awake evs = Event.awake ((Kernel.boot (system N C config)).2.map .output ++
        ((Kernel.boot (system N C config)).1.exec ops).events) ∧
      ∃ acts cut, System.Implements.Explains (spec N C config) (deadlines .atLedger)
        (delivered .atLedger) evs acts cut := by
  obtain ⟨evs, c, hrun, hawake, -⟩ := (Kernel.exec_reachable (system N C config) ops).1
  exact ⟨evs, c, hrun, hawake, (implements_timed_kernel config).history hrun⟩

end Ledger
