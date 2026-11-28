/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Services.Postgres.Conn
public import Lanes.Services.Postgres.MessageSound

/-!
What a connection to PostgreSQL promises, for every configuration and every sequence of events:

- replies answer the requests sent, in the order they were sent, each once (`Conn.run_fifo`);
- a request is sent only when the connection is open, as the request it was submitted as, and
  only one the server reads back (`Conn.step_query`);
- `committed` is answered only to a `COMMIT` the server answered `COMMIT` without an error, from a
  transaction in progress that had not failed, with a `ReadyForQuery` that then says idle
  (`Conn.step_committed`, from `Conn.outcome_committed`);
- after SCRAM, the connection goes on only once the server's signature is the password's, and an
  `AuthenticationOk` before that closes it (`Conn.onMessage_saslFinal`, `Conn.onMessage_sasl_authOk`);
- with a password and `requireScram` (the default), the connection is authenticated only after
  SCRAM and the server's signature: `AuthenticationOk` at once, cleartext and MD5 close it
  (`Conn.onMessage_requireScram`);
- a connection that ends or breaks answers every request in flight `unknown` (`Conn.step_lost`);
  a closed connection does nothing but refuse (`Conn.step_closed`);
- no more requests are in flight than `inflight_max` (`Conn.run_queue`).
-/

@[expose] public section

namespace Lanes.Postgres.Conn

variable (cfg : Config)

/-- The numbers of the requests whose bytes are sent. -/
def queries (actions : List Action) : List Nat :=
  actions.filterMap fun | .query id _ => some id | _ => none

/-- The numbers of the requests answered, refusals aside: a refused request is never sent. -/
def answers (actions : List Action) : List Nat :=
  actions.filterMap fun
    | .reply _ (.refused _) => none
    | .reply id _ => some id
    | _ => none

def ids (c : Conn) : List Nat := c.queue.map (·.id)

/-- One step answers requests from the front of those in flight, and adds those it sends at the
back. -/
def Fifo (c : Conn) (r : Conn × List Action) : Prop :=
  ids c ++ queries r.2 = answers r.2 ++ ids r.1

@[simp] theorem queries_nil : queries [] = [] := rfl
@[simp] theorem answers_nil : answers [] = [] := rfl

@[simp] theorem queries_append (a b : List Action) : queries (a ++ b) = queries a ++ queries b := by
  simp [queries]

@[simp] theorem answers_append (a b : List Action) : answers (a ++ b) = answers a ++ answers b := by
  simp [answers]

@[simp] theorem queries_send (b : ByteArray) : queries [.send b] = [] := rfl
@[simp] theorem answers_send (b : ByteArray) : answers [.send b] = [] := rfl
@[simp] theorem queries_close (w : Closing) : queries [.close w] = [] := rfl
@[simp] theorem answers_close (w : Closing) : answers [.close w] = [] := rfl
@[simp] theorem queries_opened : queries [.opened] = [] := rfl
@[simp] theorem answers_opened : answers [.opened] = [] := rfl
@[simp] theorem queries_reply (id : Nat) (r : Reply) : queries [.reply id r] = [] := rfl

theorem queries_unknown (q : List Pending) :
    queries (q.map fun p => Action.reply p.id .unknown) = [] := by
  induction q with
  | nil => rfl
  | cons p q ih => simp [queries]

theorem answers_unknown (q : List Pending) :
    answers (q.map fun p => Action.reply p.id .unknown) = q.map (·.id) := by
  induction q with
  | nil => rfl
  | cons p q ih => simpa [answers] using ih

theorem answers_reply {id : Nat} {r : Reply} (h : ∀ why, r ≠ .refused why) :
    answers [.reply id r] = [id] := by
  cases r <;> simp_all [answers]

theorem outcome_ne_refused (p : Pending) (before after : TxStatus) (why : Refusal) :
    outcome cfg p before after ≠ .refused why := by
  unfold outcome
  repeat' split
  all_goals simp

theorem fail_fifo (c : Conn) (why : Closing) : Fifo c (fail c why) := by
  simp [Fifo, fail, ids, queries_unknown, answers_unknown]

theorem same_fifo (c c' : Conn) (h : ids c' = ids c) (actions : List Action)
    (hq : queries actions = []) (ha : answers actions = []) : Fifo c (c', actions) := by
  simp [Fifo, h, hq, ha]

theorem onReply_fifo (c : Conn) (p : Pending) (rest : List Pending) (hq : c.queue = p :: rest)
    (m : Backend) : Fifo c (onReply cfg c p rest m) := by
  cases m <;> simp only [onReply] <;> (try split) <;> (try split) <;>
    first
    | exact fail_fifo c _
    | exact same_fifo c _ (by simp [ids, hq]) [] rfl rfl
    | (simp [Fifo, ids, hq, answers_reply (outcome_ne_refused cfg _ _ _)]; done)

theorem onMessage_fifo (c : Conn) (m : Backend) : Fifo c (onMessage cfg c m) := by
  unfold onMessage
  split
  case h_7 =>
    split
    · rename_i p rest hq
      exact onReply_fifo cfg c p rest hq m
    · cases m <;> (try simp only []) <;> first | exact fail_fifo c _ | exact same_fifo c _ rfl _ rfl rfl
  all_goals
    (try unfold onAuth) <;> (try unfold onSasl) <;> (try unfold onSaslFinal) <;> cases m <;>
      (try simp only []) <;> (repeat' split) <;>
      first | exact fail_fifo c _ | exact same_fifo c _ rfl _ rfl rfl

theorem drain_fifo (fuel : Nat) (c : Conn) : Fifo c (drain cfg fuel c) := by
  induction fuel generalizing c with
  | zero => exact same_fifo c c rfl [] rfl rfl
  | succ fuel ih =>
    unfold drain
    split
    · exact same_fifo c c rfl [] rfl rfl
    · split
      · exact same_fifo c c rfl [] rfl rfl
      · exact fail_fifo c _
      · split
        · exact fail_fifo c _
        · rename_i next _ _ m _
          have h1 := onMessage_fifo cfg { c with pos := next } m
          have h2 := ih (onMessage cfg { c with pos := next } m).1
          simp only [Fifo, ids] at h1 h2 ⊢
          simp only [queries_append, answers_append, ← List.append_assoc]
          rw [h1, List.append_assoc, h2, List.append_assoc]

theorem submit_fifo (id : Nat) (r : Request) (c : Conn) : Fifo c (submit cfg id r c) := by
  unfold submit
  repeat' split
  all_goals first
    | exact same_fifo c c rfl _ rfl rfl
    | simp [Fifo, ids, queries, answers]

/-- Before TLS, bytes leave the connection as it is, close it, or start the handshake. -/
theorem beforeTls_cases (c : Conn) (bytes : ByteArray) :
    beforeTls c bytes = (c, []) ∨ (∃ why, beforeTls c bytes = fail c why)
      ∨ beforeTls c bytes = ({ c with phase := .handshake }, [.startTls]) := by
  unfold beforeTls
  split
  · split
    · exact .inl rfl
    · exact .inr (.inl ⟨_, rfl⟩)
  · split
    · exact .inl rfl
    · exact .inr (.inr rfl)
    · exact .inr (.inl ⟨_, rfl⟩)
    · exact .inr (.inl ⟨_, rfl⟩)

/-- The end of the handshake closes the connection, or sends the start-up. -/
theorem secure_cases (c : Conn) (endPoint : Option ByteArray) (selected : ByteArray) :
    (∃ why, secure cfg c endPoint selected = fail c why)
      ∨ (c.phase = .handshake ∧ alpnOk cfg selected = true
        ∧ secure cfg c endPoint selected
          = ({ c with phase := .startup, endPoint }, [.send (startup cfg).encode])) := by
  unfold secure
  split
  · exact .inl ⟨_, rfl⟩
  · split
    · exact .inl ⟨_, rfl⟩
    · rename_i h1 h2
      exact .inr ⟨Classical.not_not.mp h1, by simpa using h2, rfl⟩

theorem mem_beforeTls {c : Conn} {bytes : ByteArray} {a : Action} (h : a ∈ (beforeTls c bytes).2) :
    (∃ why, a ∈ (fail c why).2) ∨ a = .startTls := by
  rcases beforeTls_cases c bytes with e | ⟨w, e⟩ | e <;> rw [e] at h
  · simp at h
  · exact .inl ⟨w, h⟩
  · exact .inr (by simpa using h)

theorem mem_secure {c : Conn} {endPoint : Option ByteArray} {selected : ByteArray} {a : Action}
    (h : a ∈ (secure cfg c endPoint selected).2) :
    (∃ why, a ∈ (fail c why).2) ∨ a = .send (startup cfg).encode := by
  rcases secure_cases cfg c endPoint selected with ⟨w, e⟩ | ⟨_, _, e⟩ <;> rw [e] at h
  · exact .inl ⟨w, h⟩
  · exact .inr (by simpa using h)

theorem step_fifo (c : Conn) (e : Event) : Fifo c (step cfg c e) := by
  cases e with
  | submit id r => exact submit_fifo cfg id r c
  | received bytes =>
    simp only [step]
    split
    · exact same_fifo c c rfl _ rfl rfl
    · split
      · rcases beforeTls_cases c bytes with e | ⟨w, e⟩ | e <;> rw [e]
        · exact same_fifo c c rfl _ rfl rfl
        · exact fail_fifo c _
        · exact same_fifo c _ rfl _ rfl rfl
      · split
        · exact fail_fifo c _
        · exact drain_fifo cfg _ (receive bytes c)
  | secured p a =>
    simp only [step]
    split
    · exact same_fifo c c rfl _ rfl rfl
    · rcases secure_cases cfg c p a with ⟨w, e⟩ | ⟨_, _, e⟩ <;> rw [e]
      · exact fail_fifo c _
      · exact same_fifo c _ rfl _ rfl rfl
  | stop =>
    simp only [step]
    split
    · exact same_fifo c c rfl _ rfl rfl
    · split
      · exact fail_fifo c _
      · have := fail_fifo c .stopped
        simp only [Fifo] at this ⊢
        simpa [queries, answers] using this
  | _ =>
    simp only [step]
    split
    · exact same_fifo c c rfl _ rfl rfl
    · exact fail_fifo c _

/-- Replies answer the requests sent, in the order they were sent: what was in flight and what
a run sends are what it answers and what is left in flight, in that order. -/
theorem run_fifo (c : Conn) (events : List Event) :
    ids c ++ queries (run cfg c events).2 = answers (run cfg c events).2 ++ ids (run cfg c events).1 := by
  induction events generalizing c with
  | nil => simp [run]
  | cons e rest ih =>
    have h1 := step_fifo cfg c e
    have h2 := ih (step cfg c e).1
    simp only [Fifo] at h1
    simp only [run, queries_append, answers_append, ← List.append_assoc]
    rw [h1, List.append_assoc, h2, List.append_assoc]

/-! ## Only a `COMMIT` that committed is reported committed -/

/-- `committed` is the outcome only of a `COMMIT` the server answered `COMMIT` without an error,
from a transaction in progress that had not failed, and that left it idle. -/
theorem outcome_committed {p : Pending} {before after : TxStatus}
    (h : outcome cfg p before after = .committed) :
    p.kind = .commit ∧ p.error = none ∧ p.tag = some "COMMIT" ∧ before = .inTx ∧ after = .idle := by
  unfold outcome at h
  split at h
  · cases h
  · rename_i herr
    split at h
    · split at h
      · rename_i hk hc
        exact ⟨hk, herr, hc.1, hc.2.1, hc.2.2⟩
      · cases h
    · cases h
    · split at h <;> cases h

theorem not_mem_fail_committed {c : Conn} {why : Closing} {id : Nat} :
    .reply id .committed ∉ (fail c why).2 := by
  simp [fail]

/-- The conditions under which a message makes the connection answer `committed`: it is a
`ReadyForQuery` that says idle, the connection is open and the state the last one reported is a
transaction in progress, and the request at the front of those in flight is a `COMMIT` the
server answered `COMMIT` without an error. -/
def Commits (c : Conn) (m : Backend) (id : Nat) : Prop :=
  c.phase = .ready ∧ m = .readyForQuery .idle ∧ c.status = .inTx ∧
    ∃ p rest, c.queue = p :: rest ∧ p.id = id ∧ p.kind = .commit ∧ p.tag = some "COMMIT"
      ∧ p.error = none

theorem onReply_committed {c : Conn} {p : Pending} {rest : List Pending} {m : Backend} {id : Nat}
    (h : .reply id .committed ∈ (onReply cfg c p rest m).2) :
    m = .readyForQuery .idle ∧ c.status = .inTx ∧ p.id = id ∧ p.kind = .commit
      ∧ p.tag = some "COMMIT" ∧ p.error = none := by
  cases m <;> (try simp only [onReply] at h) <;> (try split at h) <;> (try split at h) <;>
    first
    | exact absurd h not_mem_fail_committed
    | simp at h
    | skip
  rename_i status
  obtain ⟨hid, hout⟩ := h
  obtain ⟨hk, herr, htag, hbefore, hafter⟩ := outcome_committed cfg hout.symm
  exact ⟨by rw [hafter], hbefore, hid.symm, hk, htag, herr⟩

theorem onMessage_committed {c : Conn} {m : Backend} {id : Nat}
    (h : .reply id .committed ∈ (onMessage cfg c m).2) : Commits c m id := by
  unfold onMessage at h
  split at h
  case h_7 hphase =>
    split at h
    · rename_i p rest hq
      obtain ⟨hm, hs, hid, hk, htag, herr⟩ := onReply_committed cfg h
      exact ⟨hphase, hm, hs, p, rest, hq, hid, hk, htag, herr⟩
    · cases m <;> simp only at h <;> first | exact absurd h not_mem_fail_committed | simp at h
  all_goals
    (try unfold onAuth at h) <;> (try unfold onSasl at h) <;> (try unfold onSaslFinal at h) <;>
      cases m <;> (try simp only at h) <;> (repeat' split at h) <;>
      first | exact absurd h not_mem_fail_committed | simp at h

/-- `c'` is what the connection becomes from `c` by receiving bytes and reading messages. -/
inductive Reads : Conn → Conn → Prop where
  | refl (c : Conn) : Reads c c
  | receive {c c' : Conn} (bytes : ByteArray) : Reads c c' → Reads c (receive bytes c')
  | message {c c' : Conn} (next : Nat) (m : Backend) :
      Reads c c' → Reads c (onMessage cfg { c' with pos := next } m).1

theorem Reads.trans {a b d : Conn} (h : Reads cfg a b) (h' : Reads cfg b d) : Reads cfg a d := by
  induction h' with
  | refl => exact h
  | receive bytes _ ih => exact .receive bytes ih
  | message next m _ ih => exact .message next m ih

/-- Some message read, from a connection reached by reading, made it answer `committed`. -/
def Answered (c : Conn) (id : Nat) : Prop :=
  ∃ c' next m, Reads cfg c c' ∧ Commits { c' with pos := next } m id

theorem drain_committed (fuel : Nat) (c : Conn) {id : Nat}
    (h : .reply id .committed ∈ (drain cfg fuel c).2) : Answered cfg c id := by
  induction fuel generalizing c with
  | zero => simp [drain] at h
  | succ fuel ih =>
    unfold drain at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · exact absurd h not_mem_fail_committed
      · split at h
        · exact absurd h not_mem_fail_committed
        · rename_i next _ _ m _
          simp only [List.mem_append] at h
          rcases h with h | h
          · exact ⟨c, next, m, .refl c, onMessage_committed cfg h⟩
          · obtain ⟨c', next', m', hr, hc⟩ := ih _ h
            exact ⟨c', next', m', Reads.trans cfg (.message next m (.refl c)) hr, hc⟩

/-- A step answers `committed` only through a message it read that makes it so (`Commits`):
a `ReadyForQuery` saying idle, read while the state the server last reported was a transaction
in progress and the request at the front was a `COMMIT` the server answered `COMMIT` without an
error. -/
theorem step_committed (c : Conn) (e : Event) {id : Nat}
    (h : .reply id .committed ∈ (step cfg c e).2) : Answered cfg c id := by
  cases e with
  | submit i r =>
    simp only [step, submit] at h
    repeat' split at h
    all_goals simp at h
  | received bytes =>
    simp only [step] at h
    split at h
    · simp at h
    · split at h
      · rcases mem_beforeTls h with ⟨_, h⟩ | h
        · exact absurd h not_mem_fail_committed
        · cases h
      · split at h
        · exact absurd h not_mem_fail_committed
        · obtain ⟨c', next, m, hr, hc⟩ := drain_committed cfg _ _ h
          exact ⟨c', next, m, Reads.trans cfg (.receive bytes (.refl c)) hr, hc⟩
  | secured p a =>
    simp only [step] at h
    split at h
    · simp at h
    · rcases mem_secure cfg h with ⟨_, h⟩ | h
      · exact absurd h not_mem_fail_committed
      · cases h
  | stop =>
    simp only [step] at h
    split at h
    · simp at h
    · split at h
      · exact absurd h not_mem_fail_committed
      · simp only [List.mem_cons, reduceCtorEq, false_or] at h
        exact absurd h not_mem_fail_committed
  | _ =>
    simp only [step] at h
    split at h
    · simp at h
    · exact absurd h not_mem_fail_committed

/-! ## What is sent -/

theorem not_mem_fail_query {c : Conn} {why : Closing} {id : Nat} {b : ByteArray} :
    .query id b ∉ (fail c why).2 := by
  simp [fail]

theorem onMessage_query {c : Conn} {m : Backend} {id : Nat} {b : ByteArray} :
    .query id b ∉ (onMessage cfg c m).2 := by
  intro h
  unfold onMessage at h
  split at h
  case h_7 =>
    split at h
    · unfold onReply at h
      cases m <;> (try simp only at h) <;> (repeat' split at h) <;>
        first | exact not_mem_fail_query h | simp at h
    · cases m <;> (try simp only at h) <;> first | exact not_mem_fail_query h | simp at h
  all_goals
    (try unfold onAuth at h) <;> (try unfold onSasl at h) <;> (try unfold onSaslFinal at h) <;>
      cases m <;> (try simp only at h) <;> (repeat' split at h) <;>
      first | exact not_mem_fail_query h | simp at h

theorem drain_query (fuel : Nat) (c : Conn) {id : Nat} {b : ByteArray} :
    .query id b ∉ (drain cfg fuel c).2 := by
  induction fuel generalizing c with
  | zero => simp [drain]
  | succ fuel ih =>
    unfold drain
    split
    · simp
    · split
      · simp
      · exact not_mem_fail_query
      · split
        · exact not_mem_fail_query
        · simp only [List.mem_append, not_or]
          exact ⟨onMessage_query cfg, ih _⟩

/-- A request's bytes are sent only when it is submitted, to an open connection, as the bytes of
that request, and only if each of its messages is within its bounds and `message_max`. -/
theorem step_query (c : Conn) (e : Event) {id : Nat} {b : ByteArray}
    (h : .query id b ∈ (step cfg c e).2) :
    c.phase = .ready ∧ ∃ r, e = .submit id r ∧ b = Request.encode r ∧ valid cfg r = true := by
  cases e with
  | submit i r =>
    simp only [step, submit] at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · rename_i hready _ hvalid
          simp only [List.mem_singleton, Action.query.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨Classical.not_not.mp hready, r, rfl, rfl, by simpa using hvalid⟩
  | received bytes =>
    simp only [step] at h
    split at h
    · simp at h
    · split at h
      · rcases mem_beforeTls h with ⟨_, h⟩ | h
        · exact absurd h not_mem_fail_query
        · cases h
      · split at h
        · exact absurd h not_mem_fail_query
        · exact absurd h (drain_query cfg _ _)
  | secured p a =>
    simp only [step] at h
    split at h
    · simp at h
    · rcases mem_secure cfg h with ⟨_, h⟩ | h
      · exact absurd h not_mem_fail_query
      · cases h
  | stop =>
    simp only [step] at h
    split at h
    · simp at h
    · split at h
      · exact absurd h not_mem_fail_query
      · simp only [List.mem_cons, reduceCtorEq, false_or] at h
        exact absurd h not_mem_fail_query
  | _ =>
    simp only [step] at h
    split at h
    · simp at h
    · exact absurd h not_mem_fail_query

/-- Every message of a request sent is read by the server as that message. -/
theorem valid_decode {r : Request} (h : valid cfg r = true) :
    ∀ m ∈ Request.messages r, Frontend.decode m.expect m.encode = some m := by
  intro m hm
  simp only [valid, List.all_eq_true] at h
  have := h m hm
  simp only [fits, Bool.and_eq_true, decide_eq_true_eq] at this
  exact Frontend.decode_encode m this.1.1 this.2

/-! ## Closing -/

/-- A closed connection stays as it is, and answers a request only by refusing it. -/
theorem step_closed (c : Conn) (e : Event) (h : c.phase = .closed) :
    (step cfg c e).1 = c ∧ ∀ a ∈ (step cfg c e).2, ∃ id, a = .reply id (.refused .notReady) := by
  cases e with
  | submit i r => simp [step, submit, h]
  | _ => simp [step, h]

/-- A connection that ends or breaks answers every request in flight `unknown`, and closes. -/
theorem step_lost (c : Conn) (h : c.phase ≠ .closed) (e : Event) (why : Closing)
    (he : e = .ended ∧ why = .ended ∨ e = .broken ∧ why = .broken) :
    (step cfg c e).1.phase = .closed ∧ (step cfg c e).1.queue = [] ∧
      (step cfg c e).2 = c.queue.map (fun p => .reply p.id .unknown) ++ [.close why] := by
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [step, h, fail]

/-! ## Bounds -/

theorem fail_queue (c : Conn) (why : Closing) : (fail c why).1.queue = [] := rfl

theorem onMessage_queue (c : Conn) (m : Backend) :
    (onMessage cfg c m).1.queue.length ≤ c.queue.length := by
  unfold onMessage
  split
  case h_7 =>
    split
    · rename_i p rest hq
      unfold onReply
      cases m <;> (try simp only) <;> (repeat' split) <;> simp [fail, hq]
    · cases m <;> (try simp only) <;> simp [fail]
  all_goals
    (try unfold onAuth) <;> (try unfold onSasl) <;> (try unfold onSaslFinal) <;>
      cases m <;> (try simp only) <;> (repeat' split) <;> simp [fail]

theorem drain_queue (fuel : Nat) (c : Conn) : (drain cfg fuel c).1.queue.length ≤ c.queue.length := by
  induction fuel generalizing c with
  | zero => simp [drain]
  | succ fuel ih =>
    unfold drain
    split
    · simp
    · split
      · simp
      · simp [fail]
      · split
        · simp [fail]
        · rename_i next _ _ m _
          exact Nat.le_trans (ih _) (onMessage_queue cfg { c with pos := next } m)

theorem step_queue (c : Conn) (e : Event) (h : c.queue.length ≤ cfg.inflight_max) :
    (step cfg c e).1.queue.length ≤ cfg.inflight_max := by
  cases e with
  | submit i r =>
    simp only [step, submit]
    repeat' split
    all_goals simp_all
    omega
  | received bytes =>
    simp only [step]
    split
    · exact h
    · split
      · rcases beforeTls_cases c bytes with e | ⟨w, e⟩ | e <;> rw [e] <;> simp [fail, h]
      · split
        · simp [fail]
        · exact Nat.le_trans (drain_queue cfg _ _) h
  | secured p a =>
    simp only [step]
    split
    · exact h
    · rcases secure_cases cfg c p a with ⟨w, e⟩ | ⟨_, _, e⟩ <;> rw [e] <;> simp [fail, h]
  | stop =>
    simp only [step]
    split
    · exact h
    · split <;> simp [fail]
  | _ =>
    simp only [step]
    split
    · exact h
    · simp [fail]

/-- No more than `inflight_max` requests are ever in flight. -/
theorem run_queue (c : Conn) (events : List Event) (h : c.queue.length ≤ cfg.inflight_max) :
    (run cfg c events).1.queue.length ≤ cfg.inflight_max := by
  induction events generalizing c with
  | nil => simpa [run] using h
  | cons e rest ih => exact ih _ (step_queue cfg c e h)

theorem start_queue : (start cfg).1.queue = [] := by
  dsimp only [start]
  split
  · rfl
  · split <;> rfl

theorem onMessage_buffer (c : Conn) (m : Backend) :
    (onMessage cfg c m).1.buffer = c.buffer ∧ (onMessage cfg c m).1.pos = c.pos := by
  unfold onMessage
  split
  case h_7 =>
    split
    · unfold onReply
      cases m <;> (try simp only) <;> (repeat' split) <;> simp [fail]
    · cases m <;> (try simp only) <;> simp [fail]
  all_goals
    (try unfold onAuth) <;> (try unfold onSasl) <;> (try unfold onSaslFinal) <;>
      cases m <;> (try simp only) <;> (repeat' split) <;> simp [fail]

theorem drain_buffer (fuel : Nat) (c : Conn) {bound : Nat} (h : c.buffer.size - c.pos ≤ bound) :
    (drain cfg fuel c).1.buffer.size - (drain cfg fuel c).1.pos ≤ bound := by
  induction fuel generalizing c with
  | zero => simpa [drain] using h
  | succ fuel ih =>
    unfold drain
    split
    · exact h
    · split
      · exact h
      · exact h
      · split
        · exact h
        · rename_i _ _ next hread _ m _
          obtain ⟨hpos, _, _⟩ := Frame.read_done hread
          obtain ⟨hb, hp⟩ := onMessage_buffer cfg { c with pos := next } m
          apply ih
          rw [hb, hp]
          simp only
          omega

/-- The bytes held and not yet read stay within `message_max + 1`: the reader never waits on more
(`Frame.read_more`), and the loop is asked for no more than `room`. -/
theorem step_buffer (c : Conn) (e : Event) (h : c.buffer.size - c.pos ≤ cfg.message_max + 1) :
    (step cfg c e).1.buffer.size - (step cfg c e).1.pos ≤ cfg.message_max + 1 := by
  cases e with
  | submit i r =>
    simp only [step, submit]
    repeat' split
    all_goals exact h
  | received bytes =>
    simp only [step]
    split
    · exact h
    · split
      · rcases beforeTls_cases c bytes with e | ⟨w, e⟩ | e <;> rw [e] <;> exact h
      · split
        · exact h
        · rename_i _ _ hroom
          apply drain_buffer
          simp only [receive, room] at hroom ⊢
          split
          · rename_i hz
            rw [ByteArray.size_append]
            omega
          · rw [ByteArray.size_append, ByteArray.size_extract]
            omega
  | secured p a =>
    simp only [step]
    split
    · exact h
    · rcases secure_cases cfg c p a with ⟨w, e⟩ | ⟨_, _, e⟩ <;> rw [e] <;> exact h
  | stop =>
    simp only [step]
    split
    · exact h
    · split <;> exact h
  | _ =>
    simp only [step]
    split
    · exact h
    · exact h

/-! ## Authentication -/

/-- After SCRAM's last message, the connection goes on only once the server's answer carries the
signature of the password. -/
theorem onMessage_saslFinal {c : Conn} {signature : ByteArray} {m : Backend}
    (hc : c.phase = .saslFinal signature) (h : (onMessage cfg c m).1.phase = .saslDone) :
    ∃ data final, m = .authSaslFinal data ∧ String.fromUTF8? data = some final
      ∧ Scram.verify signature final = true := by
  unfold onMessage at h
  rw [hc] at h
  simp only at h
  unfold onSaslFinal at h
  cases m <;> (try simp only at h) <;> (repeat' split at h) <;> (try simp [fail] at h)
  · rename_i data _ final hfinal hverify
    exact ⟨data, final, rfl, hfinal, hverify⟩
  · simp [hc] at h

/-- With `requireScram` and a password, a connection that has not finished SCRAM goes on only to
another phase before the server's proof, or closes, or reaches `saslDone` from SCRAM's last
message, by `Scram.verify` of the server's signature: so it is `authed`, and opens, only after
the server proved it knows the password (`onMessage_saslFinal`). An `AuthenticationOk` at once,
or a request for a cleartext password or an MD5 digest, closes it. -/
theorem onMessage_requireScram (hs : cfg.scramOnly = true) {c : Conn} {m : Backend}
    (hc : c.phase = .startup ∨ (∃ b, c.phase = .sasl b) ∨ ∃ s, c.phase = .saslFinal s) :
    ((onMessage cfg c m).1.phase = .closed ∨ (onMessage cfg c m).1.phase = .startup
        ∨ (∃ b, (onMessage cfg c m).1.phase = .sasl b)
        ∨ ∃ s, (onMessage cfg c m).1.phase = .saslFinal s)
      ∨ ((onMessage cfg c m).1.phase = .saslDone ∧ ∃ s data final, c.phase = .saslFinal s
          ∧ m = .authSaslFinal data ∧ String.fromUTF8? data = some final
          ∧ Scram.verify s final = true) := by
  simp only [Config.scramOnly, Bool.and_eq_true, Option.isSome_iff_exists] at hs
  obtain ⟨hr, pw, hpw⟩ := hs
  rcases hc with hc | ⟨b, hc⟩ | ⟨s, hc⟩
  · left
    simp only [onMessage, hc]
    unfold onAuth
    cases m <;> (try simp only) <;> (repeat' split) <;> simp_all [fail, Config.scramOnly]
  · left
    simp only [onMessage, hc]
    unfold onSasl
    cases m <;> (try simp only) <;> (repeat' split) <;> simp_all [fail]
  · by_cases hd : (onMessage cfg c m).1.phase = .saslDone
    · obtain ⟨data, final, h1, h2, h3⟩ := onMessage_saslFinal cfg hc hd
      exact .inr ⟨hd, s, data, final, hc, h1, h2, h3⟩
    · left
      simp only [onMessage, hc] at hd ⊢
      unfold onSaslFinal at hd ⊢
      cases m <;> (try simp only at hd ⊢) <;> (repeat' split) <;> simp_all [fail]

/-- A server that says `AuthenticationOk` before it has proved it knows the password, once SCRAM
has begun, is not trusted: the connection closes. -/
theorem onMessage_sasl_authOk {c : Conn}
    (hc : (∃ b, c.phase = .sasl b) ∨ ∃ s, c.phase = .saslFinal s) :
    onMessage cfg c .authOk = fail c .signature := by
  rcases hc with ⟨b, hc⟩ | ⟨s, hc⟩ <;> simp [onMessage, hc, onSasl, onSaslFinal]

/-- The connection reports itself open only on the server's first `ReadyForQuery` after it
authenticated. -/
theorem onMessage_opened {c : Conn} {m : Backend} (h : .opened ∈ (onMessage cfg c m).2) :
    c.phase = .authed ∧ ∃ s, m = .readyForQuery s := by
  unfold onMessage at h
  split at h
  case h_6 hphase =>
    cases m <;> (try simp only at h) <;> (try simp [fail] at h)
    exact ⟨hphase, _, rfl⟩
  case h_7 =>
    split at h
    · unfold onReply at h
      cases m <;> (try simp only at h) <;> (repeat' split at h) <;> simp [fail] at h
    · cases m <;> (try simp only at h) <;> simp [fail] at h
  all_goals
    (try unfold onAuth at h) <;> (try unfold onSasl at h) <;> (try unfold onSaslFinal at h) <;>
      cases m <;> (try simp only at h) <;> (repeat' split at h) <;> simp [fail] at h


theorem not_mem_fail_startTls {c : Conn} {why : Closing} : .startTls ∉ (fail c why).2 := by
  simp [fail]

theorem onMessage_startTls {c : Conn} {m : Backend} : .startTls ∉ (onMessage cfg c m).2 := by
  intro h
  unfold onMessage at h
  split at h
  case h_7 =>
    split at h
    · unfold onReply at h
      cases m <;> (try simp only at h) <;> (repeat' split at h) <;>
        first | exact not_mem_fail_startTls h | simp at h
    · cases m <;> (try simp only at h) <;> first | exact not_mem_fail_startTls h | simp at h
  all_goals
    (try unfold onAuth at h) <;> (try unfold onSasl at h) <;> (try unfold onSaslFinal at h) <;>
      cases m <;> (try simp only at h) <;> (repeat' split at h) <;>
      first | exact not_mem_fail_startTls h | simp at h

theorem drain_startTls (fuel : Nat) (c : Conn) : .startTls ∉ (drain cfg fuel c).2 := by
  induction fuel generalizing c with
  | zero => simp [drain]
  | succ fuel ih =>
    unfold drain
    split
    · simp
    · split
      · simp
      · exact not_mem_fail_startTls
      · split
        · exact not_mem_fail_startTls
        · simp only [List.mem_append, not_or]
          exact ⟨onMessage_startTls cfg, ih _⟩

/-! ## TLS first -/

/-- The bytes the connection sends: of the start-up, authentication, `Terminate`, `SSLRequest`
and requests. -/
def Action.bytes : Action → Option ByteArray
  | .send b => some b
  | .query _ b => some b
  | _ => none

def sent (actions : List Action) : List ByteArray := actions.filterMap Action.bytes

@[simp] theorem sent_append (a b : List Action) : sent (a ++ b) = sent a ++ sent b := by
  simp [sent]

theorem sent_fail (c : Conn) (why : Closing) : sent (fail c why).2 = [] := by
  simp [fail, sent, List.filterMap_eq_nil_iff, Action.bytes]

/-- Before TLS, until the IO says the handshake is done, a step sends nothing, and the connection
stays before TLS or closes. -/
theorem step_beforeTls (c : Conn) (e : Event) (hc : c.phase.beforeTls = true)
    (he : ∀ p a, e ≠ .secured p a) :
    sent (step cfg c e).2 = []
      ∧ ((step cfg c e).1.phase.beforeTls = true ∨ (step cfg c e).1.phase = .closed) := by
  have hr : c.phase ≠ .ready := by intro h; simp [h, Phase.beforeTls] at hc
  have hcl : c.phase ≠ .closed := by intro h; simp [h, Phase.beforeTls] at hc
  cases e with
  | submit i r => simp [step, submit, hr, sent, hc, Action.bytes]
  | received bytes =>
    simp only [step, hcl, hc, ↓reduceIte]
    rcases beforeTls_cases c bytes with e | ⟨w, e⟩ | e <;> rw [e]
    · simp [sent, hc]
    · exact ⟨sent_fail c w, .inr rfl⟩
    · simp [sent, Phase.beforeTls, Action.bytes]
  | secured p a => exact absurd rfl (he p a)
  | stop =>
    simp only [step, hcl, hc, ↓reduceIte]
    exact ⟨sent_fail c _, .inr rfl⟩
  | _ =>
    simp only [step, hcl, ↓reduceIte]
    exact ⟨sent_fail c _, .inr rfl⟩

theorem step_closed_sent (c : Conn) (e : Event) (h : c.phase = .closed) :
    sent (step cfg c e).2 = [] ∧ (step cfg c e).1.phase = .closed := by
  obtain ⟨hs, ha⟩ := step_closed cfg c e h
  refine ⟨?_, by rw [hs]; exact h⟩
  simp only [sent, List.filterMap_eq_nil_iff]
  intro a ha'
  obtain ⟨id, rfl⟩ := ha a ha'
  rfl

/-- From before TLS, a run of events none of which says the handshake is done sends nothing. -/
theorem run_beforeTls (c : Conn) (events : List Event)
    (hc : c.phase.beforeTls = true ∨ c.phase = .closed)
    (he : ∀ e ∈ events, ∀ p a, e ≠ .secured p a) : sent (run cfg c events).2 = [] := by
  induction events generalizing c with
  | nil => rfl
  | cons e rest ih =>
    have he' : ∀ p a, e ≠ .secured p a := he e (List.mem_cons_self ..)
    have hnext : sent (step cfg c e).2 = []
        ∧ ((step cfg c e).1.phase.beforeTls = true ∨ (step cfg c e).1.phase = .closed) := by
      rcases hc with hc | hc
      · exact step_beforeTls cfg c e hc he'
      · obtain ⟨h1, h2⟩ := step_closed_sent cfg c e hc
        exact ⟨h1, .inr h2⟩
    simp only [run, sent_append, hnext.1, List.nil_append]
    exact ih _ hnext.2 fun e h => he e (List.mem_cons_of_mem _ h)

/-- With TLS, the only bytes sent before the IO says the handshake is done are `SSLRequest`'s:
not the start-up, not a password, not a request. -/
theorem tls_first (h : cfg.encryption ≠ .plain) (events : List Event)
    (he : ∀ e ∈ events, ∀ p a, e ≠ .secured p a) :
    ∀ b ∈ sent ((start cfg).2 ++ (run cfg (start cfg).1 events).2), b = sslRequest := by
  have hs : sent (start cfg).2 ⊆ [sslRequest] ∧
      ((start cfg).1.phase.beforeTls = true ∨ (start cfg).1.phase = .closed) := by
    unfold start
    split
    · simp [sent, Action.bytes]
    · split
      · exact absurd ‹_› h
      · simp [sent, Phase.beforeTls, Action.bytes]
      · simp [sent, Phase.beforeTls, Action.bytes]
  intro b hb
  rw [sent_append, run_beforeTls cfg _ events hs.2 he, List.append_nil] at hb
  simpa using hs.1 hb

/-- The handshake starts only on an `S` alone, in answer to `SSLRequest`, or at once with direct
TLS (`start`). -/
theorem step_startTls (c : Conn) (e : Event) (h : .startTls ∈ (step cfg c e).2) :
    c.phase = .sslRequest ∧ ∃ bytes, e = .received bytes ∧ bytes.data.toList = [83] := by
  cases e with
  | submit i r =>
    simp only [step, submit] at h
    repeat' split at h
    all_goals simp at h
  | received bytes =>
    simp only [step] at h
    split at h
    · simp at h
    · split at h
      · rename_i hb
        unfold beforeTls at h
        split at h
        · split at h <;> simp [fail] at h
        · split at h
          · simp at h
          · rename_i hp _ hd
            refine ⟨?_, bytes, rfl, hd⟩
            cases hq : c.phase <;> simp_all [Phase.beforeTls]
          · simp [fail] at h
          · simp [fail] at h
      · split at h
        · simp [fail] at h
        · exact absurd h (drain_startTls cfg _ _)
  | secured p a =>
    simp only [step] at h
    split at h
    · simp at h
    · rcases mem_secure cfg h with ⟨_, h⟩ | h
      · simp [fail] at h
      · cases h
  | stop =>
    simp only [step] at h
    split at h
    · simp at h
    · split at h <;> simp [fail] at h
  | _ =>
    simp only [step] at h
    split at h
    · simp at h
    · simp [fail] at h

/-- A server that answers `SSLRequest` with `N` is refused: TLS is never given up. -/
theorem step_refusedTls (c : Conn) (bytes : ByteArray) (hc : c.phase = .sslRequest)
    (hn : bytes.data.toList.head? = some 78) :
    step cfg c (.received bytes) = fail c .refusedTls := by
  obtain ⟨rest, hr⟩ : ∃ rest, bytes.data.toList = 78 :: rest := by
    cases h : bytes.data.toList with
    | nil => simp [h] at hn
    | cons x rest => simp only [h, List.head?_cons, Option.some.injEq] at hn; exact ⟨rest, by rw [hn]⟩
  simp only [step, hc, beforeTls, Phase.beforeTls, reduceCtorEq, ↓reduceIte, hr]

/-- The start-up is sent after the handshake only when the server chose the ALPN protocol the
encryption allows. -/
theorem step_secured (c : Conn) (p : Option ByteArray) (a : ByteArray) {b : ByteArray}
    (h : .send b ∈ (step cfg c (.secured p a)).2) :
    c.phase = .handshake ∧ alpnOk cfg a = true ∧ b = (startup cfg).encode
      ∧ (step cfg c (.secured p a)).1.endPoint = p := by
  simp only [step] at h ⊢
  split at h
  · simp at h
  · rename_i hcl
    simp only [hcl, ↓reduceIte]
    rcases secure_cases cfg c p a with ⟨w, e⟩ | ⟨h1, h2, e⟩ <;> rw [e] at h ⊢
    · simp [fail] at h
    · simp only [List.mem_singleton, Action.send.injEq] at h
      exact ⟨h1, h2, h, rfl⟩

/-! ## Channel binding -/

theorem unbound_ne {mechanisms : List String} {hash : ByteArray} :
    unbound cfg mechanisms ≠ some (.endPoint hash) := by
  unfold unbound
  split
  · simp
  · split <;> simp

theorem unbound_require (hr : cfg.channelBinding = .require) (mechanisms : List String) :
    unbound cfg mechanisms = none := by
  simp [unbound, hr]

/-- SCRAM is bound to a certificate's hash only with TLS, when the server offers
`SCRAM-SHA-256-PLUS`, and to the hash the handshake gave. -/
theorem choose_endPoint {c : Conn} {mechanisms : List String} {hash : ByteArray}
    (h : choose cfg c mechanisms = some (.endPoint hash)) :
    c.endPoint = some hash ∧ Scram.mechanismPlus ∈ mechanisms ∧ cfg.encryption ≠ .plain := by
  unfold choose at h
  split at h
  · rename_i e he
    split at h
    · rename_i hc
      simp only [Option.some.injEq, Scram.Binding.endPoint.injEq] at h
      exact ⟨h ▸ he, hc.2.2, hc.1⟩
    · exact absurd h (unbound_ne cfg)
  · exact absurd h (unbound_ne cfg)

/-- With `channelBinding := require`, SCRAM is always bound to the certificate's hash. -/
theorem choose_require (hr : cfg.channelBinding = .require) {c : Conn} {mechanisms : List String}
    {b : Scram.Binding} (h : choose cfg c mechanisms = some b) :
    ∃ hash, b = .endPoint hash ∧ c.endPoint = some hash := by
  unfold choose at h
  split at h
  · rename_i e he
    split at h
    · exact ⟨e, (Option.some.inj h).symm, he⟩
    · simp [unbound_require cfg hr] at h
  · simp [unbound_require cfg hr] at h

/-- In SCRAM's exchange the binding is to the hash the handshake gave, and with `require` there
is one. -/
def Bound (c : Conn) : Prop :=
  ∀ b, c.phase = .sasl b → (∀ h, b = .endPoint h → c.endPoint = some h)
    ∧ (cfg.channelBinding = .require → ∃ h, b = .endPoint h)

theorem bound_of {c : Conn} (h : ∀ b, c.phase ≠ .sasl b) : Bound cfg c :=
  fun b hb => absurd hb (h b)

theorem bound_fail (c : Conn) (why : Closing) : Bound cfg (fail c why).1 :=
  bound_of cfg (by simp [fail])

theorem onMessage_bound (c : Conn) (m : Backend) (h : Bound cfg c) :
    Bound cfg (onMessage cfg c m).1 := by
  unfold onMessage
  split
  case h_1 =>
    unfold onAuth
    cases m <;> (try simp only) <;> (repeat' split) <;>
      first
      | exact h
      | exact bound_fail cfg c _
      | (apply bound_of; simp [*]; done)
      | skip
    rename_i b hb
    intro b' hb'
    cases hb'
    refine ⟨fun hash hh => ?_, fun hr => ?_⟩
    · cases hh
      exact (choose_endPoint cfg hb).1
    · exact (choose_require cfg hr hb).imp fun _ h => h.1
  case h_7 =>
    split
    · unfold onReply
      cases m <;> (try simp only) <;> (repeat' split) <;>
        first | exact h | exact bound_fail cfg c _ | (apply bound_of; simp [*]; done)
    · cases m <;> (try simp only) <;> first | exact h | exact bound_fail cfg c _
  all_goals
    (try unfold onSasl) <;> (try unfold onSaslFinal) <;>
      cases m <;> (try simp only) <;> (repeat' split) <;>
      first | exact h | exact bound_fail cfg c _ | (apply bound_of; simp [*]; done)

theorem drain_bound (fuel : Nat) (c : Conn) (h : Bound cfg c) : Bound cfg (drain cfg fuel c).1 := by
  induction fuel generalizing c with
  | zero => exact h
  | succ fuel ih =>
    unfold drain
    split
    · exact h
    · split
      · exact h
      · exact bound_fail cfg c _
      · split
        · exact bound_fail cfg c _
        · exact ih _ (onMessage_bound cfg _ _ h)

theorem step_bound (c : Conn) (e : Event) (h : Bound cfg c) : Bound cfg (step cfg c e).1 := by
  cases e with
  | submit i r =>
    simp only [step, submit]
    repeat' split
    all_goals first | exact h | exact fun b hb => h b hb
  | received bytes =>
    simp only [step]
    split
    · exact h
    · split
      · rcases beforeTls_cases c bytes with e | ⟨w, e⟩ | e <;> rw [e]
        · exact h
        · exact bound_fail cfg c _
        · (apply bound_of; simp)
      · split
        · exact bound_fail cfg c _
        · exact drain_bound cfg _ _ h
  | secured p a =>
    simp only [step]
    split
    · exact h
    · rcases secure_cases cfg c p a with ⟨w, e⟩ | ⟨_, _, e⟩ <;> rw [e]
      · exact bound_fail cfg c _
      · (apply bound_of; simp)
  | stop =>
    simp only [step]
    split
    · exact h
    · split <;> exact bound_fail cfg c .stopped
  | _ =>
    simp only [step]
    split
    · exact h
    · exact bound_fail cfg c _

/-- Over every run from the start, SCRAM's binding is to the certificate's hash that the handshake
gave (`Event.secured`), and with `channelBinding := require` it is bound. -/
theorem run_bound (events : List Event) : Bound cfg (run cfg (start cfg).1 events).1 := by
  have hs : Bound cfg (start cfg).1 := by
    apply bound_of
    unfold start
    split
    · simp
    · split <;> simp
  suffices ∀ c, Bound cfg c → Bound cfg (run cfg c events).1 from this _ hs
  induction events with
  | nil => exact fun c h => h
  | cons e rest ih => exact fun c h => ih _ (step_bound cfg c e h)

/-- In SCRAM's exchange with binding `b`, the client's last message binds `b`: its `c=` is
`b`'s GS2 header and binding data in base 64 (`Scram.Binding.data`), the certificate's hash for
`tls-server-end-point` (`Scram.Binding.data_endPoint`), which is the one the handshake gave
(`Conn.run_bound`). -/
theorem onMessage_binds {c : Conn} {b : Scram.Binding} {m : Backend} {bytes : ByteArray}
    (hc : c.phase = .sasl b) (h : .send bytes ∈ (onMessage cfg c m).2) :
    ∃ final nonce proof, bytes = (Frontend.saslResponse final.toUTF8).encode
      ∧ final = "c=" ++ Base64.encode .std b.data ++ ",r=" ++ nonce ++ ",p=" ++ proof := by
  simp only [onMessage, hc] at h
  unfold onSasl at h
  cases m <;> (try simp only at h) <;> (repeat' split at h) <;> (try simp [fail] at h)
  rename_i final signature hr
  obtain ⟨nonce, proof, hf⟩ := Scram.respond_binds hr
  exact ⟨final, nonce, proof, h, hf⟩

end Lanes.Postgres.Conn
