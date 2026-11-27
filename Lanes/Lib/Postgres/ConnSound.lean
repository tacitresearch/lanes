/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Lib.Postgres.Conn
public import Lanes.Lib.Postgres.MessageSound

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

theorem step_fifo (c : Conn) (e : Event) : Fifo c (step cfg c e) := by
  cases e with
  | submit id r => exact submit_fifo cfg id r c
  | received bytes =>
    simp only [step]
    repeat' split
    · exact same_fifo c c rfl _ rfl rfl
    · exact fail_fifo c _
    · exact drain_fifo cfg _ (receive bytes c)
  | stop =>
    simp only [step]
    split
    · exact same_fifo c c rfl _ rfl rfl
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
      · exact absurd h not_mem_fail_committed
      · obtain ⟨c', next, m, hr, hc⟩ := drain_committed cfg _ _ h
        exact ⟨c', next, m, Reads.trans cfg (.receive bytes (.refl c)) hr, hc⟩
  | stop =>
    simp only [step] at h
    split at h
    · simp at h
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
      · exact absurd h not_mem_fail_query
      · exact absurd h (drain_query cfg _ _)
  | stop =>
    simp only [step] at h
    split at h
    · simp at h
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
    repeat' split
    · exact h
    · simp [fail]
    · exact Nat.le_trans (drain_queue cfg _ _) h
  | stop =>
    simp only [step]
    split
    · exact h
    · simp [fail]
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
  split <;> rfl

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
      · exact h
      · rename_i _ hroom
        apply drain_buffer
        simp only [receive, room] at hroom ⊢
        split
        · rename_i hz
          rw [ByteArray.size_append]
          omega
        · rw [ByteArray.size_append, ByteArray.size_extract]
          omega
  | stop =>
    simp only [step]
    split
    · exact h
    · exact h
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

/-- A server that says `AuthenticationOk` before it has proved it knows the password, once SCRAM
has begun, is not trusted: the connection closes. -/
theorem onMessage_sasl_authOk {c : Conn} (hc : c.phase = .sasl ∨ ∃ s, c.phase = .saslFinal s) :
    onMessage cfg c .authOk = fail c .signature := by
  rcases hc with hc | ⟨s, hc⟩ <;> simp [onMessage, hc, onSasl, onSaslFinal]

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

end Lanes.Postgres.Conn
