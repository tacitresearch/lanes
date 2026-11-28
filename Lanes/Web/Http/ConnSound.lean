/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Web.Http.Conn
public import Lanes.Web.Http.ReadRequestSound

/-!
What a connection of the HTTP server does (`Lanes.Web.Http.Conn`), for every configuration and every
sequence of events:

- responses are written in the order the requests were read, each once: the numbers of the
  writes of a run are `written, written + 1, …` (`Conn.run_writes`), and requests are handed on
  in increasing order, each number once (`Conn.run_submits`);
- every request handed on is one the strict reader reads in the connection's bytes
  (`Conn.step_submit_read`), and an answer to a request not waiting is ignored
  (`Conn.answer_ignored`);
- the buffer never holds more than `message_max` bytes (`Conn.run_buffer`), and no more than
  `inflight_max` requests are in flight (`Conn.run_slots`);
- a closed connection does nothing more and stays closed (`Conn.step_closed`); one that has
  stopped reading takes no more bytes and does not read again (`Conn.step_notReading`,
  `Conn.step_reading`); at a deadline it stops reading (`Conn.step_tick`); the loop is asked to
  read only an open connection that reads, for at least one byte (`Conn.wantsInput_room`);
- what it writes for a response, `HEAD` aside, is read back by the client's reader as that
  response (`Conn.read_encode`);
- no more connections are taken than the bound (`Conn.Count.admit_le`).
-/

@[expose] public section

namespace Lanes.Http.Conn

def Action.wrote : Action → Option Nat
  | .write seq _ => some seq
  | _ => none

def Action.submitted : Action → Option Nat
  | .submit seq _ | .begin seq _ => some seq
  | _ => none

variable {cfg : Config} {now : Nat}

/-! Pieces that change little -/

/-- `c'` holds the bytes, the requests in flight and the flags of `c`. -/
def Frame (c c' : Conn) : Prop :=
  c'.buffer = c.buffer ∧ c'.pos = c.pos ∧ c'.slots = c.slots ∧ c'.written = c.written
    ∧ c'.reading = c.reading ∧ c'.closed = c.closed

theorem waitMore_frame (c : Conn) : Frame c (waitMore cfg now c).1 := by
  simp only [waitMore, settle]
  repeat' split
  all_goals simp_all [Frame]

theorem waitMore_actions (c : Conn) : ∀ a ∈ (waitMore cfg now c).2, ∃ s b, a = .interim s b := by
  simp only [waitMore]
  repeat' split
  all_goals simp

theorem flushSlots_spec : ∀ (n : Nat) (slots : List Slot),
    n ≤ (flushSlots n slots).2.1
      ∧ (flushSlots n slots).1.filterMap Action.wrote = List.range' n ((flushSlots n slots).2.1 - n)
      ∧ (flushSlots n slots).2.1 + (flushSlots n slots).2.2.length = n + slots.length
      ∧ (flushSlots n slots).2.2.length ≤ slots.length
      ∧ ∀ a ∈ (flushSlots n slots).1, ∃ s b, a = .write s b
  | n, [] => by simp [flushSlots]
  | n, .asked _ _ :: rest => by simp [flushSlots]
  | n, .opened .. :: rest => by simp [flushSlots]
  | n, .stream _ :: rest => by simp [flushSlots]
  | n, .upgrading _ :: rest => by simp [flushSlots]
  | n, .switched .. :: rest => by simp [flushSlots]
  | n, .ready bytes :: rest => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := flushSlots_spec (n + 1) rest
    rcases e : flushSlots (n + 1) rest with ⟨actions, m, left⟩
    rw [e] at h1 h2 h3 h4 h5
    simp only at h1 h2 h3 h4 h5
    simp only [flushSlots, e, List.length_cons]
    refine ⟨by omega, ?_, by omega, by omega, ?_⟩
    · rw [show m - n = (m - (n + 1)) + 1 by omega, List.range'_succ]
      simp [Action.wrote, h2]
    · intro a ha
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact ⟨n, bytes, rfl⟩
      · exact h5 a ha

/-! A property of the parts of `step`, carried through them -/

section Carried

variable (P : Conn → Conn → List Action → Prop)
  (trans : ∀ {a b c xs ys}, P a b xs → P b c ys → P a c (xs ++ ys))

include trans in
theorem take_of
    (hwait : ∀ c, c.closed = false → c.reading = true → c.slots.length < cfg.inflight_max →
      Request.read cfg.limits c.buffer c.pos = .more → P c (waitMore cfg now c).1 (waitMore cfg now c).2)
    (hstay : ∀ c, P c c [])
    (hfull : ∀ c, P c (settle now c .full) [])
    (hrefuse : ∀ c why, c.closed = false → c.reading = true → c.slots.length < cfg.inflight_max →
      Request.read cfg.limits c.buffer c.pos = .refuse why →
      P c { c with reading := false, slots := c.slots ++ [.ready (refusal why)] } [])
    (hdone : ∀ c incoming stop, c.closed = false → c.reading = true →
      c.slots.length < cfg.inflight_max →
      Request.read cfg.limits c.buffer c.pos = .done incoming stop →
      P c { c with pos := stop, need := 0, slots := c.slots ++ [.asked incoming.headOnly incoming.close]
                   reading := !incoming.close, continued := false, stage := .idle, since_ms := now }
        [.submit (next c) incoming.request])
    (hbegin : ∀ c head start, c.closed = false → c.reading = true →
      c.slots.length < cfg.inflight_max → streamHead? cfg c = some (head, start) →
      P c (begin now c head start) [.begin (next c) (head.incoming .empty).request])
    (hupgrade : ∀ c head start, c.closed = false → c.reading = true →
      c.slots.length < cfg.inflight_max → upgradeHead? cfg c = some (head, start) →
      P c (beginUpgrade now c head start) [.begin (next c) (head.incoming .empty).request]) :
    ∀ fuel c, P c (take cfg now fuel c).1 (take cfg now fuel c).2
  | 0, c => hstay c
  | fuel + 1, c => by
    simp only [take]
    by_cases hc : (c.closed || !c.reading || c.inflow.isSome) = true
    · simp only [hc, ↓reduceIte]
      exact hstay c
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      have hc1 : c.closed = false := by cases h : c.closed <;> simp_all
      have hc2 : c.reading = true := by cases h : c.reading <;> simp_all
      by_cases hf : cfg.inflight_max ≤ c.slots.length
      · simp only [hf, ↓reduceIte]
        exact hfull c
      · simp only [hf, ↓reduceIte]
        by_cases hn : c.buffer.size - c.pos < c.need
        · simp only [hn, ↓reduceIte]
          exact hstay c
        · simp only [hn, ↓reduceIte]
          have hl : c.slots.length < cfg.inflight_max := by omega
          split
          · rename_i head start hs
            exact hupgrade c head start hc1 hc2 hl hs
          · split
            · rename_i head start hs
              exact trans (hbegin c head start hc1 hc2 hl hs)
                (take_of hwait hstay hfull hrefuse hdone hbegin hupgrade fuel _)
            · split
              · rename_i h
                exact hwait c hc1 hc2 hl h
              · rename_i why h
                exact hrefuse c why hc1 hc2 hl h
              · rename_i incoming stop h
                exact trans (hdone c incoming stop hc1 hc2 hl h)
                  (take_of hwait hstay hfull hrefuse hdone hbegin hupgrade fuel _)

include trans in
theorem drain_of
    (hflush : ∀ c, P c (flush now c).1 (flush now c).2)
    (hstream : ∀ c, P c (flushStream cfg now c).1 (flushStream cfg now c).2)
    (hswitch : ∀ c, P c (flushSwitch c).1 (flushSwitch c).2) (c : Conn) :
    P c (drain cfg now c).1 (drain cfg now c).2 := by
  have h1 := hflush c
  rcases e1 : flush now c with ⟨c1, a1⟩
  rw [e1] at h1
  have h2 := hstream c1
  rcases e2 : flushStream cfg now c1 with ⟨c2, a2⟩
  rw [e2] at h2
  have h3 := hflush c2
  rcases e3 : flush now c2 with ⟨c3, a3⟩
  rw [e3] at h3
  have h4 := hswitch c3
  rcases e4 : flushSwitch c3 with ⟨c4, a4⟩
  rw [e4] at h4
  simp only [drain, e1, e2, e3, e4]
  exact trans (trans (trans h1 h2) h3) h4

include trans in
theorem advance_of
    (htake : ∀ fuel c, P c (take cfg now fuel c).1 (take cfg now fuel c).2)
    (hflush : ∀ c, P c (flush now c).1 (flush now c).2)
    (hstream : ∀ c, P c (flushStream cfg now c).1 (flushStream cfg now c).2)
    (hswitch : ∀ c, P c (flushSwitch c).1 (flushSwitch c).2)
    (hpump : ∀ c, P c (pump cfg now c).1 (pump cfg now c).2)
    (hfinish : ∀ c, P c (finish c).1 (finish c).2) (c : Conn) :
    P c (advance cfg now c).1 (advance cfg now c).2 := by
  have h1 := drain_of P trans hflush hstream hswitch c
  rcases e1 : drain cfg now c with ⟨c1, a1⟩
  rw [e1] at h1
  have h2 := htake (cfg.inflight_max + 1) c1
  rcases e2 : take cfg now (cfg.inflight_max + 1) c1 with ⟨c2, a2⟩
  rw [e2] at h2
  have h3 := hpump c2
  rcases e3 : pump cfg now c2 with ⟨c3, a3⟩
  rw [e3] at h3
  have h4 := drain_of P trans hflush hstream hswitch c3
  rcases e4 : drain cfg now c3 with ⟨c4, a4⟩
  rw [e4] at h4
  have h5 := hfinish c4
  rcases e5 : finish c4 with ⟨c5, a5⟩
  rw [e5] at h5
  simp only [advance, e1, e2, e3, e4, e5]
  exact trans (trans (trans (trans h1 h2) h3) h4) h5

include trans in
theorem step_of
    (hadvance : ∀ c, P c (advance cfg now c).1 (advance cfg now c).2)
    (hstay : ∀ c, P c c [])
    (hreceive : ∀ c bytes, c.closed = false → c.reading = true → bytes.size ≤ room cfg c →
      P c (receive bytes c) [])
    (hanswer : ∀ c seq r, P c (answer seq r c) [])
    (hexpire : ∀ c, P c (expire cfg now c) [])
    (hquiet : ∀ c, P c (quiet c) [])
    (hclose : ∀ c, P c { c with closed := true } [.close])
    (hrespond : ∀ c seq r, P c (respond seq r c) [])
    (htook : ∀ c seq index r, P c (took cfg now seq index r c) [])
    (hpulled : ∀ c seq index r, P c (pulled cfg now seq index r c) [])
    (hsent : ∀ c, P c { c with unsent := false } []) (c : Conn) (e : Event) :
    P c (step cfg now c e).1 (step cfg now c e).2 := by
  unfold step
  by_cases hc : c.closed = true
  · simp only [hc, ↓reduceIte]
    exact hstay c
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]
    have hc : c.closed = false := by simpa using hc
    cases e with
    | received bytes =>
      dsimp only
      by_cases hr : c.reading = true
      · by_cases hroom : room cfg c < bytes.size
        · simpa [hr, hroom, hc] using hclose c
        · have := trans (hreceive c bytes hc hr (by omega)) (hadvance _)
          simpa [hr, hroom, hc] using this
      · simp only [Bool.not_eq_true] at hr
        simpa [hr, hc] using hstay c
    | ended => simpa [hc] using trans (hquiet c) (hadvance _)
    | broken => simpa [hc] using hclose c
    | answered seq r => simpa [hc] using trans (hanswer c seq r) (hadvance _)
    | responded seq r => simpa [hc] using trans (hrespond c seq r) (hadvance _)
    | took seq index r => simpa [hc] using trans (htook c seq index r) (hadvance _)
    | pulled seq index r => simpa [hc] using trans (hpulled c seq index r) (hadvance _)
    | sent => simpa [hc] using trans (hsent c) (hadvance _)
    | tick => simpa [hc] using trans (hexpire c) (hadvance _)
    | stop => simpa [hc] using trans (hquiet c) (hadvance _)

include trans in
theorem run_of (hstay : ∀ c, P c c [])
    (hstep : ∀ now c e, P c (step cfg now c e).1 (step cfg now c e).2) :
    ∀ (c : Conn) (events : List (Nat × Event)), P c (run cfg c events).1 (run cfg c events).2
  | c, [] => hstay c
  | c, (now, e) :: rest => by
    have h1 := hstep now c e
    rcases e1 : step cfg now c e with ⟨c1, a1⟩
    rw [e1] at h1
    have h2 := run_of hstay hstep c1 rest
    rcases e2 : run cfg c1 rest with ⟨c2, a2⟩
    rw [e2] at h2
    simp only [run, e1, e2]
    exact trans h1 h2

end Carried

/-! Pieces of `step`, one at a time -/

theorem settle_frame (now : Nat) (c : Conn) (stage : Stage) : Frame c (settle now c stage) := by
  unfold settle
  split <;> simp [Frame]

theorem flush_eq (now : Nat) (c : Conn) :
    (flush now c).1.written = (flushSlots c.written c.slots).2.1
      ∧ (flush now c).1.slots = (flushSlots c.written c.slots).2.2
      ∧ (flush now c).2 = (flushSlots c.written c.slots).1
      ∧ (flush now c).1.buffer = c.buffer ∧ (flush now c).1.pos = c.pos
      ∧ (flush now c).1.reading = c.reading ∧ (flush now c).1.closed = c.closed := by
  unfold flush
  rcases flushSlots c.written c.slots with ⟨a, m, l⟩
  simp

theorem finish_eq (c : Conn) :
    ((finish c).1 = { c with closed := true } ∧ (finish c).2 = [.close])
      ∨ ((finish c).1 = c ∧ (finish c).2 = []) := by
  unfold finish
  split
  · exact .inl ⟨rfl, rfl⟩
  · exact .inr ⟨rfl, rfl⟩

theorem answer_eq (seq : Nat) (r : Response) (c : Conn) :
    ∃ slots, answer seq r c = { c with slots } ∧ slots.length = c.slots.length := by
  unfold answer
  split
  · split
    · exact ⟨_, rfl, by simp⟩
    · exact ⟨c.slots, rfl, rfl⟩
  · exact ⟨c.slots, rfl, rfl⟩

theorem expire_eq (now : Nat) (c : Conn) :
    expire cfg now c = c ∨ expire cfg now c = { c with reading := false }
      ∨ (c.slots.length < cfg.inflight_max
        ∧ expire cfg now c = { c with reading := false, slots := c.slots ++ [.ready timeout] }) := by
  unfold expire
  split
  · split
    · split
      · exact .inr (.inl rfl)
      · rename_i h
        refine .inr (.inr ⟨?_, rfl⟩)
        simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at h
        omega
    · exact .inl rfl
  · exact .inl rfl

/-- `c'` holds the bytes and the requests in flight of `c`, numbered alike, and reads only if
`c` does. -/
def Calm (c c' : Conn) : Prop :=
  c'.buffer = c.buffer ∧ c'.pos = c.pos ∧ c'.written = c.written
    ∧ c'.slots.length = c.slots.length ∧ (c'.reading = true → c.reading = true)

theorem respond_calm (seq : Nat) (r : Response) (c : Conn) : Calm c (respond seq r c) := by
  unfold respond
  split
  · split <;> simp [Calm]
  · simp [Calm]

theorem pulled_calm (now seq index : Nat) (r : Response) (c : Conn) :
    Calm c (pulled cfg now seq index r c) := by
  unfold pulled
  split
  · split
    · split
      · simp [Calm]
      · simp [Calm]
    · simp [Calm]
  · simp [Calm]

theorem took_calm (now seq index : Nat) (r : Response) (c : Conn) :
    Calm c (took cfg now seq index r c) := by
  unfold took
  repeat' split
  all_goals simp_all [Calm, settle]
  all_goals split <;> simp_all

theorem quiet_calm (c : Conn) : Calm c (quiet c) := by
  simp [Calm, quiet]

theorem sent_calm (c : Conn) : Calm c { c with unsent := false } := by
  simp [Calm]

/-- Where a piece ends is within the bytes. -/
theorem next_stop {bytes : ByteArray} {taken room : Nat} :
    ∀ {fuel pos : Nat} {framing : Inflow.Framing} {data : ByteArray} {stop : Nat}
      {framing' : Inflow.Framing} {last : Bool},
      Inflow.next cfg bytes pos taken room framing fuel = .piece data stop framing' last →
      stop ≤ bytes.size
  | 0, pos, framing, data, stop, framing', last, h => by
    cases framing <;> simp [Inflow.next] at h
  | fuel + 1, pos, framing, data, stop, framing', last, h => by
    cases framing with
    | length left =>
      simp only [Inflow.next] at h
      split at h
      · cases h
      · cases h; omega
    | data left =>
      simp only [Inflow.next] at h
      split at h
      · cases h
      · cases h; omega
    | size =>
      simp only [Inflow.next] at h
      split at h
      · cases h
      · cases h
      · split at h
        · exact next_stop h
        · split at h
          · cases h
          · exact next_stop h
    | crlf =>
      simp only [Inflow.next] at h
      split at h
      · cases h
      · cases h
      · exact next_stop h
    | last =>
      simp only [Inflow.next] at h
      split at h
      · cases h
      · cases h
      · rename_i q hq
        cases h
        exact (crlf_bound hq).2

theorem gather_stop {bytes : ByteArray} :
    ∀ {fuel pos taken : Nat} {framing : Inflow.Framing} {acc data : ByteArray} {stop : Nat}
      {framing' : Inflow.Framing} {last : Bool}, pos ≤ bytes.size →
      Inflow.gather cfg bytes fuel pos taken framing acc = .piece data stop framing' last →
      stop ≤ bytes.size
  | 0, pos, taken, framing, acc, data, stop, framing', last, hp, h => by
    simp only [Inflow.gather] at h
    split at h
    · cases h
    · cases h; exact hp
  | fuel + 1, pos, taken, framing, acc, data, stop, framing', last, hp, h => by
    simp only [Inflow.gather] at h
    split at h
    · split at h
      · cases h
      · cases h; exact hp
    · split at h
      · cases h
      · cases h; exact hp
    · rename_i d s f l hn
      have hs := next_stop hn
      split at h
      · cases h; exact hs
      · exact gather_stop hs h

/-- What `pump` does: the bytes, the number written and the requests in flight stay, the next
request may start later in the buffer but within it, reading only stops, and it writes
`100 Continue` and hands on pieces, nothing else. -/
theorem pump_frame (now : Nat) (c : Conn) :
    (pump cfg now c).1.buffer = c.buffer ∧ (pump cfg now c).1.written = c.written
      ∧ (pump cfg now c).1.slots.length = c.slots.length
      ∧ ((pump cfg now c).1.reading = true → c.reading = true)
      ∧ (c.pos ≤ c.buffer.size → (pump cfg now c).1.pos ≤ c.buffer.size)
      ∧ ∀ a ∈ (pump cfg now c).2, a.wrote = none ∧ a.submitted = none
        ∧ ∀ s r, a ≠ .submit s r := by
  unfold pump
  split
  · simp
  · rename_i f hf
    split
    · simp
    · split
      · simp
      · split
        · split <;> simp [Action.wrote, Action.submitted]
        · dsimp only
          generalize hg : Inflow.gather cfg c.buffer (max 1 cfg.piece_max) c.pos f.taken f.framing .empty = g
          cases g with
          | more =>
            refine ⟨rfl, rfl, rfl, id, id, ?_⟩
            intro a ha
            split at ha <;> simp_all [Action.wrote, Action.submitted]
          | refuse why =>
            refine ⟨rfl, rfl, by simp, by simp, id, ?_⟩
            intro a ha
            split at ha <;> simp_all [Action.wrote, Action.submitted]
          | piece data stop framing last =>
            simp only [settle]
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
            all_goals (try split) <;> simp_all
            all_goals first
              | exact fun hp => gather_stop hp hg
              | simp [Action.wrote, Action.submitted]

/-- What `flushStream` does: the bytes stay, reading only stops, nothing is handed on, and
either nothing is written and the requests in flight stay, or the streamed response at the
front ends and is written. -/
theorem flushStream_frame (now : Nat) (c : Conn) :
    (flushStream cfg now c).1.buffer = c.buffer ∧ (flushStream cfg now c).1.pos = c.pos
      ∧ ((flushStream cfg now c).1.reading = true → c.reading = true)
      ∧ (∀ a ∈ (flushStream cfg now c).2, a.submitted = none ∧ ∀ s r, a ≠ .submit s r)
      ∧ (((flushStream cfg now c).1.written = c.written
            ∧ (flushStream cfg now c).1.slots.length = c.slots.length
            ∧ ∀ a ∈ (flushStream cfg now c).2, a.wrote = none)
        ∨ ((flushStream cfg now c).1.written = c.written + 1
            ∧ (flushStream cfg now c).1.slots.length + 1 = c.slots.length
            ∧ (flushStream cfg now c).2.filterMap Action.wrote = [c.written])) := by
  unfold flushStream
  split
  · simp
  · split
    · rename_i o rest hs
      dsimp only
      cases hst : o.state
      all_goals cases hp : o.pending.isEmpty
      all_goals simp only [hst, ite_true, ite_false, Bool.false_eq_true]
      all_goals (repeat' split) <;> simp_all [Action.wrote, Action.submitted]
      all_goals simp [Action.wrote, List.filterMap]
    · simp

/-- The request that streams is begun: the head is handed on, the next request starts after it. -/
theorem streamHead?_some {c : Conn} {head : Request.Head} {start : Nat}
    (h : streamHead? cfg c = some (head, start)) : c.pos + 4 ≤ start ∧ start ≤ c.buffer.size := by
  unfold streamHead? at h
  split at h
  · cases h
  · split at h
    · rename_i head' start' hr
      split at h
      · cases h
        have := Request.readHead_done hr
        exact ⟨this.1, this.2.2.1⟩
      · cases h
    · cases h

/-- The request that may switch protocols is handed on: the next request starts after it. -/
theorem upgradeHead?_some {c : Conn} {head : Request.Head} {start : Nat}
    (h : upgradeHead? cfg c = some (head, start)) : start ≤ c.buffer.size := by
  unfold upgradeHead? at h
  split at h
  · cases h
  · split at h
    · rename_i head' start' hr
      split at h
      · cases h
        exact (Request.readHead_done hr).2.2.1
      · cases h
    · cases h

/-- What `flushSwitch` does: it may close the connection, and nothing else changes; it writes
nothing and hands nothing on. -/
theorem flushSwitch_frame (c : Conn) :
    (flushSwitch c).1.buffer = c.buffer ∧ (flushSwitch c).1.pos = c.pos
      ∧ (flushSwitch c).1.slots = c.slots ∧ (flushSwitch c).1.written = c.written
      ∧ (flushSwitch c).1.reading = c.reading
      ∧ ∀ a ∈ (flushSwitch c).2, a.wrote = none ∧ a.submitted = none ∧ ∀ s r, a ≠ .submit s r := by
  unfold flushSwitch
  split
  · simp
  · split <;> simp [Action.wrote, Action.submitted]

/-- The connection is handed over only once every earlier response is written, and then does
nothing more. -/
theorem flushSwitch_switch {c : Conn} {seq : Nat} {head : Request} {r : Response} {rest : ByteArray}
    (h : Action.switch seq head r rest ∈ (flushSwitch c).2) :
    seq = c.written ∧ (flushSwitch c).1.closed = true
      ∧ ∃ slots, c.slots = .switched head r :: slots := by
  unfold flushSwitch at h ⊢
  split at h
  · cases h
  · rename_i hc
    split at h
    · rename_i head' r' slots hs
      simp only [List.mem_singleton, Action.switch.injEq] at h
      obtain ⟨rfl, rfl, rfl, -⟩ := h
      simp [hs, hc]
    · cases h

/-- An answer of `101` to a request that may switch protocols switches it; any other is written,
and the connection closes after it. -/
theorem respond_upgrading {seq : Nat} {c : Conn} {head : Request} (hw : c.written ≤ seq)
    (h : c.slots[seq - c.written]? = some (.upgrading head)) (r : Response) :
    (respond seq r c).slots = c.slots.set (seq - c.written)
      (if r.status == 101 then .switched head r else .ready (encode false true r)) := by
  simp [respond, hw, h]

/-! Responses in order, each once -/

/-- The writes of `actions` are of the requests numbered from `c.written` to `c'.written`, in
order, each once. -/
def Writes (c c' : Conn) (actions : List Action) : Prop :=
  c.written ≤ c'.written
    ∧ actions.filterMap Action.wrote = List.range' c.written (c'.written - c.written)

theorem Writes.trans {a b c : Conn} {xs ys : List Action} (h₁ : Writes a b xs)
    (h₂ : Writes b c ys) : Writes a c (xs ++ ys) := by
  obtain ⟨l₁, e₁⟩ := h₁
  obtain ⟨l₂, e₂⟩ := h₂
  refine ⟨by omega, ?_⟩
  rw [List.filterMap_append, e₁, e₂]
  have := List.range'_append (s := a.written) (m := b.written - a.written)
    (n := c.written - b.written) (step := 1)
  rw [Nat.one_mul, show a.written + (b.written - a.written) = b.written by omega,
    show b.written - a.written + (c.written - b.written) = c.written - a.written by omega] at this
  exact this

theorem Writes.none {c c' : Conn} {actions : List Action} (hw : c'.written = c.written)
    (ha : ∀ a ∈ actions, a.wrote = none) : Writes c c' actions := by
  refine ⟨by omega, ?_⟩
  rw [hw, Nat.sub_self, List.range'_zero, List.filterMap_eq_nil_iff]
  exact ha

theorem Writes.calm {c c' : Conn} (h : Calm c c') : Writes c c' [] :=
  Writes.none h.2.2.1 (by simp)

theorem step_writes (now : Nat) (c : Conn) (e : Event) :
    Writes c (step cfg now c e).1 (step cfg now c e).2 := by
  refine step_of Writes Writes.trans (fun c => advance_of Writes Writes.trans
      (take_of Writes Writes.trans ?wait ?stay ?full ?refuse ?done ?begin ?upgrade) ?flush ?stream ?switch ?pump
      ?finish c)
    ?stay ?receive ?answer ?expire ?quiet ?close ?respond ?took ?pulled ?sent c e
  case begin => exact fun c _ _ _ _ _ _ => Writes.none rfl (by simp [Action.wrote])
  case upgrade => exact fun c _ _ _ _ _ _ => Writes.none rfl (by simp [Action.wrote])
  case switch =>
    intro c
    obtain ⟨-, -, -, hw, -, ha⟩ := flushSwitch_frame c
    exact Writes.none hw fun a h => (ha a h).1
  case stream =>
    intro c
    obtain ⟨-, -, -, -, h⟩ := flushStream_frame (cfg := cfg) now c
    rcases h with ⟨hw, -, ha⟩ | ⟨hw, -, ha⟩
    · exact Writes.none hw ha
    · refine ⟨by omega, ?_⟩
      rw [ha, hw, show c.written + 1 - c.written = 1 by omega]
      rfl
  case pump =>
    intro c
    obtain ⟨-, hw, -, -, -, ha⟩ := pump_frame (cfg := cfg) now c
    exact Writes.none hw fun a h => (ha a h).1
  case respond => exact fun c seq r => Writes.calm (respond_calm seq r c)
  case took => exact fun c seq index r => Writes.calm (took_calm now seq index r c)
  case pulled => exact fun c seq index r => Writes.calm (pulled_calm now seq index r c)
  case sent => exact fun c => Writes.calm (sent_calm c)
  case wait =>
    intro c _ _ _ _
    refine Writes.none (waitMore_frame c).2.2.2.1 fun a ha => ?_
    obtain ⟨s, b, rfl⟩ := waitMore_actions c a ha
    rfl
  case stay => exact fun c => Writes.none rfl (by simp)
  case full => exact fun c => Writes.none (settle_frame now c .full).2.2.2.1 (by simp)
  case refuse => exact fun c _ _ _ _ _ => Writes.none rfl (by simp)
  case done => exact fun c _ _ _ _ _ _ => Writes.none rfl (by simp [Action.wrote])
  case flush =>
    intro c
    obtain ⟨hw, -, ha, -⟩ := flush_eq now c
    obtain ⟨h₁, h₂, -⟩ := flushSlots_spec c.written c.slots
    exact ⟨hw ▸ h₁, by rw [ha, hw]; exact h₂⟩
  case finish =>
    intro c
    rcases finish_eq c with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rw [h₁, h₂] <;> exact Writes.none rfl (by simp [Action.wrote])
  case receive => exact fun c _ _ _ _ => Writes.none rfl (by simp)
  case answer =>
    intro c seq r
    obtain ⟨slots, h, -⟩ := answer_eq seq r c
    rw [h]
    exact Writes.none rfl (by simp)
  case expire =>
    intro c
    rcases expire_eq now c with h | h | ⟨-, h⟩ <;> rw [h] <;> exact Writes.none rfl (by simp)
  case quiet => exact fun c => Writes.calm (quiet_calm c)
  case close => exact fun c => Writes.none rfl (by simp [Action.wrote])

/-- Responses go out in the order the requests were read, each once: the writes of any run are
of the requests numbered `written`, `written + 1`, …, with none left out and none twice. -/
theorem run_writes (c : Conn) (events : List (Nat × Event)) :
    c.written ≤ (run cfg c events).1.written
      ∧ (run cfg c events).2.filterMap Action.wrote
        = List.range' c.written ((run cfg c events).1.written - c.written) :=
  run_of Writes Writes.trans (fun c => Writes.none rfl (by simp)) step_writes c events

/-! Requests handed on in order, each number once -/

/-- The requests `actions` hand on are numbered from `c.next` to below `c'.next`, in increasing
order. -/
def Submits (c c' : Conn) (actions : List Action) : Prop :=
  c.next ≤ c'.next ∧ (actions.filterMap Action.submitted).Pairwise (· < ·)
    ∧ ∀ s ∈ actions.filterMap Action.submitted, c.next ≤ s ∧ s < c'.next

theorem Submits.trans {a b c : Conn} {xs ys : List Action} (h₁ : Submits a b xs)
    (h₂ : Submits b c ys) : Submits a c (xs ++ ys) := by
  obtain ⟨l₁, p₁, r₁⟩ := h₁
  obtain ⟨l₂, p₂, r₂⟩ := h₂
  refine ⟨by omega, ?_, ?_⟩
  · rw [List.filterMap_append, List.pairwise_append]
    refine ⟨p₁, p₂, fun x hx y hy => ?_⟩
    have := (r₁ x hx).2
    have := (r₂ y hy).1
    omega
  · intro s hs
    rw [List.filterMap_append, List.mem_append] at hs
    rcases hs with hs | hs
    · have := r₁ s hs
      omega
    · have := r₂ s hs
      omega

theorem Submits.none {c c' : Conn} {actions : List Action} (hn : c.next ≤ c'.next)
    (ha : ∀ a ∈ actions, a.submitted = none) : Submits c c' actions := by
  unfold Submits
  rw [show actions.filterMap Action.submitted = [] from List.filterMap_eq_nil_iff.2 ha]
  exact ⟨hn, by simp, by simp⟩

theorem Submits.calm {c c' : Conn} (h : Calm c c') : Submits c c' [] :=
  Submits.none (by simp [next, h.2.2.1, h.2.2.2.1]) (by simp)

theorem step_submits (now : Nat) (c : Conn) (e : Event) :
    Submits c (step cfg now c e).1 (step cfg now c e).2 := by
  refine step_of Submits Submits.trans (fun c => advance_of Submits Submits.trans
      (take_of Submits Submits.trans ?wait ?stay ?full ?refuse ?done ?begin ?upgrade) ?flush ?stream ?switch ?pump
      ?finish c)
    ?stay ?receive ?answer ?expire ?quiet ?close ?respond ?took ?pulled ?sent c e
  case begin =>
    intro c _ _ _ _ _ _
    refine ⟨by simp only [next, begin, List.length_append]; omega, by simp [Action.submitted], ?_⟩
    simp [Action.submitted, next, begin]
  case upgrade =>
    intro c _ _ _ _ _ _
    refine ⟨by simp only [next, beginUpgrade, List.length_append]; omega, by simp [Action.submitted], ?_⟩
    simp [Action.submitted, next, beginUpgrade]
  case switch =>
    intro c
    obtain ⟨-, -, hs, hw, -, ha⟩ := flushSwitch_frame c
    exact Submits.none (by simp [next, hs, hw]) fun a h => (ha a h).2.1
  case stream =>
    intro c
    obtain ⟨-, -, -, hs, h⟩ := flushStream_frame (cfg := cfg) now c
    refine Submits.none ?_ fun a ha => (hs a ha).1
    rcases h with ⟨hw, hl, -⟩ | ⟨hw, hl, -⟩ <;> simp only [next] <;> omega
  case pump =>
    intro c
    obtain ⟨-, hw, hl, -, -, ha⟩ := pump_frame (cfg := cfg) now c
    exact Submits.none (by simp [next, hw, hl]) fun a h => (ha a h).2.1
  case respond => exact fun c seq r => Submits.calm (respond_calm seq r c)
  case took => exact fun c seq index r => Submits.calm (took_calm now seq index r c)
  case pulled => exact fun c seq index r => Submits.calm (pulled_calm now seq index r c)
  case sent => exact fun c => Submits.calm (sent_calm c)
  case wait =>
    intro c _ _ _ _
    obtain ⟨-, -, hs, hw, -⟩ := waitMore_frame (cfg := cfg) (now := now) c
    refine Submits.none (by simp [next, hs, hw]) fun a ha => ?_
    obtain ⟨s, b, rfl⟩ := waitMore_actions c a ha
    rfl
  case stay => exact fun c => Submits.none (Nat.le_refl _) (by simp)
  case full =>
    intro c
    obtain ⟨-, -, hs, hw, -⟩ := settle_frame now c .full
    exact Submits.none (by simp [next, hs, hw]) (by simp)
  case refuse =>
    exact fun c _ _ _ _ _ => Submits.none (by simp only [next, List.length_append]; omega) (by simp)
  case done =>
    intro c _ _ _ _ _ _
    refine ⟨by simp only [next, List.length_append]; omega, by simp [Action.submitted], ?_⟩
    simp [Action.submitted, next]
  case flush =>
    intro c
    obtain ⟨hw, hs, ha, -⟩ := flush_eq now c
    obtain ⟨-, -, h₃, -, h₅⟩ := flushSlots_spec c.written c.slots
    refine Submits.none (by simp only [next, hw, hs]; omega) fun a h => ?_
    rw [ha] at h
    obtain ⟨s, b, rfl⟩ := h₅ a h
    rfl
  case finish =>
    intro c
    rcases finish_eq c with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rw [h₁, h₂] <;>
      exact Submits.none (Nat.le_refl _) (by simp [Action.submitted])
  case receive => exact fun c _ _ _ _ => Submits.none (Nat.le_refl _) (by simp)
  case answer =>
    intro c seq r
    obtain ⟨slots, h, hl⟩ := answer_eq seq r c
    rw [h]
    exact Submits.none (by simp [next, hl]) (by simp)
  case expire =>
    intro c
    rcases expire_eq now c with h | h | ⟨-, h⟩ <;> rw [h] <;>
      exact Submits.none (by simp [next]) (by simp)
  case quiet => exact fun c => Submits.calm (quiet_calm c)
  case close => exact fun c => Submits.none (Nat.le_refl _) (by simp [Action.submitted])

/-- Requests are handed on in increasing order, so each number once, all from `next` on. -/
theorem run_submits (c : Conn) (events : List (Nat × Event)) :
    ((run cfg c events).2.filterMap Action.submitted).Pairwise (· < ·)
      ∧ ∀ s ∈ (run cfg c events).2.filterMap Action.submitted,
        c.next ≤ s ∧ s < (run cfg c events).1.next :=
  (run_of Submits Submits.trans (fun c => Submits.none (Nat.le_refl _) (by simp)) step_submits
    c events).2

/-! Bounds -/

/-- A part of `step` keeps `I`. -/
abbrev Keeps (I : Conn → Prop) (c c' : Conn) (_ : List Action) : Prop := I c → I c'

theorem Keeps.trans {I : Conn → Prop} {a b c : Conn} {xs ys : List Action}
    (h₁ : Keeps I a b xs) (h₂ : Keeps I b c ys) : Keeps I a c (xs ++ ys) := fun h => h₂ (h₁ h)

/-- The buffer holds at most `message_max` bytes, and the next request starts within it. -/
def Bounded (cfg : Config) (c : Conn) : Prop :=
  c.pos ≤ c.buffer.size ∧ c.buffer.size ≤ cfg.limits.message_max

theorem Calm.bounded {c c' : Conn} (h : Calm c c') : Keeps (Bounded cfg) c c' [] :=
  fun hb => ⟨by rw [h.1, h.2.1]; exact hb.1, by rw [h.1]; exact hb.2⟩

theorem step_buffer (now : Nat) (c : Conn) (e : Event) (h : Bounded cfg c) :
    Bounded cfg (step cfg now c e).1 := by
  refine step_of (Keeps (Bounded cfg)) Keeps.trans
    (fun c => advance_of (Keeps (Bounded cfg)) Keeps.trans
      (take_of (Keeps (Bounded cfg)) Keeps.trans ?wait ?stay ?full ?refuse ?done ?begin ?upgrade) ?flush
      ?stream ?switch ?pump ?finish c)
    ?stay ?receive ?answer ?expire ?quiet ?close ?respond ?took ?pulled ?sent c e h
  case begin =>
    intro c head start _ _ _ hs h
    exact ⟨(streamHead?_some hs).2, h.2⟩
  case upgrade =>
    intro c head start _ _ _ hs h
    exact ⟨by simpa [beginUpgrade] using upgradeHead?_some (cfg := cfg) hs,
      by simpa [beginUpgrade] using h.2⟩
  case switch =>
    intro c h
    obtain ⟨hb, hp, -⟩ := flushSwitch_frame c
    exact ⟨by rw [hb, hp]; exact h.1, by rw [hb]; exact h.2⟩
  case stream =>
    intro c h
    obtain ⟨hb, hp, -⟩ := flushStream_frame (cfg := cfg) now c
    exact ⟨by rw [hb, hp]; exact h.1, by rw [hb]; exact h.2⟩
  case pump =>
    intro c h
    obtain ⟨hb, -, -, -, hp, -⟩ := pump_frame (cfg := cfg) now c
    exact ⟨by rw [hb]; exact hp h.1, by rw [hb]; exact h.2⟩
  case respond => exact fun c seq r => Calm.bounded (respond_calm seq r c)
  case took => exact fun c seq index r => Calm.bounded (took_calm now seq index r c)
  case pulled => exact fun c seq index r => Calm.bounded (pulled_calm now seq index r c)
  case sent => exact fun c => Calm.bounded (sent_calm c)
  case wait =>
    intro c _ _ _ _ h
    obtain ⟨hb, hp, -⟩ := waitMore_frame (cfg := cfg) (now := now) c
    exact ⟨by rw [hb, hp]; exact h.1, by rw [hb]; exact h.2⟩
  case stay => exact fun _ h => h
  case full =>
    intro c h
    obtain ⟨hb, hp, -⟩ := settle_frame now c .full
    exact ⟨by rw [hb, hp]; exact h.1, by rw [hb]; exact h.2⟩
  case refuse => exact fun _ _ _ _ _ _ h => h
  case done =>
    intro c _ _ _ _ _ hr h
    exact ⟨(Request.read_done hr).2.1, h.2⟩
  case flush =>
    intro c h
    obtain ⟨-, -, -, hb, hp, -⟩ := flush_eq now c
    exact ⟨by rw [hb, hp]; exact h.1, by rw [hb]; exact h.2⟩
  case finish =>
    intro c h
    rcases finish_eq c with ⟨h₁, -⟩ | ⟨h₁, -⟩ <;> rw [h₁] <;> exact h
  case receive =>
    intro c bytes _ _ hroom h
    obtain ⟨h₁, h₂⟩ := h
    unfold room at hroom
    have key : (receive bytes c).buffer.size = c.buffer.size - c.pos + bytes.size := by
      unfold receive
      split
      · rename_i h0
        simp [h0]
      · simp
    exact ⟨by simp [receive], by rw [key]; omega⟩
  case answer =>
    intro c seq r h
    obtain ⟨slots, e, -⟩ := answer_eq seq r c
    rw [e]
    exact h
  case expire =>
    intro c h
    rcases expire_eq now c with e | e | ⟨-, e⟩ <;> rw [e] <;> exact h
  case quiet => exact fun c => Calm.bounded (quiet_calm c)
  case close => exact fun _ h => h

/-- The buffer never holds more than `message_max` bytes. -/
theorem run_buffer (c : Conn) (events : List (Nat × Event)) (h : Bounded cfg c) :
    Bounded cfg (run cfg c events).1 :=
  run_of (Keeps (Bounded cfg)) Keeps.trans (fun _ h => h) (fun now c e => step_buffer now c e)
    c events h

theorem Calm.slots {c c' : Conn} (h : Calm c c') :
    Keeps (fun c => c.slots.length ≤ cfg.inflight_max) c c' [] :=
  fun hs => by show c'.slots.length ≤ cfg.inflight_max; rw [h.2.2.2.1]; exact hs

theorem step_slots (now : Nat) (c : Conn) (e : Event) (h : c.slots.length ≤ cfg.inflight_max) :
    (step cfg now c e).1.slots.length ≤ cfg.inflight_max := by
  refine step_of (Keeps fun c => c.slots.length ≤ cfg.inflight_max) Keeps.trans
    (fun c => advance_of (Keeps fun c => c.slots.length ≤ cfg.inflight_max) Keeps.trans
      (take_of (Keeps fun c => c.slots.length ≤ cfg.inflight_max) Keeps.trans ?wait ?stay ?full
        ?refuse ?done ?begin ?upgrade) ?flush ?stream ?switch ?pump ?finish c)
    ?stay ?receive ?answer ?expire ?quiet ?close ?respond ?took ?pulled ?sent c e h
  case begin => exact fun _ _ _ _ _ hl _ _ => by simp [begin]; omega
  case upgrade => exact fun _ _ _ _ _ hl _ _ => by simp [beginUpgrade]; omega
  case switch =>
    intro c h
    rw [(flushSwitch_frame c).2.2.1]
    exact h
  case stream =>
    intro c h
    obtain ⟨-, -, -, -, hs⟩ := flushStream_frame (cfg := cfg) now c
    rcases hs with ⟨-, hl, -⟩ | ⟨-, hl, -⟩ <;> omega
  case pump =>
    intro c h
    rw [(pump_frame (cfg := cfg) now c).2.2.1]
    exact h
  case respond => exact fun c seq r => Calm.slots (respond_calm seq r c)
  case took => exact fun c seq index r => Calm.slots (took_calm now seq index r c)
  case pulled => exact fun c seq index r => Calm.slots (pulled_calm now seq index r c)
  case sent => exact fun c => Calm.slots (sent_calm c)
  case wait =>
    intro c _ _ _ _ h
    rw [(waitMore_frame (cfg := cfg) (now := now) c).2.2.1]
    exact h
  case stay => exact fun _ h => h
  case full =>
    intro c h
    rw [(settle_frame now c .full).2.2.1]
    exact h
  case refuse => exact fun _ _ _ _ hl _ _ => by simp; omega
  case done => exact fun _ _ _ _ _ hl _ _ => by simp; omega
  case flush =>
    intro c h
    obtain ⟨-, hs, -⟩ := flush_eq now c
    rw [hs]
    exact Nat.le_trans (flushSlots_spec c.written c.slots).2.2.2.1 h
  case finish =>
    intro c h
    rcases finish_eq c with ⟨h₁, -⟩ | ⟨h₁, -⟩ <;> rw [h₁] <;> exact h
  case receive => exact fun _ _ _ _ _ h => h
  case answer =>
    intro c seq r h
    obtain ⟨slots, e, hl⟩ := answer_eq seq r c
    rw [e]
    simpa [hl] using h
  case expire =>
    intro c h
    rcases expire_eq now c with e | e | ⟨hl, e⟩ <;> rw [e]
    · exact h
    · exact h
    · simp
      omega
  case quiet => exact fun c => Calm.slots (quiet_calm c)
  case close => exact fun _ h => h

/-- No more than `inflight_max` requests are in flight on a connection. -/
theorem run_slots (c : Conn) (events : List (Nat × Event))
    (h : c.slots.length ≤ cfg.inflight_max) :
    (run cfg c events).1.slots.length ≤ cfg.inflight_max :=
  run_of (Keeps fun c => c.slots.length ≤ cfg.inflight_max) Keeps.trans (fun _ h => h)
    (fun now c e => step_slots now c e) c events h

/-! Closing and reading -/

/-- A closed connection does nothing more, and so stays closed. -/
theorem step_closed (now : Nat) {c : Conn} (h : c.closed = true) (e : Event) :
    step cfg now c e = (c, []) := by
  simp [step, h]

/-- A connection that has stopped reading takes no more bytes. -/
theorem step_notReading (now : Nat) {c : Conn} (h : c.reading = false) (bytes : ByteArray) :
    step cfg now c (.received bytes) = (c, []) := by
  unfold step
  split <;> simp [h]

theorem advance_quiet (now : Nat) (c : Conn) (h : c.reading = false) :
    (advance cfg now c).1.reading = false := by
  refine advance_of (Keeps fun c => c.reading = false) Keeps.trans
    (take_of (Keeps fun c => c.reading = false) Keeps.trans ?wait ?stay ?full ?refuse ?done ?begin ?upgrade)
    ?flush ?stream ?switch ?pump ?finish c h
  case wait => exact fun _ _ hr _ _ h => by rw [h] at hr; cases hr
  case begin => exact fun _ _ _ _ hr _ _ h => by rw [h] at hr; cases hr
  case upgrade => exact fun _ _ _ _ hr _ _ h => by rw [h] at hr; cases hr
  case switch =>
    intro c h
    rw [(flushSwitch_frame c).2.2.2.2.1]
    exact h
  case stream =>
    intro c h
    cases h' : (flushStream cfg now c).1.reading
    · rfl
    · have := (flushStream_frame (cfg := cfg) now c).2.2.1 h'
      rw [h] at this
      cases this
  case pump =>
    intro c h
    cases h' : (pump cfg now c).1.reading
    · rfl
    · have := (pump_frame (cfg := cfg) now c).2.2.2.1 h'
      rw [h] at this
      cases this
  case stay => exact fun _ h => h
  case full =>
    intro c h
    show (settle now c .full).reading = false
    rw [(settle_frame now c .full).2.2.2.2.1]
    exact h
  case refuse => exact fun _ _ _ _ _ _ h => rfl
  case done => exact fun _ _ _ _ hr _ _ h => by rw [h] at hr; cases hr
  case flush =>
    intro c h
    show (flush now c).1.reading = false
    rw [(flush_eq now c).2.2.2.2.2.1]
    exact h
  case finish =>
    intro c h
    rcases finish_eq c with ⟨h₁, -⟩ | ⟨h₁, -⟩ <;> rw [h₁] <;> exact h

theorem Calm.quiet {c c' : Conn} (h : Calm c c') : Keeps (fun c => c.reading = false) c c' [] :=
  fun hr => by
    show c'.reading = false
    cases h' : c'.reading
    · rfl
    · have := h.2.2.2.2 h'
      rw [hr] at this
      cases this

/-- One that has stopped reading never reads again. -/
theorem step_reading (now : Nat) {c : Conn} (h : c.reading = false) (e : Event) :
    (step cfg now c e).1.reading = false := by
  refine step_of (Keeps fun c => c.reading = false) Keeps.trans
    (fun c => advance_quiet now c) ?stay ?receive ?answer ?expire ?quiet ?close ?respond ?took
    ?pulled ?sent c e h
  case respond => exact fun c seq r => Calm.quiet (respond_calm seq r c)
  case took => exact fun c seq index r => Calm.quiet (took_calm now seq index r c)
  case pulled => exact fun c seq index r => Calm.quiet (pulled_calm now seq index r c)
  case sent => exact fun c => Calm.quiet (sent_calm c)
  case stay => exact fun _ h => h
  case receive => exact fun _ _ _ _ _ h => h
  case answer =>
    intro c seq r h
    obtain ⟨slots, e, -⟩ := answer_eq seq r c
    rw [e]
    exact h
  case expire =>
    intro c h
    rcases expire_eq now c with e | e | ⟨-, e⟩ <;> rw [e] <;> first | exact h | rfl
  case quiet => exact fun _ _ => rfl
  case close => exact fun _ h => h

/-- At a deadline the connection stops reading: it writes what it owes, a `408` for a request
cut short, and closes. -/
theorem step_tick (now : Nat) {c : Conn} {t : Nat} (h : deadline cfg c = some t)
    (ht : t ≤ now) : (step cfg now c .tick).1.reading = false := by
  have hc : c.closed = false := by
    unfold deadline at h
    cases e : c.closed <;> simp_all
  simp only [step, hc, Bool.false_eq_true, ↓reduceIte]
  apply advance_quiet
  unfold expire
  rw [h]
  simp only [ht, ↓reduceIte]
  split <;> rfl

/-- The loop reads only a connection that is open and reading, and asks for at least one byte. -/
theorem wantsInput_room {c : Conn} (h : wantsInput cfg c = true) :
    c.closed = false ∧ c.reading = true ∧ 0 < room cfg c := by
  simp only [wantsInput, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.2⟩

/-! Answers -/

/-- An answer to a request that is not waiting, because it was answered already, never asked
or written, changes nothing. -/
theorem answer_ignored {seq : Nat} {c : Conn}
    (h : c.written ≤ seq → ∀ headOnly close, c.slots[seq - c.written]? ≠ some (.asked headOnly close))
    (r : Response) : answer seq r c = c := by
  unfold answer
  split
  · rename_i hw
    split
    · rename_i headOnly close e
      exact absurd e (h hw headOnly close)
    · rfl
  · rfl

/-- The answer to a request that is waiting is what will be written for it, as it asked. -/
theorem answer_waiting {seq : Nat} {c : Conn} {headOnly close : Bool} (hw : c.written ≤ seq)
    (h : c.slots[seq - c.written]? = some (.asked headOnly close)) (r : Response) :
    (answer seq r c).slots = c.slots.set (seq - c.written) (.ready (encode headOnly close r)) := by
  simp [answer, hw, h]

/-! What is handed on is what the reader reads -/

/-- Every request in `actions` is one the reader reads somewhere in the bytes of `c`, and `c'`
holds those bytes. -/
def Reads (cfg : Config) (c c' : Conn) (actions : List Action) : Prop :=
  c'.buffer = c.buffer ∧ ∀ s request, .submit s request ∈ actions →
    ∃ pos incoming stop, Request.read cfg.limits c.buffer pos = .done incoming stop
      ∧ incoming.request = request

theorem Reads.trans {a b c : Conn} {xs ys : List Action} (h₁ : Reads cfg a b xs)
    (h₂ : Reads cfg b c ys) : Reads cfg a c (xs ++ ys) := by
  refine ⟨h₂.1.trans h₁.1, fun s request h => ?_⟩
  rcases List.mem_append.1 h with h | h
  · exact h₁.2 s request h
  · rw [← h₁.1]
    exact h₂.2 s request h

theorem Reads.none {c c' : Conn} {actions : List Action} (hb : c'.buffer = c.buffer)
    (ha : ∀ a ∈ actions, a.submitted = none) : Reads cfg c c' actions :=
  ⟨hb, fun s request h => by cases ha _ h⟩

theorem Reads.quiet {c c' : Conn} {actions : List Action} (hb : c'.buffer = c.buffer)
    (ha : ∀ s request, .submit s request ∉ actions) : Reads cfg c c' actions :=
  ⟨hb, fun s request h => absurd h (ha s request)⟩

theorem advance_reads (now : Nat) (c : Conn) : Reads cfg c (advance cfg now c).1 (advance cfg now c).2 := by
  refine advance_of (Reads cfg) Reads.trans
    (take_of (Reads cfg) Reads.trans ?wait ?stay ?full ?refuse ?done ?begin ?upgrade) ?flush ?stream ?switch ?pump
    ?finish c
  case begin => exact fun c _ _ _ _ _ _ => Reads.quiet rfl (by simp)
  case upgrade => exact fun c _ _ _ _ _ _ => Reads.quiet rfl (by simp)
  case switch =>
    intro c
    obtain ⟨hb, -, -, -, -, ha⟩ := flushSwitch_frame c
    exact Reads.quiet hb fun s r h => (ha _ h).2.2 s r rfl
  case stream =>
    intro c
    obtain ⟨hb, -, -, hs, -⟩ := flushStream_frame (cfg := cfg) now c
    exact Reads.quiet hb fun s r h => (hs _ h).2 s r rfl
  case pump =>
    intro c
    obtain ⟨hb, -, -, -, -, ha⟩ := pump_frame (cfg := cfg) now c
    exact Reads.quiet hb fun s r h => (ha _ h).2.2 s r rfl
  case wait =>
    intro c _ _ _ _
    refine Reads.none (waitMore_frame c).1 fun a ha => ?_
    obtain ⟨s, b, rfl⟩ := waitMore_actions c a ha
    rfl
  case stay => exact fun c => Reads.none rfl (by simp)
  case full => exact fun c => Reads.none (settle_frame now c .full).1 (by simp)
  case refuse => exact fun c _ _ _ _ _ => Reads.none rfl (by simp)
  case done =>
    intro c incoming stop _ _ _ h
    refine ⟨rfl, fun s request hs => ?_⟩
    simp only [List.mem_singleton, Action.submit.injEq] at hs
    exact ⟨c.pos, incoming, stop, h, hs.2.symm⟩
  case flush =>
    intro c
    obtain ⟨-, -, ha, hb, -⟩ := flush_eq now c
    refine Reads.none hb fun a h => ?_
    rw [ha] at h
    obtain ⟨s, b, rfl⟩ := (flushSlots_spec c.written c.slots).2.2.2.2 a h
    rfl
  case finish =>
    intro c
    rcases finish_eq c with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rw [h₁, h₂] <;>
      exact Reads.none rfl (by simp [Action.submitted])

/-- Every request a connection hands on is one the strict reader (`Request.read`) reads in the
bytes the connection holds. -/
theorem step_submit_read (now : Nat) (c : Conn) (e : Event) {s : Nat} {request : Request}
    (h : .submit s request ∈ (step cfg now c e).2) :
    ∃ pos incoming stop, Request.read cfg.limits (step cfg now c e).1.buffer pos = .done incoming stop
      ∧ incoming.request = request := by
  have key : ∀ x : Conn, .submit s request ∈ (advance cfg now x).2 →
      ∃ pos incoming stop, Request.read cfg.limits (advance cfg now x).1.buffer pos
        = .done incoming stop ∧ incoming.request = request := fun x hx => by
    rw [(advance_reads now x).1]
    exact (advance_reads now x).2 s request hx
  unfold step at h ⊢
  by_cases hc : c.closed = true
  · simp [hc] at h
  · simp only [hc, Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases e with
    | received bytes =>
      dsimp only at h ⊢
      by_cases hr : c.reading = true
      · by_cases hroom : room cfg c < bytes.size
        · simp [hr, hroom] at h
        · simp only [hr, hroom, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
          exact key _ h
      · simp [hr] at h
    | ended => exact key _ h
    | broken => simp at h
    | answered seq r => exact key _ h
    | responded seq r => exact key _ h
    | took seq index r => exact key _ h
    | pulled seq index r => exact key _ h
    | sent => exact key _ h
    | tick => exact key _ h
    | stop => exact key _ h

/-! Streams -/

/-- The bytes of a streamed response, its head, the chunk of each part and the last chunk, are
`Response.wireChunked`, and the client's reader reads them back as the head with the parts, in
order, as its body, as soon as the last chunk is there, whatever follows. -/
theorem read_streamed {close : Bool} {r : Response} (hs : streamable close r = true)
    {parts : List ByteArray} (hparts : ∀ p ∈ parts, 0 < p.size ∧ p.size < 16 ^ 16)
    (hbody : (parts.foldl (· ++ ·) ByteArray.empty).size < 10 ^ 18) {limit : Nat}
    (hlimit : (streamHead close r ++ parts.foldl (· ++ Response.chunk ·) ByteArray.empty
      ++ lastChunk).size ≤ limit) (tail : ByteArray) (ended : Bool) :
    Response.read limit (streamHead close r ++ parts.foldl (· ++ Response.chunk ·) ByteArray.empty
        ++ lastChunk ++ tail) ended
      = .done (some { streamed close r with
          headers := ("transfer-encoding", "chunked") :: Response.lowered (streamed close r).headers
          body := parts.foldl (· ++ ·) ByteArray.empty }) := by
  have hw : streamHead close r ++ parts.foldl (· ++ Response.chunk ·) ByteArray.empty ++ lastChunk
      = Response.wireChunked { streamed close r with body := parts.foldl (· ++ ·) ByteArray.empty }
          parts :=
    rfl
  simp only [streamable, Bool.and_eq_true, bne_iff_ne, ne_eq] at hs
  obtain ⟨⟨hwr, h204⟩, h304⟩ := hs
  have hr : Response.writable { streamed close r with body := parts.foldl (· ++ ·) ByteArray.empty } := by
    simp only [Response.writable, streamed, Bool.and_eq_true, decide_eq_true_eq] at hwr ⊢
    obtain ⟨⟨⟨⟨h1, h2⟩, -⟩, -⟩, h5⟩ := hwr
    refine ⟨⟨⟨⟨h1, h2⟩, ?_⟩, hbody⟩, h5⟩
    simp [h204, h304]
  rw [hw] at hlimit ⊢
  exact Response.read_wireChunked hr ⟨h204, h304⟩ hparts rfl hlimit tail ended

/-- The answer to a request that streams that opens a stream makes its slot a stream whose head
is to be written first. -/
theorem respond_opens {seq : Nat} {c : Conn} {head : Request} {close : Bool}
    (hw : c.written ≤ seq) (h : c.slots[seq - c.written]? = some (.opened head false close))
    {r : Response} {mode : Stream.Mode} (hm : Stream.mode? r = some mode)
    (hs : streamable close r = true) :
    (respond seq r c).slots = c.slots.set (seq - c.written)
      (.stream { head, events := mode == .events, close, pending := streamHead close r
                 after := head.header? "last-event-id" }) := by
  simp [respond, hw, h, hm, hs]

/-- An answer to a request that is not waiting as one that streams or switches protocols
changes nothing. -/
theorem respond_ignored {seq : Nat} {c : Conn}
    (h : c.written ≤ seq → (∀ head headOnly close,
      c.slots[seq - c.written]? ≠ some (.opened head headOnly close))
      ∧ ∀ head, c.slots[seq - c.written]? ≠ some (.upgrading head)) (r : Response) :
    respond seq r c = c := by
  unfold respond
  split
  · rename_i hw
    split
    · rename_i head headOnly close e
      exact absurd e ((h hw).1 head headOnly close)
    · rename_i head e
      exact absurd e ((h hw).2 head)
    · rfl
  · rfl

/-- A part of bytes the system gives for the pull it was asked is to be written as its chunk,
after what came before it. -/
theorem pulled_part {seq index : Nat} {c : Conn} {o : Outflow} (hw : c.written ≤ seq)
    (h : c.slots[seq - c.written]? = some (.stream o)) (hask : o.asking = true)
    (hi : o.index = index) (hst : o.state = .going) (hev : o.events = false) {r : Response}
    {d : ByteArray} (hp : Stream.part r = .data d) (hd : d.size ≤ cfg.part_max) :
    (pulled cfg now seq index r c).slots = c.slots.set (seq - c.written)
      (.stream { o with asking := false, index := index + 1
                        pending := o.pending ++ Response.chunk d }) := by
  have hb : r.body = d := by
    unfold Stream.part at hp
    repeat' split at hp
    all_goals (cases hp <;> rfl)
  simp [pulled, hw, h, hask, hi, hst, hp, Outflow.accept, hev, hb, show ¬ cfg.part_max < d.size by omega]

/-- An answer to a pull that is not the one a stream waits for changes nothing. -/
theorem pulled_ignored {seq index : Nat} {c : Conn}
    (h : ∀ o, c.written ≤ seq → c.slots[seq - c.written]? = some (.stream o) →
      ¬(o.asking = true ∧ o.index = index ∧ o.state = .going)) (r : Response) :
    pulled cfg now seq index r c = c := by
  unfold pulled
  split
  · rename_i hw
    split
    · rename_i o e
      have := h o hw e
      split
      · rfl
      · rename_i hne
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', Bool.not_eq_false] at hne
        exact absurd ⟨hne.1.1, hne.1.2, hne.2⟩ this
    · rfl
  · rfl

/-- A part larger than `part_max` cuts its stream short. -/
theorem pulled_large {seq index : Nat} {c : Conn} {o : Outflow} (hw : c.written ≤ seq)
    (h : c.slots[seq - c.written]? = some (.stream o)) (hask : o.asking = true)
    (hi : o.index = index) (hst : o.state = .going) {r : Response} {d : ByteArray}
    (hp : Stream.part r = .data d) (hd : cfg.part_max < d.size) :
    (pulled cfg now seq index r c).slots = c.slots.set (seq - c.written)
      (.stream { o with asking := false, index := index + 1, state := .cut }) := by
  simp [pulled, hw, h, hask, hi, hst, hp, hd]

/-- A streamed response the system ended, at the front, writes what has come of it and then its
last chunk, and leaves. -/
theorem flushStream_ended {c : Conn} (hc : c.closed = false) {o : Outflow} {rest : List Slot}
    (hs : c.slots = .stream o :: rest) (hst : o.state = .ended) :
    (flushStream cfg now c).2
        = (if o.pending.isEmpty then [] else [.part c.written o.pending]) ++ [.write c.written lastChunk]
      ∧ (flushStream cfg now c).1.written = c.written + 1 ∧ (flushStream cfg now c).1.slots = rest := by
  unfold flushStream
  cases hp : o.pending.isEmpty <;> simp [hc, hs, hst, hp]

/-- A streamed response going on, at the front, writes what has come of it; it asks for the next
part only when nothing written is unsent and no pull is with the system. -/
theorem flushStream_going {c : Conn} (hc : c.closed = false) {o : Outflow} {rest : List Slot}
    (hs : c.slots = .stream o :: rest) (hst : o.state = .going) :
    (∀ s b, .part s b ∈ (flushStream cfg now c).2 → s = c.written ∧ (b = o.pending ∨ b = heartbeatChunk))
      ∧ (∀ s k request, .pull s k request ∈ (flushStream cfg now c).2 →
          c.unsent = false ∧ o.pending.isEmpty ∧ o.asking = false ∧ s = c.written ∧ k = o.index
            ∧ request = Stream.pull o.head o.index o.after)
      ∧ (∀ s b, .write s b ∉ (flushStream cfg now c).2) := by
  unfold flushStream
  cases hp : o.pending.isEmpty <;> cases hu : c.unsent <;> cases ha : o.asking <;>
    simp [hc, hs, hst, hp, ha] <;> (repeat' split) <;> simp_all

/-- A stream not at the front writes nothing and asks for nothing. -/
theorem flushStream_other {c : Conn} (h : ∀ o rest, c.slots ≠ .stream o :: rest) :
    flushStream cfg now c = (c, []) := by
  unfold flushStream
  split
  · rfl
  · split
    · rename_i o rest hs
      exact absurd hs (h o rest)
    · rfl

/-- Of a body framed by its length, a piece is the bytes of the buffer from the connection's
position to where the piece ends, which is within what is left of the body; what is left after
it is the framing, and it is the last piece exactly when nothing is left. So the pieces of such a
body, one after another, are its bytes in order: the body the strict reader reads
(`Request.read` takes the `n` bytes after the head). -/
theorem gather_length {bytes : ByteArray} :
    ∀ {fuel pos taken left : Nat} {acc data : ByteArray} {stop : Nat}
      {framing : Inflow.Framing} {last : Bool}, 0 < left →
      Inflow.gather cfg bytes fuel pos taken (.length left) acc = .piece data stop framing last →
      pos ≤ stop ∧ stop ≤ pos + left ∧ data = acc ++ bytes.extract pos stop
        ∧ framing = .length (left - (stop - pos)) ∧ (last = true ↔ stop = pos + left)
  | 0, pos, taken, left, acc, data, stop, framing, last, hl, h => by
    simp only [Inflow.gather] at h
    split at h
    · cases h
    · cases h
      refine ⟨Nat.le_refl _, by omega, by simp, by simp, by simp; omega⟩
  | fuel + 1, pos, taken, left, acc, data, stop, framing, last, hl, h => by
    simp only [Inflow.gather, Inflow.next] at h
    by_cases hm0 : min (max 1 cfg.piece_max - acc.size) (min (bytes.size - pos) left) = 0
    · simp only [hm0, ↓reduceIte] at h
      split at h
      · cases h
      · cases h
        refine ⟨Nat.le_refl _, by omega, by simp, by simp, by simp; omega⟩
    · simp only [hm0, ↓reduceIte] at h
      split at h
      · cases h
        refine ⟨by omega, by omega, rfl, by simp, by simp; omega⟩
      · rename_i hnot
        have hlast : ¬ left = min (max 1 cfg.piece_max - acc.size) (min (bytes.size - pos) left) := by
          intro e
          apply hnot
          simp only [Bool.or_eq_true, decide_eq_true_eq]
          exact .inl e
        obtain ⟨h1, h2, h3, h4, h5⟩ := gather_length (by omega) h
        refine ⟨by omega, by omega, ?_, ?_, ?_⟩
        · rw [h3, ByteArray.append_assoc, ByteArray.extract_append_extract]
          congr 2 <;> omega
        · rw [h4]
          congr 1
          omega
        · rw [h5]
          omega

/-- A piece handed on is the next bytes of the body as `Inflow.gather` reads them at the
connection's position in its buffer, or the piece the system was too busy to take, offered
again; one at a time. -/
theorem pump_piece {c : Conn} {s k : Nat} {request : Request}
    (h : .piece s k request ∈ (pump cfg now c).2) :
    ∃ f, c.inflow = some f ∧ s = f.seq ∧ k = f.index
      ∧ ((f.asked = none ∧ ∃ data stop framing last,
            Inflow.gather cfg c.buffer (max 1 cfg.piece_max) c.pos f.taken f.framing .empty
              = .piece data stop framing last
            ∧ request = Stream.piece f.head k data last
            ∧ (pump cfg now c).1.inflow.bind (·.asked) = some (data, last))
        ∨ ∃ data last, f.asked = some (data, last) ∧ request = Stream.piece f.head k data last) := by
  unfold pump at h ⊢
  split at h
  · simp at h
  · rename_i f hf
    refine ⟨f, hf, ?_⟩
    split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · rename_i data last ha
          split at h
          · simp only [List.mem_singleton, Action.piece.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            exact ⟨rfl, rfl, .inr ⟨data, last, ha, rfl⟩⟩
          · simp at h
        · rename_i ha
          dsimp only at h ⊢
          split at h
          · split at h <;> simp at h
          · split at h <;> simp at h
          · rename_i data stop framing last hg
            simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton,
              Action.piece.injEq] at h
            rcases h with ⟨-, h⟩ | ⟨rfl, rfl, rfl⟩
            · cases h
            · refine ⟨rfl, rfl, .inl ⟨ha, data, stop, framing, last, hg, rfl, ?_⟩⟩
              repeat' split
              all_goals simp_all [settle]
              all_goals (split <;> rfl)

/-! What is written -/

theorem sendable_writable (close : Bool) (r : Response) : (sendable close r).writable = true := by
  unfold sendable
  dsimp only
  split
  · assumption
  · decide

/-- What a connection writes for a response to a request other than `HEAD` is read back by the
client's reader as that response, as soon as its last byte is there, whatever follows. -/
theorem read_encode (close : Bool) (r : Response) {limit : Nat}
    (hlimit : (encode false close r).size ≤ limit) (tail : ByteArray) (ended : Bool) :
    Response.read limit (encode false close r ++ tail) ended
      = .done (some { sendable close r with
          headers := ("content-length", toString (sendable close r).body.size)
            :: Response.lowered (sendable close r).headers }) :=
  Response.read_wire (sendable_writable close r) hlimit tail ended

/-! Connections -/

/-- No more connections are open than the bound. -/
theorem Count.admit_le {n : Count} {connections_max : Nat} (h : n.count ≤ connections_max) :
    (n.admit connections_max).2.count ≤ connections_max := by
  unfold Count.admit
  split
  · rename_i hc
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc
    exact hc.2
  · exact h

/-- None is taken while the server stops. -/
theorem Count.admit_stopping {n : Count} (h : n.stopping = true) (connections_max : Nat) :
    (n.admit connections_max).1 = false := by
  simp [Count.admit, h]

end Lanes.Http.Conn
