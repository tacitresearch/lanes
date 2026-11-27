/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Http.Conn
public import Lanes.Http.ReadRequestSound

/-!
What a connection of the HTTP server does (`Lanes.Http.Conn`), for every configuration and every
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
  | .submit seq _ => some seq
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
        [.submit (next c) incoming.request]) :
    ∀ fuel c, P c (take cfg now fuel c).1 (take cfg now fuel c).2
  | 0, c => hstay c
  | fuel + 1, c => by
    simp only [take]
    by_cases hc : (c.closed || !c.reading) = true
    · simp only [hc, ↓reduceIte]
      exact hstay c
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_true, Bool.not_eq_false] at hc
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
          · rename_i h
            exact hwait c hc.1 hc.2 hl h
          · rename_i why h
            exact hrefuse c why hc.1 hc.2 hl h
          · rename_i incoming stop h
            exact trans (hdone c incoming stop hc.1 hc.2 hl h) (take_of hwait hstay hfull hrefuse hdone fuel _)

include trans in
theorem advance_of
    (htake : ∀ fuel c, P c (take cfg now fuel c).1 (take cfg now fuel c).2)
    (hflush : ∀ c, P c (flush now c).1 (flush now c).2)
    (hfinish : ∀ c, P c (finish c).1 (finish c).2) (c : Conn) :
    P c (advance cfg now c).1 (advance cfg now c).2 := by
  have h1 := hflush c
  rcases e1 : flush now c with ⟨c1, a1⟩
  rw [e1] at h1
  have h2 := htake (cfg.inflight_max + 1) c1
  rcases e2 : take cfg now (cfg.inflight_max + 1) c1 with ⟨c2, a2⟩
  rw [e2] at h2
  have h3 := hflush c2
  rcases e3 : flush now c2 with ⟨c3, a3⟩
  rw [e3] at h3
  have h4 := hfinish c3
  rcases e4 : finish c3 with ⟨c4, a4⟩
  rw [e4] at h4
  simp only [advance, e1, e2, e3, e4]
  exact trans (trans (trans h1 h2) h3) h4

include trans in
theorem step_of
    (hadvance : ∀ c, P c (advance cfg now c).1 (advance cfg now c).2)
    (hstay : ∀ c, P c c [])
    (hreceive : ∀ c bytes, c.closed = false → c.reading = true → bytes.size ≤ room cfg c →
      P c (receive bytes c) [])
    (hanswer : ∀ c seq r, P c (answer seq r c) [])
    (hexpire : ∀ c, P c (expire cfg now c) [])
    (hquiet : ∀ c, P c { c with reading := false } [])
    (hclose : ∀ c, P c { c with closed := true } [.close]) (c : Conn) (e : Event) :
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

theorem step_writes (now : Nat) (c : Conn) (e : Event) :
    Writes c (step cfg now c e).1 (step cfg now c e).2 := by
  refine step_of Writes Writes.trans (fun c => advance_of Writes Writes.trans
      (take_of Writes Writes.trans ?wait ?stay ?full ?refuse ?done) ?flush ?finish c)
    ?stay ?receive ?answer ?expire ?quiet ?close c e
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
  case quiet => exact fun c => Writes.none rfl (by simp)
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

theorem step_submits (now : Nat) (c : Conn) (e : Event) :
    Submits c (step cfg now c e).1 (step cfg now c e).2 := by
  refine step_of Submits Submits.trans (fun c => advance_of Submits Submits.trans
      (take_of Submits Submits.trans ?wait ?stay ?full ?refuse ?done) ?flush ?finish c)
    ?stay ?receive ?answer ?expire ?quiet ?close c e
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
  case quiet => exact fun c => Submits.none (Nat.le_refl _) (by simp)
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

theorem step_buffer (now : Nat) (c : Conn) (e : Event) (h : Bounded cfg c) :
    Bounded cfg (step cfg now c e).1 := by
  refine step_of (Keeps (Bounded cfg)) Keeps.trans
    (fun c => advance_of (Keeps (Bounded cfg)) Keeps.trans
      (take_of (Keeps (Bounded cfg)) Keeps.trans ?wait ?stay ?full ?refuse ?done) ?flush ?finish c)
    ?stay ?receive ?answer ?expire ?quiet ?close c e h
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
  case quiet => exact fun _ h => h
  case close => exact fun _ h => h

/-- The buffer never holds more than `message_max` bytes. -/
theorem run_buffer (c : Conn) (events : List (Nat × Event)) (h : Bounded cfg c) :
    Bounded cfg (run cfg c events).1 :=
  run_of (Keeps (Bounded cfg)) Keeps.trans (fun _ h => h) (fun now c e => step_buffer now c e)
    c events h

theorem step_slots (now : Nat) (c : Conn) (e : Event) (h : c.slots.length ≤ cfg.inflight_max) :
    (step cfg now c e).1.slots.length ≤ cfg.inflight_max := by
  refine step_of (Keeps fun c => c.slots.length ≤ cfg.inflight_max) Keeps.trans
    (fun c => advance_of (Keeps fun c => c.slots.length ≤ cfg.inflight_max) Keeps.trans
      (take_of (Keeps fun c => c.slots.length ≤ cfg.inflight_max) Keeps.trans ?wait ?stay ?full ?refuse ?done) ?flush ?finish c)
    ?stay ?receive ?answer ?expire ?quiet ?close c e h
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
  case quiet => exact fun _ h => h
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
    (take_of (Keeps fun c => c.reading = false) Keeps.trans ?wait ?stay ?full ?refuse ?done) ?flush
    ?finish c h
  case wait => exact fun _ _ hr _ _ h => by rw [h] at hr; cases hr
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

/-- One that has stopped reading never reads again. -/
theorem step_reading (now : Nat) {c : Conn} (h : c.reading = false) (e : Event) :
    (step cfg now c e).1.reading = false := by
  refine step_of (Keeps fun c => c.reading = false) Keeps.trans
    (fun c => advance_quiet now c) ?stay ?receive ?answer ?expire ?quiet ?close c e h
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

theorem advance_reads (now : Nat) (c : Conn) : Reads cfg c (advance cfg now c).1 (advance cfg now c).2 := by
  refine advance_of (Reads cfg) Reads.trans
    (take_of (Reads cfg) Reads.trans ?wait ?stay ?full ?refuse ?done) ?flush ?finish c
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
    | tick => exact key _ h
    | stop => exact key _ h

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
