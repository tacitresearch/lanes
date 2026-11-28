/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std

/-!
# A pool of connections, as a pure function

Which connection a client is handed, when one is opened or closed, and who waits or is refused,
decided here; the IO (`Lanes/Services/Postgres/IO/Pool.lean`) opens and closes connections, keeps
the clients waiting, and says when a connection opened or failed to, was handed back, and when a
client's deadline passed. Connections and clients are named by numbers the IO chooses.

At most `max` connections are open or being opened (`Pool.run_size`), and at most
`waiting_max` clients wait (`Pool.run_waiting`). A connection handed back as not reusable (it
broke, or was left in a transaction) is closed and never handed out again
(`Pool.never_again`), given that the IO never says a connection opened under a number it used
before. A connection is opened only for a client waiting that no connection being opened will
serve, so a failing server is not asked again and again: each failure refuses the oldest client
waiting. A connection idle in the pool is not watched; one that broke there is found when it
is used, handed back as not reusable, and closed.
-/

@[expose] public section

namespace Lanes.Postgres.Pool

/-- Every limit is explicit (rule 2.6). -/
structure Config where
  /-- Connections open, handed out, idle or being opened, at most. -/
  max : Nat := 10
  waiting_max : Nat := 100

inductive Refusal where
  /-- `waiting_max` clients wait already. -/
  | full
  /-- The client's deadline passed. -/
  | timeout
  /-- A connection could not be opened. -/
  | unavailable
  deriving DecidableEq, Repr, Hashable

inductive Event where
  | checkout (client : Nat)
  | opened (conn : Nat)
  | failed
  /-- The connection handed back, and whether it may be handed out again. -/
  | checkin (conn : Nat) (reusable : Bool)
  /-- The client's deadline passed. -/
  | expire (client : Nat)
  deriving DecidableEq, Repr

inductive Action where
  /-- Open a connection, and say `opened` or `failed`. -/
  | connect
  | give (client conn : Nat)
  | refuse (client : Nat) (why : Refusal)
  | close (conn : Nat)
  deriving DecidableEq, Repr

structure State where
  idle : List Nat := []
  busy : List Nat := []
  opening : Nat := 0
  /-- Oldest first. -/
  waiting : List Nat := []
  deriving DecidableEq, Repr, Hashable

namespace State

/-- The connections open or being opened. -/
def size (p : State) : Nat := p.idle.length + p.busy.length + p.opening

end State

variable (cfg : Config)

/-- One connection more, if a client waits that no connection being opened will serve, and
there is room. -/
def refill (p : State) : State × List Action :=
  if p.opening < p.waiting.length ∧ p.size < cfg.max then ({ p with opening := p.opening + 1 }, [.connect])
  else (p, [])

/-- A connection that may be used: to the oldest client waiting, or idle. -/
def hand (p : State) (c : Nat) : State × List Action :=
  match p.waiting with
  | w :: rest => ({ p with waiting := rest, busy := c :: p.busy }, [.give w c])
  | [] => ({ p with idle := c :: p.idle }, [])

def onCheckout (p : State) (w : Nat) : State × List Action :=
  match p.idle with
  | c :: rest => ({ p with idle := rest, busy := c :: p.busy }, [.give w c])
  | [] =>
    if cfg.waiting_max ≤ p.waiting.length then (p, [.refuse w .full])
    else refill cfg { p with waiting := p.waiting ++ [w] }

def onOpened (p : State) (c : Nat) : State × List Action :=
  if p.opening = 0 then (p, [.close c]) else hand { p with opening := p.opening - 1 } c

def onFailed (p : State) : State × List Action :=
  if p.opening = 0 then (p, [])
  else
    match p.waiting with
    | w :: rest =>
      let (p, more) := refill cfg { p with opening := p.opening - 1, waiting := rest }
      (p, .refuse w .unavailable :: more)
    | [] => ({ p with opening := p.opening - 1 }, [])

/-- A connection handed back that is not reusable leaves the pool, wherever it was in it. -/
def onCheckin (p : State) (c : Nat) (reusable : Bool) : State × List Action :=
  if reusable then
    if c ∈ p.busy then hand { p with busy := p.busy.filter (· ≠ c) } c else (p, [])
  else if c ∈ p.busy ∨ c ∈ p.idle then
    let (p, more) := refill cfg { p with busy := p.busy.filter (· ≠ c), idle := p.idle.filter (· ≠ c) }
    (p, .close c :: more)
  else (p, [])

def onExpire (p : State) (w : Nat) : State × List Action :=
  if w ∈ p.waiting then ({ p with waiting := p.waiting.filter (· ≠ w) }, [.refuse w .timeout])
  else (p, [])

def step (p : State) : Event → State × List Action
  | .checkout w => onCheckout cfg p w
  | .opened c => onOpened p c
  | .failed => onFailed cfg p
  | .checkin c reusable => onCheckin cfg p c reusable
  | .expire w => onExpire p w

def run (p : State) : List Event → State × List Action
  | [] => (p, [])
  | e :: rest =>
    let (p, first) := step cfg p e
    let (p, later) := run p rest
    (p, first ++ later)

/-! ## The bound -/

theorem refill_size (p : State) (h : p.size ≤ cfg.max) : (refill cfg p).1.size ≤ cfg.max := by
  unfold refill
  split
  · rename_i hr
    simp only [State.size] at hr ⊢
    omega
  · exact h

theorem refill_opening (p : State) : (refill cfg p).1.opening ≤ p.opening + 1 := by
  unfold refill
  split <;> simp

theorem refill_waiting (p : State) : (refill cfg p).1.waiting = p.waiting := by
  unfold refill
  split <;> rfl

theorem hand_size (p : State) (c : Nat) : (hand p c).1.size = p.size + 1 := by
  unfold hand
  split <;> simp [State.size] <;> omega

theorem length_filter_ne {l : List Nat} {c : Nat} (h : c ∈ l) :
    (l.filter (· ≠ c)).length < l.length :=
  List.length_filter_lt_length_iff_exists.mpr ⟨c, h, by simp⟩

theorem length_filter_le (l : List Nat) (c : Nat) : (l.filter (· ≠ c)).length ≤ l.length :=
  List.length_filter_le _ _

/-- No step opens more than `max` connections. -/
theorem step_size (p : State) (e : Event) (h : p.size ≤ cfg.max) :
    (step cfg p e).1.size ≤ cfg.max := by
  cases e with
  | checkout w =>
    simp only [step, onCheckout]
    split
    · simp only [State.size] at h ⊢
      simp_all
      omega
    · split
      · exact h
      · exact refill_size cfg _ (by simpa [State.size] using h)
  | opened c =>
    simp only [step, onOpened]
    split
    · exact h
    · rw [hand_size]
      simp only [State.size] at h ⊢
      omega
  | failed =>
    simp only [step, onFailed]
    split
    · exact h
    · split
      · exact refill_size cfg _ (by simp only [State.size] at h ⊢; omega)
      · simp only [State.size] at h ⊢
        omega
  | checkin c reusable =>
    simp only [step, onCheckin]
    split
    · split
      · rw [hand_size]
        have := length_filter_ne ‹c ∈ p.busy›
        simp only [State.size] at h ⊢
        omega
      · exact h
    · split
      · apply refill_size
        have := length_filter_le p.busy c
        have := length_filter_le p.idle c
        simp only [State.size] at h ⊢
        omega
      · exact h
  | expire w =>
    simp only [step, onExpire]
    split
    · exact h
    · exact h

/-- At most `max` connections are ever open or being opened. -/
theorem run_size (p : State) (events : List Event) (h : p.size ≤ cfg.max) :
    (run cfg p events).1.size ≤ cfg.max := by
  induction events generalizing p with
  | nil => exact h
  | cons e rest ih => exact ih _ (step_size cfg p e h)

theorem step_waiting (p : State) (e : Event) (h : p.waiting.length ≤ cfg.waiting_max) :
    (step cfg p e).1.waiting.length ≤ cfg.waiting_max := by
  cases e with
  | checkout w =>
    simp only [step, onCheckout]
    split
    · exact h
    · split
      · exact h
      · rw [refill_waiting]
        simp only [List.length_append, List.length_singleton]
        omega
  | opened c =>
    simp only [step, onOpened]
    split
    · exact h
    · unfold hand
      split
      · rename_i w rest hw
        simp only at hw
        simp only [hw, List.length_cons] at h
        simp only
        omega
      · exact h
  | failed =>
    simp only [step, onFailed]
    split
    · exact h
    · split
      · rename_i w rest hw
        rw [refill_waiting]
        simp only [hw, List.length_cons] at h ⊢
        omega
      · exact h
  | checkin c reusable =>
    simp only [step, onCheckin]
    split
    · split
      · unfold hand
        split
        · rename_i w rest hw
          simp only at hw
          simp only [hw, List.length_cons] at h
          simp only
          omega
        · exact h
      · exact h
    · split
      · rw [refill_waiting]
        exact h
      · exact h
  | expire w =>
    simp only [step, onExpire]
    split
    · exact Nat.le_trans (length_filter_le _ _) h
    · exact h

/-- At most `waiting_max` clients ever wait. -/
theorem run_waiting (p : State) (events : List Event) (h : p.waiting.length ≤ cfg.waiting_max) :
    (run cfg p events).1.waiting.length ≤ cfg.waiting_max := by
  induction events generalizing p with
  | nil => exact h
  | cons e rest ih => exact ih _ (step_waiting cfg p e h)

/-! ## A broken connection is never handed out again -/

/-- The connection `c` is not in the pool. -/
def Out (p : State) (c : Nat) : Prop := c ∉ p.idle ∧ c ∉ p.busy

theorem refill_out {p : State} {c : Nat} (h : Out p c) :
    Out (refill cfg p).1 c ∧ ∀ w, .give w c ∉ (refill cfg p).2 := by
  unfold refill
  split <;> simp_all [Out]

/-- A connection not in the pool is handed out only by `opened`, under its number. -/
theorem step_out (p : State) (e : Event) {c : Nat} (h : Out p c) (he : e ≠ .opened c) :
    Out (step cfg p e).1 c ∧ ∀ w, .give w c ∉ (step cfg p e).2 := by
  obtain ⟨hi, hb⟩ := h
  cases e with
  | checkout w =>
    simp only [step, onCheckout]
    split
    · rename_i d rest hd
      have : d ≠ c := fun hdc => hi (by simp [hd, hdc])
      simp_all [Out]
    · split
      · simp_all [Out]
      · exact refill_out cfg ⟨hi, hb⟩
  | opened d =>
    have hd : c ≠ d := fun h => he (by rw [h])
    simp only [step, onOpened]
    split
    · simp_all [Out]
    · unfold hand
      split <;> simp_all [Out]
  | failed =>
    simp only [step, onFailed]
    split
    · simp_all [Out]
    · split
      · obtain ⟨h1, h2⟩ := refill_out cfg (p := { p with opening := p.opening - 1, waiting := _ })
          (c := c) ⟨hi, hb⟩
        exact ⟨h1, by simpa using h2⟩
      · simp_all [Out]
  | checkin d reusable =>
    simp only [step, onCheckin]
    split
    · split
      · have : c ≠ d := fun hdc => hb (hdc ▸ ‹d ∈ p.busy›)
        unfold hand
        split <;> simp_all [Out]
      · simp_all [Out]
    · split
      · obtain ⟨h1, h2⟩ := refill_out cfg
          (p := { p with busy := p.busy.filter (· ≠ d), idle := p.idle.filter (· ≠ d) }) (c := c)
          ⟨by simp [hi], by simp [hb]⟩
        exact ⟨h1, by simpa using h2⟩
      · simp_all [Out]
  | expire w =>
    simp only [step, onExpire]
    split <;> simp_all [Out]

/-- A connection handed back as not reusable is out of the pool. -/
theorem checkin_out (p : State) (c : Nat) : Out (step cfg p (.checkin c false)).1 c := by
  simp only [step, onCheckin, Bool.false_eq_true, ↓reduceIte]
  split
  · exact (refill_out cfg (p := { p with busy := p.busy.filter (· ≠ c), idle := p.idle.filter (· ≠ c) })
      (c := c) ⟨by simp, by simp⟩).1
  · rename_i h
    simp only [not_or] at h
    exact ⟨h.2, h.1⟩

theorem run_out (p : State) (events : List Event) {c : Nat} (h : Out p c)
    (he : ∀ e ∈ events, e ≠ .opened c) : ∀ w, .give w c ∉ (run cfg p events).2 := by
  induction events generalizing p with
  | nil => simp [run]
  | cons e rest ih =>
    have := step_out cfg p e h (he e (List.mem_cons_self ..))
    intro w hw
    simp only [run, List.mem_append] at hw
    rcases hw with hw | hw
    · exact this.2 w hw
    · exact ih _ this.1 (fun e h => he e (List.mem_cons_of_mem _ h)) w hw

/-- A connection handed back as not reusable is never handed out again, provided the IO never
says a connection opened under its number again. -/
theorem never_again (p : State) (c : Nat) (rest : List Event) (he : ∀ e ∈ rest, e ≠ .opened c) :
    ∀ w, .give w c ∉ (run cfg p (.checkin c false :: rest)).2 := by
  intro w hw
  simp only [run, List.mem_append] at hw
  rcases hw with hw | hw
  · simp only [step, onCheckin, Bool.false_eq_true, ↓reduceIte] at hw
    split at hw
    · simp only [List.mem_cons, reduceCtorEq, false_or] at hw
      exact (refill_out cfg (p := { p with busy := p.busy.filter (· ≠ c), idle := p.idle.filter (· ≠ c) })
        (c := c) ⟨by simp, by simp⟩).2 w hw
    · simp at hw
  · exact run_out cfg _ rest (checkin_out cfg p c) he w hw

end Lanes.Postgres.Pool
