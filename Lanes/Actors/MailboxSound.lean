/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Actors.Mailbox

/-!
What a `Mailbox` does, for every capacity and every sequence of operations: what a `take`
returns, who is refused, and that nobody who sleeps or waits is forgotten. The operations are
the calls the runtime shell makes (`Op`), run one after another by `exec`, and the invariant
`Sound` holds of every mailbox they reach from an empty one.
-/

@[expose] public section

namespace Lanes.Mailbox

variable {α W : Type}

inductive Op (α W : Type) where
  | offer (x : α)
  | offerOrWait (x : α) (room : W)
  | urge (x : α)
  | take
  | rest (wake : W)
  | close

inductive Reply (α W : Type) where
  | offered (answer : Offered W)
  | urged (answer : Option (Option W))
  | took (taken : Taken α W)
  | rested (asleep : Bool)
  | closed (wake : List W)

def Op.apply (capacity : Nat) : Op α W → Mailbox α W → Reply α W × Mailbox α W
  | .offer x, m => ((.offered (m.offer capacity x).1), (m.offer capacity x).2)
  | .offerOrWait x room, m =>
    ((.offered (m.offerOrWait capacity x room).1), (m.offerOrWait capacity x room).2)
  | .urge x, m => ((.urged (m.urge x).1), (m.urge x).2)
  | .take, m => ((.took m.take.1), m.take.2)
  | .rest wake, m => ((.rested (m.rest wake).1), (m.rest wake).2)
  | .close, m => ((.closed m.close.1), m.close.2)

def exec (capacity : Nat) : List (Op α W) → Mailbox α W → List (Reply α W) × Mailbox α W
  | [], m => ([], m)
  | op :: ops, m =>
    ((op.apply capacity m).1 :: (exec capacity ops (op.apply capacity m).2).1,
      (exec capacity ops (op.apply capacity m).2).2)

def Reachable (capacity : Nat) (m : Mailbox α W) : Prop :=
  ∃ ops : List (Op α W), (exec capacity ops {}).2 = m

/-- Something went in. -/
def Reply.admitted : Reply α W → Bool
  | .offered (.taken _) | .urged (some _) => true
  | _ => false

/-- Whoever the shell is to wake on this reply. -/
def Reply.woken : Reply α W → List W
  | .offered (.taken wake) | .urged (some wake) => wake.toList
  | .took taken => taken.wake
  | .closed wake => wake
  | _ => []

def Op.urgentIn : Op α W → Reply α W → List α
  | .urge x, .urged (some _) => [x]
  | _, _ => []

def Op.boundedIn : Op α W → Reply α W → List α
  | .offer x, .offered (.taken _) | .offerOrWait x _, .offered (.taken _) => [x]
  | _, _ => []

def Op.waitedIn : Op α W → Reply α W → List W
  | .offerOrWait _ room, .offered .full => [room]
  | _, _ => []

theorem Op.waitedIn_reverse (op : Op α W) (r : Reply α W) :
    (op.waitedIn r).reverse = op.waitedIn r := by
  unfold Op.waitedIn
  split <;> simp

def Op.resetsSleeper : Op α W → Bool
  | .rest _ | .close => true
  | _ => false

/-- What came in from other shards during `ops`, in the order it came. -/
def urgentIn (capacity : Nat) (ops : List (Op α W)) (m : Mailbox α W) : List α :=
  (List.zipWith Op.urgentIn ops (exec capacity ops m).1).flatten

/-- What was taken in under the bound during `ops`, in the order it came. -/
def boundedIn (capacity : Nat) (ops : List (Op α W)) (m : Mailbox α W) : List α :=
  (List.zipWith Op.boundedIn ops (exec capacity ops m).1).flatten

/-- The senders that found no room during `ops` and wait, in the order they came. -/
def waitedIn (capacity : Nat) (ops : List (Op α W)) (m : Mailbox α W) : List W :=
  (List.zipWith Op.waitedIn ops (exec capacity ops m).1).flatten

structure Sound (capacity : Nat) (m : Mailbox α W) : Prop where
  /-- `count` is the number of bounded items. -/
  count_eq : m.count = m.items.length
  /-- The bounded lane never holds more than `capacity`. -/
  bounded : m.items.length ≤ capacity
  /-- A sender waits only while the bounded lane is full. -/
  waiting_full : m.waiting ≠ [] → capacity ≤ m.items.length
  /-- The shard sleeps only on an open mailbox with nothing in it. -/
  asleep_empty : m.sleeper.isSome → m.items = [] ∧ m.urgent = [] ∧ m.closed = false
  /-- Nobody sleeps on or waits for a closed mailbox. -/
  closed_quiet : m.closed = true → m.sleeper = none ∧ m.waiting = []

section Steps

variable {capacity : Nat} {m : Mailbox α W}

theorem offer_full_iff {x : α} :
    (m.offer capacity x).1 = .full ↔ m.closed = false ∧ capacity ≤ m.count := by
  cases hc : m.closed <;> by_cases hr : m.count < capacity <;> simp [offer, hc, hr] <;> omega

theorem offerOrWait_eq_offer {x : α} {room : W} :
    (m.offerOrWait capacity x room).1 = (m.offer capacity x).1 := by
  cases hc : m.closed <;> by_cases hr : m.count < capacity <;> simp [offerOrWait, offer, hc, hr]

theorem offerOrWait_full_iff {x : α} {room : W} :
    (m.offerOrWait capacity x room).1 = .full ↔ m.closed = false ∧ capacity ≤ m.count := by
  rw [offerOrWait_eq_offer, offer_full_iff]

theorem offer_taken {x : α} {wake : Option W} (h : (m.offer capacity x).1 = .taken wake) :
    wake = m.sleeper := by
  cases hc : m.closed <;> by_cases hr : m.count < capacity <;> simp_all [offer]

theorem urge_some {x : α} {wake : Option W} (h : (m.urge x).1 = some wake) :
    wake = m.sleeper := by
  cases hc : m.closed <;> simp_all [urge]

theorem rest_eq_true_iff {wake : W} :
    (m.rest wake).1 = true ↔ m.closed = false ∧ m.items = [] ∧ m.urgent = [] := by
  cases hc : m.closed <;> cases hi : m.items <;> cases hu : m.urgent <;> simp [rest, hc, hi, hu]

/-- The shard stays awake while something is waiting to be taken or the mailbox is closed. -/
theorem rest_eq_false {wake : W} (h : m.closed = true ∨ m.take.1.batch ≠ []) :
    (m.rest wake).1 = false := by
  cases hr : (m.rest wake).1
  · rfl
  · obtain ⟨hc, hi, hu⟩ := rest_eq_true_iff.mp hr
    simp [take, hc, hi, hu] at h

theorem sound_empty : Sound capacity ({} : Mailbox α W) where
  count_eq := rfl
  bounded := Nat.zero_le _
  waiting_full := by simp
  asleep_empty := by simp
  closed_quiet := by simp

theorem Sound.apply (h : Sound capacity m) (op : Op α W) :
    Sound capacity (op.apply capacity m).2 := by
  obtain ⟨hcount, hbound, hwait, hasleep, hclosed⟩ := h
  cases op with
  | offer x | offerOrWait x room =>
    have hwait' : m.waiting = [] ∨ capacity ≤ m.items.length := by
      by_cases hw : m.waiting = [] <;> simp_all
    cases hc : m.closed <;> by_cases hr : m.count < capacity <;>
      simp only [Op.apply, offerOrWait, offer, hc, hr, ↓reduceIte, Bool.false_eq_true] <;>
      rcases hwait' with hw | hw <;> refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp_all <;> omega
  | urge x =>
    cases hc : m.closed <;> simp only [Op.apply, urge, hc, ↓reduceIte, Bool.false_eq_true] <;>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp_all
  | take => refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp_all [Op.apply, take]
  | rest wake =>
    cases hr : (m.rest wake).1
    · have : (m.rest wake).2 = m := by
        unfold rest at hr ⊢
        split <;> simp_all
      simp only [Op.apply, this]
      exact ⟨hcount, hbound, hwait, hasleep, hclosed⟩
    · obtain ⟨hc, hi, hu⟩ := rest_eq_true_iff.mp hr
      simp only [Op.apply, rest, hc, hi, hu, List.isEmpty_nil, Bool.not_true, Bool.or_self,
        Bool.false_eq_true, ↓reduceIte]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp_all
  | close => refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp_all [Op.apply, close]

theorem Sound.exec (h : Sound capacity m) (ops : List (Op α W)) :
    Sound capacity (exec capacity ops m).2 := by
  induction ops generalizing m with
  | nil => exact h
  | cons op ops ih => exact ih (h.apply op)

theorem Reachable.sound (h : Reachable capacity m) : Sound capacity m := by
  obtain ⟨ops, rfl⟩ := h
  exact sound_empty.exec ops

end Steps

section Runs

variable {capacity : Nat}

@[simp] theorem exec_nil (m : Mailbox α W) : exec capacity [] m = ([], m) := rfl

theorem urgentIn_cons (op : Op α W) (ops : List (Op α W)) (m : Mailbox α W) :
    urgentIn capacity (op :: ops) m
      = op.urgentIn (op.apply capacity m).1 ++ urgentIn capacity ops (op.apply capacity m).2 :=
  rfl

theorem boundedIn_cons (op : Op α W) (ops : List (Op α W)) (m : Mailbox α W) :
    boundedIn capacity (op :: ops) m
      = op.boundedIn (op.apply capacity m).1 ++ boundedIn capacity ops (op.apply capacity m).2 :=
  rfl

theorem waitedIn_cons (op : Op α W) (ops : List (Op α W)) (m : Mailbox α W) :
    waitedIn capacity (op :: ops) m
      = op.waitedIn (op.apply capacity m).1 ++ waitedIn capacity ops (op.apply capacity m).2 :=
  rfl

private theorem apply_urgent (m : Mailbox α W) {op : Op α W} (h : op ≠ .take) :
    (op.apply capacity m).2.urgent.reverse
      = m.urgent.reverse ++ op.urgentIn (op.apply capacity m).1 := by
  cases op <;> first
    | exact absurd rfl h
    | cases hc : m.closed <;> by_cases hr : m.count < capacity <;>
        simp only [Op.apply, offer, offerOrWait, urge, rest, close, hc, hr, ↓reduceIte,
          Bool.false_eq_true, Bool.true_or, Bool.false_or] <;> (try split) <;> simp_all [Op.urgentIn]

private theorem apply_items (m : Mailbox α W) {op : Op α W} (h : op ≠ .take) :
    (op.apply capacity m).2.items.reverse
      = m.items.reverse ++ op.boundedIn (op.apply capacity m).1 := by
  cases op <;> first
    | exact absurd rfl h
    | cases hc : m.closed <;> by_cases hr : m.count < capacity <;>
        simp only [Op.apply, offer, offerOrWait, urge, rest, close, hc, hr, ↓reduceIte,
          Bool.false_eq_true, Bool.true_or, Bool.false_or] <;> (try split) <;> simp_all [Op.boundedIn]

private theorem apply_waiting (m : Mailbox α W) {op : Op α W} (htake : op ≠ .take)
    (hclose : op ≠ .close) :
    (op.apply capacity m).2.waiting = op.waitedIn (op.apply capacity m).1 ++ m.waiting := by
  cases op <;> first
    | exact absurd rfl htake
    | exact absurd rfl hclose
    | cases hc : m.closed <;> by_cases hr : m.count < capacity <;>
        simp only [Op.apply, offer, offerOrWait, urge, rest, hc, hr, ↓reduceIte,
          Bool.false_eq_true, Bool.true_or, Bool.false_or] <;> (try split) <;> simp_all [Op.waitedIn]

theorem exec_urgent (m : Mailbox α W) {ops : List (Op α W)} (h : ∀ op ∈ ops, op ≠ .take) :
    (exec capacity ops m).2.urgent.reverse = m.urgent.reverse ++ urgentIn capacity ops m := by
  induction ops generalizing m with
  | nil => simp [urgentIn]
  | cons op ops ih =>
    rw [urgentIn_cons, exec, ih _ fun o ho => h o (List.mem_cons_of_mem _ ho),
      apply_urgent m (h op List.mem_cons_self), List.append_assoc]

theorem exec_items (m : Mailbox α W) {ops : List (Op α W)} (h : ∀ op ∈ ops, op ≠ .take) :
    (exec capacity ops m).2.items.reverse = m.items.reverse ++ boundedIn capacity ops m := by
  induction ops generalizing m with
  | nil => simp [boundedIn]
  | cons op ops ih =>
    rw [boundedIn_cons, exec, ih _ fun o ho => h o (List.mem_cons_of_mem _ ho),
      apply_items m (h op List.mem_cons_self), List.append_assoc]

theorem exec_waiting (m : Mailbox α W) {ops : List (Op α W)}
    (h : ∀ op ∈ ops, op ≠ .take ∧ op ≠ .close) :
    (exec capacity ops m).2.waiting = (waitedIn capacity ops m).reverse ++ m.waiting := by
  induction ops generalizing m with
  | nil => simp [waitedIn]
  | cons op ops ih =>
    have hop := h op List.mem_cons_self
    rw [waitedIn_cons, exec, ih _ fun o ho => h o (List.mem_cons_of_mem _ ho),
      apply_waiting m hop.1 hop.2]
    simp [List.reverse_append, Op.waitedIn_reverse]

/-- What a `take` returns is exactly what was taken in since the last `take`: what came from
other shards first, then the rest, each in the order it went in. -/
theorem batch_since_take (m : Mailbox α W) {ops : List (Op α W)} (h : ∀ op ∈ ops, op ≠ .take) :
    (exec capacity ops m.take.2).2.take.1.batch
      = urgentIn capacity ops m.take.2 ++ boundedIn capacity ops m.take.2 := by
  simp only [take] at h ⊢
  rw [exec_urgent _ h, exec_items _ h]
  rfl

/-- A `take` wakes every sender that waited for room since the last `take`, each as often as it
waited. -/
theorem wake_since_take (m : Mailbox α W) {ops : List (Op α W)}
    (h : ∀ op ∈ ops, op ≠ .take ∧ op ≠ .close) :
    (exec capacity ops m.take.2).2.take.1.wake = (waitedIn capacity ops m.take.2).reverse := by
  simp only [take] at h ⊢
  rw [exec_waiting _ h, List.append_nil]

/-- So does a `close`, with the sleeper first. -/
theorem close_since_take (m : Mailbox α W) {ops : List (Op α W)}
    (h : ∀ op ∈ ops, op ≠ .take ∧ op ≠ .close) :
    (exec capacity ops m.take.2).2.close.1
      = (exec capacity ops m.take.2).2.sleeper.toList ++ (waitedIn capacity ops m.take.2).reverse := by
  simp only [close]
  rw [wake_since_take m h |>.symm]
  rfl

private theorem apply_sleeper (m : Mailbox α W) {op : Op α W} (hrest : op.resetsSleeper = false)
    (hquiet : (op.apply capacity m).1.admitted = false) :
    (op.apply capacity m).2.sleeper = m.sleeper := by
  cases op with
  | rest => simp [Op.resetsSleeper] at hrest
  | close => simp [Op.resetsSleeper] at hrest
  | _ =>
    cases hc : m.closed <;> by_cases hr : m.count < capacity <;>
      simp only [Op.apply, offer, offerOrWait, urge, take, hc, hr, ↓reduceIte,
        Bool.false_eq_true] at hquiet ⊢ <;> simp_all [Reply.admitted]

theorem exec_sleeper (m : Mailbox α W) {ops : List (Op α W)} (hrest : ∀ op ∈ ops, op.resetsSleeper = false)
    (hquiet : ∀ r ∈ (exec capacity ops m).1, r.admitted = false) :
    (exec capacity ops m).2.sleeper = m.sleeper := by
  induction ops generalizing m with
  | nil => rfl
  | cons op ops ih =>
    simp only [exec, List.mem_cons, forall_eq_or_imp] at hquiet ⊢
    rw [ih _ (fun o ho => hrest o (List.mem_cons_of_mem _ ho)) hquiet.2,
      apply_sleeper m (hrest op List.mem_cons_self) hquiet.1]

/-- No lost wake-up: once `rest` has answered that the shard sleeps, the next thing taken in,
or a `close`, hands back that sleeper to be woken, and it is not held any longer. Operations
in between that take nothing in leave it asleep. -/
theorem woken_after_rest {m : Mailbox α W} {wake : W} (hrest : (m.rest wake).1 = true)
    {ops : List (Op α W)} (hops : ∀ op ∈ ops, op.resetsSleeper = false)
    (hquiet : ∀ r ∈ (exec capacity ops (m.rest wake).2).1, r.admitted = false) {op : Op α W}
    (hnext : (op.apply capacity (exec capacity ops (m.rest wake).2).2).1.admitted = true
      ∨ op = .close) :
    wake ∈ (op.apply capacity (exec capacity ops (m.rest wake).2).2).1.woken
      ∧ (op.apply capacity (exec capacity ops (m.rest wake).2).2).2.sleeper = none := by
  have hsleeper : (exec capacity ops (m.rest wake).2).2.sleeper = some wake := by
    rw [exec_sleeper _ hops hquiet]
    unfold rest at hrest ⊢
    split <;> simp_all
  obtain ⟨m', hm'⟩ : ∃ m', (exec capacity ops (m.rest wake).2).2 = m' := ⟨_, rfl⟩
  rw [hm'] at hsleeper hnext ⊢
  rcases hnext with h | rfl
  · cases op with
    | take => simp [Op.apply, Reply.admitted] at h
    | rest => simp [Op.apply, Reply.admitted] at h
    | close => simp [Op.apply, Reply.admitted] at h
    | _ =>
      cases hc : m'.closed <;> by_cases hr : m'.count < capacity <;>
        simp only [Op.apply, offer, offerOrWait, urge, hc, hr, hsleeper, ↓reduceIte,
          Bool.false_eq_true] at h ⊢ <;> simp_all [Reply.admitted, Reply.woken]
  · simp [Op.apply, close, hsleeper, Reply.woken]

/-- After `close` nothing is taken in, nobody sleeps or waits, and no reply wakes anyone: those
who slept or waited were all handed back by the `close`. -/
theorem after_close (m : Mailbox α W) (ops : List (Op α W)) :
    (∀ r ∈ (exec capacity ops m.close.2).1, r.admitted = false ∧ r.woken = [])
      ∧ (exec capacity ops m.close.2).2.closed = true
      ∧ (exec capacity ops m.close.2).2.sleeper = none
      ∧ (exec capacity ops m.close.2).2.waiting = [] := by
  suffices ∀ m : Mailbox α W, m.closed = true → m.sleeper = none → m.waiting = [] →
      (∀ r ∈ (exec capacity ops m).1, r.admitted = false ∧ r.woken = [])
        ∧ (exec capacity ops m).2.closed = true ∧ (exec capacity ops m).2.sleeper = none
        ∧ (exec capacity ops m).2.waiting = [] from
    this _ rfl rfl rfl
  induction ops with
  | nil => intro m h1 h2 h3; simp [h1, h2, h3]
  | cons op ops ih =>
    intro m hclosed hsleeper hwaiting
    have hop : (op.apply capacity m).1.admitted = false ∧ (op.apply capacity m).1.woken = []
        ∧ (op.apply capacity m).2.closed = true ∧ (op.apply capacity m).2.sleeper = none
        ∧ (op.apply capacity m).2.waiting = [] := by
      cases op <;>
        simp [Op.apply, offer, offerOrWait, urge, take, rest, close, Reply.admitted, Reply.woken,
          hclosed, hsleeper, hwaiting]
    obtain ⟨h1, h2, h3, h4, h5⟩ := hop
    obtain ⟨hr, hc, hs, hw⟩ := ih _ h3 h4 h5
    simp only [exec, List.mem_cons, forall_eq_or_imp]
    exact ⟨⟨⟨h1, h2⟩, hr⟩, hc, hs, hw⟩

end Runs

section Reachable

variable {capacity : Nat} {m : Mailbox α W}

/-- An offer is refused for want of room exactly when the bounded lane holds `capacity`. -/
theorem Reachable.offer_full_iff (h : Reachable capacity m) {x : α} :
    (m.offer capacity x).1 = .full ↔ m.closed = false ∧ capacity ≤ m.items.length := by
  rw [Mailbox.offer_full_iff, h.sound.count_eq]

theorem Reachable.bounded (h : Reachable capacity m) : m.items.length ≤ capacity :=
  h.sound.bounded

/-- The shard never sleeps on what has arrived. -/
theorem Reachable.asleep_empty (h : Reachable capacity m) (hs : m.sleeper.isSome) :
    m.take.1.batch = [] ∧ m.closed = false := by
  obtain ⟨hi, hu, hc⟩ := h.sound.asleep_empty hs
  simp [take, hi, hu, hc]

/-- With room for one, no sender waits for room while the shard sleeps: it would wait for a
`take` that never comes. -/
theorem Reachable.not_asleep_waiting (h : Reachable capacity m) (hcap : 0 < capacity)
    (hs : m.sleeper.isSome) : m.waiting = [] := by
  have hempty := (h.sound.asleep_empty hs).1
  cases hw : m.waiting with
  | nil => rfl
  | cons room rooms =>
    have := h.sound.waiting_full (by simp [hw])
    simp [hempty] at this
    omega

end Reachable

end Lanes.Mailbox
