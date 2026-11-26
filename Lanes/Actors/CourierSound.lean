/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Actors.Courier
public import Lanes.Data.List

/-!
What the courier does, for every limit and every sequence of events, whatever the handler and
the network report and in whatever order. A run (`Courier.exec`) is the list of what the
courier was told and what it answered, in order (`Entry`), and the theorems are about that
list. They rest on an invariant (`Courier.Sound`) of every courier a run reaches.
-/

@[expose] public section

namespace Lanes.Peers

variable {σ : Signature}

inductive Entry (σ : Signature) where
  | told (event : Event)
  | did (action : Action σ)

def Line.conn? : Line → Option Conn
  | .dialing conn | .up conn _ => some conn
  | _ => none

def Line.until? : Line → Option Nat
  | .resting until_ms => some until_ms
  | _ => none

@[simp] theorem Line.conn?_idle : Line.idle.conn? = none := rfl
@[simp] theorem Line.conn?_dialing (conn : Conn) : (Line.dialing conn).conn? = some conn := rfl
@[simp] theorem Line.conn?_up (conn : Conn) (busy : Bool) : (Line.up conn busy).conn? = some conn :=
  rfl
@[simp] theorem Line.conn?_resting (until_ms : Nat) : (Line.resting until_ms).conn? = none := rfl
@[simp] theorem Line.until?_resting (until_ms : Nat) :
    (Line.resting until_ms).until? = some until_ms := rfl

namespace Courier

variable (limits : Limits) (read : ByteArray → Option (List (Parcel σ) × Nat))

def exec : Courier → List Event → Courier × List (Entry σ)
  | c, [] => (c, [])
  | c, e :: es =>
    ((exec (c.step limits read e).1 es).1,
      .told e :: (c.step limits read e).2.map .did ++ (exec (c.step limits read e).1 es).2)

def Reachable (c : Courier) : Prop :=
  ∃ es, (exec limits read {} es).1 = c

structure Sound (c : Courier) : Prop where
  /-- A connection the courier asked for is the line of the process it leads to, and the line
  of a process is a connection the courier asked for. -/
  wired : ∀ conn to, c.dialed[conn]? = some to ↔ (c.wire to).line.conn? = some conn
  /-- A connection asked for has a name already given. -/
  dialed_lt : ∀ conn, conn ∈ c.dialed → conn < c.nextConn
  /-- A connection adopted has a name already given. -/
  inbound_lt : ∀ conn, conn ∈ c.inbound → conn < c.nextConn
  /-- No connection is both asked for and adopted. -/
  apart : ∀ conn, conn ∈ c.dialed → conn ∉ c.inbound
  /-- The queue for a process holds at most `limits.queue` parcels. -/
  bounded : ∀ to, (c.wire to).waiting.length ≤ limits.queue
  /-- After `stop` the courier holds no connection. -/
  stopped_quiet : c.stopped = true → ∀ conn, conn ∉ c.dialed ∧ conn ∉ c.inbound

variable {limits read}

@[simp] theorem wire_setWire (c : Courier) (to to' : Address) (w : Wire) :
    (c.setWire to w).wire to' = if to = to' then w else c.wire to' := by
  simp [setWire, wire, Std.HashMap.getD_insert]

@[simp] theorem dialed_setWire (c : Courier) (to : Address) (w : Wire) :
    (c.setWire to w).dialed = c.dialed := rfl

@[simp] theorem inbound_setWire (c : Courier) (to : Address) (w : Wire) :
    (c.setWire to w).inbound = c.inbound := rfl

@[simp] theorem nextConn_setWire (c : Courier) (to : Address) (w : Wire) :
    (c.setWire to w).nextConn = c.nextConn := rfl

@[simp] theorem stopped_setWire (c : Courier) (to : Address) (w : Wire) :
    (c.setWire to w).stopped = c.stopped := rfl

@[simp] theorem wire_empty (to : Address) : ({} : Courier).wire to = {} := by
  simp [wire]

@[simp] theorem wire_stopped (n : Conn) (to : Address) :
    ({ stopped := true, nextConn := n } : Courier).wire to = {} := by
  simp [wire]

@[simp] theorem wire_mk (c : Courier) (d : Std.HashMap Conn Address)
    (i : Std.HashMap Conn ByteArray) (n : Conn) (s : Bool) (to : Address) :
    ({ wires := c.wires, dialed := d, inbound := i, nextConn := n, stopped := s } : Courier).wire to
      = c.wire to := rfl

section Helpers

variable (c : Courier) (to to' : Address) (bytes : ByteArray)

@[simp] theorem dial_snd : (dial (σ := σ) limits c to bytes).2 = [.dial c.nextConn to] := rfl

@[simp] theorem dialed_dial :
    (dial (σ := σ) limits c to bytes).1.dialed = c.dialed.insert c.nextConn to := rfl

@[simp] theorem inbound_dial : (dial (σ := σ) limits c to bytes).1.inbound = c.inbound := rfl

@[simp] theorem nextConn_dial : (dial (σ := σ) limits c to bytes).1.nextConn = c.nextConn + 1 :=
  rfl

@[simp] theorem stopped_dial : (dial (σ := σ) limits c to bytes).1.stopped = c.stopped := rfl

@[simp] theorem wire_dial : (dial (σ := σ) limits c to bytes).1.wire to'
    = if to = to' then
        Wire.mk (.dialing c.nextConn) (if limits.queue = 0 then .mk [] [] else (Fifo.mk [] []).push bytes)
      else c.wire to' := by
  simp [Courier.dial]

variable (w : Wire)

@[simp] theorem dialed_enqueue : (enqueue limits c to w bytes).dialed = c.dialed := by
  unfold enqueue; split <;> rfl

@[simp] theorem inbound_enqueue : (enqueue limits c to w bytes).inbound = c.inbound := by
  unfold enqueue; split <;> rfl

@[simp] theorem nextConn_enqueue : (enqueue limits c to w bytes).nextConn = c.nextConn := by
  unfold enqueue; split <;> rfl

@[simp] theorem stopped_enqueue : (enqueue limits c to w bytes).stopped = c.stopped := by
  unfold enqueue; split <;> rfl

@[simp] theorem wire_enqueue : (enqueue limits c to w bytes).wire to'
    = if to = to' ∧ w.waiting.length < limits.queue then { w with waiting := w.waiting.push bytes }
      else c.wire to' := by
  unfold enqueue
  by_cases hq : w.waiting.length < limits.queue <;> simp [hq]

variable (conn : Conn)

@[simp] theorem dialed_next : (next (σ := σ) c to conn w).1.dialed = c.dialed := by
  unfold next; split <;> rfl

@[simp] theorem inbound_next : (next (σ := σ) c to conn w).1.inbound = c.inbound := by
  unfold next; split <;> rfl

@[simp] theorem nextConn_next : (next (σ := σ) c to conn w).1.nextConn = c.nextConn := by
  unfold next; split <;> rfl

@[simp] theorem stopped_next : (next (σ := σ) c to conn w).1.stopped = c.stopped := by
  unfold next; split <;> rfl

theorem next_of_pop {rest : Fifo ByteArray} (h : w.waiting.pop? = some (bytes, rest)) :
    next (σ := σ) c to conn w
      = (c.setWire to { line := .up conn true, waiting := rest }, [.write conn bytes]) := by
  simp [next, h]

theorem next_of_none (h : w.waiting.pop? = none) :
    next (σ := σ) c to conn w = (c.setWire to { w with line := .up conn false }, []) := by
  simp [next, h]

end Helpers

theorem sound_empty : Sound limits {} where
  wired := by simp [Line.conn?]
  dialed_lt := by simp
  inbound_lt := by simp
  apart := by simp
  bounded := by simp [Fifo.length]
  stopped_quiet := by simp

theorem mem_of_getElem? {β : Type} {m : Std.HashMap Conn β} {k : Conn} {v : β}
    (h : m[k]? = some v) : k ∈ m :=
  Std.HashMap.mem_iff_isSome_getElem?.mpr (by simp [h])

theorem Sound.dial {c : Courier} (h : Sound limits c) {to : Address}
    (hl : (c.wire to).line.conn? = none) (hs : c.stopped = false) (bytes : ByteArray) :
    Sound limits (dial (σ := σ) limits c to bytes).1 := by
  obtain ⟨wired, dlt, ilt, apart, bounded, quiet⟩ := h
  refine ⟨fun conn to' => ?_, fun conn hc => ?_, fun conn hc => ?_, fun conn hc => ?_,
    fun to' => ?_, by simp [hs]⟩
  · simp only [dialed_dial, wire_dial, Std.HashMap.getElem?_insert, beq_iff_eq]
    by_cases hn : c.nextConn = conn <;> by_cases ht : to = to' <;> simp only [hn, ht, ↓reduceIte]
    · simp
    · simp only [Option.some.injEq, ht, false_iff]
      intro hc
      have := dlt _ (mem_of_getElem? ((wired _ _).mpr hc))
      unfold Conn at *
      omega
    · simp only [Line.conn?_dialing, Option.some.injEq, hn, iff_false]
      intro hc
      have := (wired _ _).mp hc
      simp_all
    · exact wired _ _
  · simp only [dialed_dial, nextConn_dial, Std.HashMap.mem_insert, beq_iff_eq] at hc ⊢
    unfold Conn at *
    rcases hc with hc | hc
    · omega
    · have := dlt _ hc; omega
  · simp only [inbound_dial, nextConn_dial] at hc ⊢
    have := ilt _ hc
    unfold Conn at *
    omega
  · simp only [dialed_dial, inbound_dial, Std.HashMap.mem_insert, beq_iff_eq] at hc ⊢
    rcases hc with rfl | hc
    · intro hin; have := ilt _ hin; unfold Conn at *; omega
    · exact apart _ hc
  · simp only [wire_dial]
    split
    · split <;> simp [Fifo.length, Fifo.push, *] <;> omega
    · exact bounded _

theorem Sound.setWire {c : Courier} (h : Sound limits c) {to : Address} {w : Wire}
    (hline : w.line.conn? = (c.wire to).line.conn?) (hwait : w.waiting.length ≤ limits.queue) :
    Sound limits (c.setWire to w) := by
  obtain ⟨wired, dlt, ilt, apart, bounded, quiet⟩ := h
  refine ⟨fun conn to' => ?_, dlt, ilt, apart, fun to' => ?_, quiet⟩
  · simp only [dialed_setWire, wire_setWire]
    split
    · next ht => subst ht; rw [hline]; exact wired _ _
    · exact wired _ _
  · simp only [wire_setWire]
    split
    · exact hwait
    · exact bounded _

theorem Sound.enqueue {c : Courier} (h : Sound limits c) (to : Address) (bytes : ByteArray) :
    Sound limits (enqueue limits c to (c.wire to) bytes) := by
  unfold Courier.enqueue
  split
  · next hq =>
    exact h.setWire rfl (by simp [Fifo.length, Fifo.push] at hq ⊢; omega)
  · exact h

theorem Sound.next {c : Courier} (h : Sound limits c) {to : Address} {conn : Conn}
    (hline : (c.wire to).line.conn? = some conn) :
    Sound limits (next (σ := σ) c to conn (c.wire to)).1 := by
  cases hp : (c.wire to).waiting.pop? with
  | none => rw [next_of_none _ _ _ _ hp]; exact h.setWire (by simp [hline]) (h.bounded to)
  | some p =>
    obtain ⟨bytes, rest⟩ := p
    rw [next_of_pop _ _ _ _ _ hp]
    refine h.setWire (by simp [hline]) ?_
    have := Fifo.toList_of_pop? hp
    have hb := h.bounded to
    rw [← Fifo.length_toList, this] at hb
    simp [← Fifo.length_toList] at hb ⊢
    omega

theorem Sound.broken {c : Courier} (h : Sound limits c) {conn : Conn} {to : Address}
    (hto : c.dialed[conn]? = some to) (until_ms : Nat) :
    Sound limits ({ c with dialed := c.dialed.erase conn }.setWire to { line := .resting until_ms }) := by
  obtain ⟨wired, dlt, ilt, apart, bounded, quiet⟩ := h
  have hline := (wired _ _).mp hto
  refine ⟨fun k to' => ?_, fun k hk => ?_, ilt, fun k hk => ?_, fun to' => ?_, fun hs => ?_⟩
  · simp only [dialed_setWire, wire_setWire, wire_mk, Std.HashMap.getElem?_erase, beq_iff_eq]
    by_cases hk : conn = k <;> by_cases ht : to = to' <;> simp only [hk, ht, ↓reduceIte]
    · simp
    · subst hk
      simp only [reduceCtorEq, false_iff]
      intro hc
      exact ht (Option.some.inj ((wired _ _).mpr hc ▸ hto).symm)
    · subst ht
      simp only [Line.conn?_resting, reduceCtorEq, iff_false]
      intro hc
      have := (wired _ _).mp hc
      rw [hline] at this
      exact hk (Option.some.inj this)
    · exact wired _ _
  · simp only [dialed_setWire, nextConn_setWire, Std.HashMap.mem_erase] at hk ⊢
    exact dlt _ hk.2
  · simp only [dialed_setWire, inbound_setWire, Std.HashMap.mem_erase] at hk ⊢
    exact apart _ hk.2
  · simp only [wire_setWire]
    split
    · simp [Fifo.length]
    · exact bounded _
  · simp only [stopped_setWire] at hs
    exact absurd (mem_of_getElem? hto) (quiet hs conn).1

theorem Sound.inbound {c : Courier} (h : Sound limits c) {inbound : Std.HashMap Conn ByteArray}
    (hsub : ∀ k, k ∈ inbound → k ∈ c.inbound) : Sound limits { c with inbound } := by
  obtain ⟨wired, dlt, ilt, apart, bounded, quiet⟩ := h
  exact ⟨wired, dlt, fun k hk => ilt _ (hsub _ hk), fun k hk hin => apart _ hk (hsub _ hin),
    bounded, fun hs k => ⟨(quiet hs k).1, fun hin => (quiet hs k).2 (hsub _ hin)⟩⟩

theorem Sound.accept {c : Courier} (h : Sound limits c) (hs : c.stopped = false) :
    Sound limits { c with nextConn := c.nextConn + 1, inbound := c.inbound.insert c.nextConn .empty } := by
  obtain ⟨wired, dlt, ilt, apart, bounded, quiet⟩ := h
  refine ⟨wired, fun k hk => ?_, fun k hk => ?_, fun k hk hin => ?_, bounded, by simp [hs]⟩
  · have := dlt _ hk; unfold Conn at *; simp only; omega
  · simp only [Std.HashMap.mem_insert, beq_iff_eq] at hk ⊢
    unfold Conn at *
    rcases hk with hk | hk
    · omega
    · have := ilt _ hk; omega
  · simp only [Std.HashMap.mem_insert, beq_iff_eq] at hin
    rcases hin with rfl | hin
    · have := dlt _ hk; unfold Conn at *; omega
    · exact apart _ hk hin

theorem sound_stopped (n : Conn) : Sound limits { stopped := true, nextConn := n } where
  wired := by simp
  dialed_lt := by simp
  inbound_lt := by simp
  apart := by simp
  bounded := by simp [Fifo.length]
  stopped_quiet := by simp

theorem Sound.step {c : Courier} (h : Sound limits c) (e : Event) :
    Sound limits (c.step limits read e).1 := by
  cases e with
  | send to bytes now =>
    simp only [Courier.step]
    split
    · exact h
    · next hs =>
      split
      · next heq => exact h.dial (by simp [heq]) (by simpa using hs) bytes
      · next heq =>
        split
        · exact h.dial (by simp [heq]) (by simpa using hs) bytes
        · exact h
      · exact h.enqueue to bytes
      · next heq => exact h.setWire (by simp [heq]) (h.bounded to)
      · exact h.enqueue to bytes
  | connected conn | written conn =>
    simp only [Courier.step]
    split
    · split
      · next heq => exact h.next (by simp [heq])
      · exact h
    · exact h
  | broken conn now =>
    simp only [Courier.step]
    split
    · next to hto =>
      have hline := (h.wired _ _).mp hto
      split
      · exact h.broken hto _
      · next hnot =>
        exfalso
        apply hnot
        simp only [wire_mk]
        revert hline
        cases (c.wire to).line <;> simp_all
    · split
      · exact h.inbound fun k hk => (Std.HashMap.mem_erase.mp hk).2
      · exact h
  | accepted =>
    simp only [Courier.step]
    split
    · exact h
    · next hs => exact h.accept (by simpa using hs)
  | received conn bytes =>
    simp only [Courier.step]
    split
    · next earlier hearlier =>
      split
      · split
        · exact h.inbound fun k hk => (Std.HashMap.mem_erase.mp hk).2
        · refine h.inbound fun k hk => ?_
          simp only [Std.HashMap.mem_insert, beq_iff_eq] at hk
          rcases hk with rfl | hk
          · exact mem_of_getElem? hearlier
          · exact hk
      · exact h.inbound fun k hk => (Std.HashMap.mem_erase.mp hk).2
    · split <;> exact h
  | stop => exact sound_stopped _

theorem Sound.exec {c : Courier} (h : Sound limits c) (es : List Event) :
    Sound limits (exec (σ := σ) limits read c es).1 := by
  induction es generalizing c with
  | nil => exact h
  | cons e es ih => exact ih (h.step e)

theorem Reachable.sound {c : Courier} (h : Reachable (σ := σ) limits read c) : Sound limits c := by
  obtain ⟨es, rfl⟩ := h
  exact sound_empty.exec es

/-- The queue for a process never holds more than `limits.queue` parcels. -/
theorem Reachable.queue_le {c : Courier} (h : Reachable (σ := σ) limits read c) (to : Address) :
    (c.wire to).waiting.length ≤ limits.queue :=
  h.sound.bounded to

/-- What a run says of one connection: not yet named, asked for (and whether a write is under
way on it), adopted, or closed. -/
inductive Status where
  | fresh
  | dialed (busy : Bool)
  | adopted
  | closed
  deriving DecidableEq

def Status.close : Status → Status
  | .dialed _ | .adopted => .closed
  | s => s

def Status.written : Status → Status
  | .dialed _ => .dialed false
  | s => s

/-- Follow one entry of a run. `none` when the courier answers something that breaks a promise:
a second write before the first was written, a write on a connection it did not ask for or has
closed, or a name it gave before. -/
def Status.next (conn : Conn) (s : Status) : Entry σ → Option Status
  | .told (.written k) => some (if k = conn then s.written else s)
  | .did (.dial k _) => if k = conn then (if s = .fresh then some (.dialed false) else none) else some s
  | .did (.adopt k) => if k = conn then (if s = .fresh then some .adopted else none) else some s
  | .did (.write k _) =>
    if k = conn then (if s = .dialed false then some (.dialed true) else none) else some s
  | .did (.close k) => some (if k = conn then s.close else s)
  | _ => some s

def status (c : Courier) (conn : Conn) : Status :=
  if c.nextConn ≤ conn then .fresh
  else match c.dialed[conn]? with
    | some to => .dialed (decide ((c.wire to).line = .up conn true))
    | none => if conn ∈ c.inbound then .adopted else .closed

section Status

variable {c : Courier}

theorem status_fresh {k : Conn} (hle : c.nextConn ≤ k) : c.status k = .fresh := by
  simp [status, hle]

theorem status_dialed {k : Conn} {to : Address} (hlt : k < c.nextConn)
    (hd : c.dialed[k]? = some to) :
    c.status k = .dialed (decide ((c.wire to).line = .up k true)) := by
  simp [status, Nat.not_le.mpr hlt, hd]

theorem status_adopted {k : Conn} (hlt : k < c.nextConn) (hd : c.dialed[k]? = none)
    (hi : k ∈ c.inbound) : c.status k = .adopted := by
  simp [status, Nat.not_le.mpr hlt, hd, hi]

theorem status_closed {k : Conn} (hlt : k < c.nextConn) (hd : c.dialed[k]? = none)
    (hi : k ∉ c.inbound) : c.status k = .closed := by
  simp [status, Nat.not_le.mpr hlt, hd, hi]

theorem status_of_none {k : Conn} (hd : c.dialed[k]? = none) :
    c.status k = if c.nextConn ≤ k then .fresh else if k ∈ c.inbound then .adopted else .closed := by
  simp [status, hd]

theorem status_congr {c' : Courier} {k : Conn} (hn : c'.nextConn ≤ k ↔ c.nextConn ≤ k)
    (hd : c'.dialed[k]? = c.dialed[k]?)
    (hw : ∀ to, c.dialed[k]? = some to → (c'.wire to).line = (c.wire to).line)
    (hi : k ∈ c'.inbound ↔ k ∈ c.inbound) : c'.status k = c.status k := by
  by_cases hle : c.nextConn ≤ k
  · rw [status_fresh hle, status_fresh (hn.mpr hle)]
  · have hlt := Nat.not_le.mp hle
    have hlt' := Nat.not_le.mp (fun h => hle (hn.mp h))
    cases hdk : c.dialed[k]? with
    | some to =>
      rw [status_dialed hlt hdk, status_dialed hlt' (hd.trans hdk), hw _ hdk]
    | none =>
      by_cases hin : k ∈ c.inbound
      · rw [status_adopted hlt hdk hin, status_adopted hlt' (hd.trans hdk) (hi.mpr hin)]
      · rw [status_closed hlt hdk hin, status_closed hlt' (hd.trans hdk) (fun h => hin (hi.mp h))]

theorem status_setWire (h : Sound limits c) {to : Address} (w : Wire) (k : Conn) :
    (c.setWire to w).status k = if (c.wire to).line.conn? = some k
      then .dialed (decide (w.line = .up k true)) else c.status k := by
  split
  · next hk =>
    have hto := (h.wired _ _).mpr hk
    have := h.dialed_lt _ (mem_of_getElem? hto)
    rw [status_dialed (c := c.setWire to w) (to := to) this (by simpa using hto)]
    simp
  · next hk =>
    refine status_congr Iff.rfl rfl (fun to' hd => ?_) Iff.rfl
    have : to ≠ to' := fun ht => hk (ht ▸ (h.wired _ _).mp hd)
    simp [this]

theorem status_dial (h : Sound limits c) {to : Address} (hl : (c.wire to).line.conn? = none)
    (bytes : ByteArray) (k : Conn) :
    (dial (σ := σ) limits c to bytes).1.status k
      = if k = c.nextConn then .dialed false else c.status k := by
  split
  · next hk =>
    subst hk
    rw [status_dialed (to := to) (by simp) (by simp)]
    simp
  · next hk =>
    refine status_congr ?_ (by simp [Std.HashMap.getElem?_insert, Ne.symm hk]) (fun to' hd => ?_)
      (by simp)
    · simp only [nextConn_dial]
      unfold Conn at *
      omega
    · have : to ≠ to' := fun ht => by
        have := (h.wired _ _).mp hd
        rw [← ht, hl] at this
        exact absurd this (by simp)
      simp [this]

theorem status_broken (h : Sound limits c) {conn : Conn} {to : Address}
    (hto : c.dialed[conn]? = some to) (until_ms : Nat) (k : Conn) :
    ({ c with dialed := c.dialed.erase conn }.setWire to { line := .resting until_ms }).status k
      = if k = conn then .closed else c.status k := by
  have hlt := h.dialed_lt _ (mem_of_getElem? hto)
  have hline := (h.wired _ _).mp hto
  split
  · next hk =>
    subst hk
    exact status_closed hlt (by simp) (by simpa using h.apart _ (mem_of_getElem? hto))
  · next hk =>
    refine status_congr Iff.rfl (by simp [Std.HashMap.getElem?_erase, Ne.symm hk])
      (fun to' hd => ?_) Iff.rfl
    have : to ≠ to' := fun ht => by
      have := (h.wired _ _).mp hd
      rw [← ht, hline] at this
      exact hk (Option.some.inj this).symm
    simp [this]

theorem status_eraseInbound (h : Sound limits c) {conn : Conn} (hin : conn ∈ c.inbound)
    (k : Conn) :
    ({ c with inbound := c.inbound.erase conn } : Courier).status k
      = if k = conn then .closed else c.status k := by
  have hlt := h.inbound_lt _ hin
  have hd : c.dialed[conn]? = none :=
    Std.HashMap.getElem?_eq_none (fun hm => h.apart _ hm hin)
  split
  · next hk =>
    subst hk
    exact status_closed hlt hd (by simp)
  · next hk =>
    exact status_congr Iff.rfl rfl (fun _ _ => rfl) (by simp [Std.HashMap.mem_erase, Ne.symm hk])

theorem status_insertInbound {conn : Conn} (hin : conn ∈ c.inbound) (bytes : ByteArray)
    (k : Conn) : ({ c with inbound := c.inbound.insert conn bytes } : Courier).status k = c.status k :=
  status_congr Iff.rfl rfl (fun _ _ => rfl) (by
    simp only [Std.HashMap.mem_insert, beq_iff_eq]
    constructor
    · rintro (rfl | h) <;> assumption
    · exact Or.inr)

theorem status_accept (h : Sound limits c) (k : Conn) :
    ({ c with nextConn := c.nextConn + 1, inbound := c.inbound.insert c.nextConn .empty } :
        Courier).status k
      = if k = c.nextConn then .adopted else c.status k := by
  split
  · next hk =>
    subst hk
    exact status_adopted (by simp)
      (Std.HashMap.getElem?_eq_none fun hm => by have := h.dialed_lt _ hm; unfold Conn at *; omega)
      (by simp)
  · next hk =>
    refine status_congr ?_ rfl (fun _ _ => rfl) (by simp [Std.HashMap.mem_insert, Ne.symm hk])
    simp only
    unfold Conn at *
    omega

theorem status_stopped (n k : Conn) :
    ({ stopped := true, nextConn := n } : Courier).status k = if n ≤ k then .fresh else .closed := by
  simp [status]

theorem foldlM_closes (conn : Conn) (ks : List Conn) (s : Status) :
    ((ks.map Action.close).map (Entry.did (σ := σ))).foldlM (Status.next conn) s
      = some (if conn ∈ ks then s.close else s) := by
  induction ks generalizing s with
  | nil => simp
  | cons k ks ih =>
    simp only [List.map_cons, List.foldlM_cons, Status.next, Option.bind_eq_bind,
      Option.bind_some, ih, List.mem_cons]
    by_cases hk : k = conn
    · subst hk
      cases s <;> simp [Status.close]
    · simp [hk, Ne.symm hk]

theorem foldlM_delivers (conn : Conn) (ps : List (Parcel σ)) (s : Status) :
    ((ps.map Action.deliver).map (Entry.did (σ := σ))).foldlM (Status.next conn) s = some s := by
  induction ps with
  | nil => simp
  | cons p ps ih => simpa [Status.next] using ih

theorem status_enqueue (h : Sound limits c) (to : Address) (bytes : ByteArray) (k : Conn) :
    (enqueue limits c to (c.wire to) bytes).status k = c.status k := by
  unfold Courier.enqueue
  split
  · rw [status_setWire h]
    split
    · next hk =>
      have hto := (h.wired _ _).mpr hk
      rw [status_dialed (h.dialed_lt _ (mem_of_getElem? hto)) hto]
    · rfl
  · rfl

theorem foldlM_told (conn : Conn) (e : Event) (l : List (Entry σ)) (s : Status) :
    (Entry.told e :: l).foldlM (Status.next conn) s
      = l.foldlM (Status.next conn) (match e with
        | .written k => if k = conn then s.written else s
        | _ => s) := by
  cases e <;> simp [Status.next]

theorem status_next (h : Sound limits c) {to : Address} {conn : Conn}
    (hline : (c.wire to).line.conn? = some conn) (k : Conn) (s : Status)
    (hs : s = if k = conn then .dialed false else c.status k) :
    ((next (σ := σ) c to conn (c.wire to)).2.map Entry.did).foldlM (Status.next k) s
      = some ((next (σ := σ) c to conn (c.wire to)).1.status k) := by
  have hk : (c.wire to).line.conn? = some k ↔ k = conn := by
    rw [hline]; exact ⟨fun e => (Option.some.inj e).symm, fun e => e ▸ rfl⟩
  cases hp : (c.wire to).waiting.pop? with
  | none =>
    rw [next_of_none _ _ _ _ hp, status_setWire h]
    by_cases hc : k = conn
    · subst hc; simp [hs, hline]
    · simp [hs, hc, hk]
  | some p =>
    obtain ⟨bytes, rest⟩ := p
    rw [next_of_pop _ _ _ _ _ hp, status_setWire h]
    by_cases hc : k = conn
    · subst hc; simp [hs, hline, Status.next]
    · simp [hs, hc, hk, Status.next, Ne.symm hc]

theorem status_step (h : Sound limits c) (conn : Conn) (e : Event) :
    (Entry.told e :: (c.step limits read e).2.map Entry.did).foldlM (Status.next conn) (c.status conn)
      = some ((c.step limits read e).1.status conn) := by
  cases e with
  | send to bytes now =>
    rw [foldlM_told]
    simp only [Courier.step]
    split
    · simp
    · next hs =>
      have hs : c.stopped = false := by simpa using hs
      have dialCase (hl : (c.wire to).line.conn? = none) :
          ((dial (σ := σ) limits c to bytes).2.map Entry.did).foldlM (Status.next conn) (c.status conn)
            = some ((dial (σ := σ) limits c to bytes).1.status conn) := by
        rw [status_dial h hl]
        by_cases hc : c.nextConn = conn
        · subst hc; simp [Status.next, status_fresh (Nat.le_refl _)]
        · simp [Status.next, hc, Ne.symm hc]
      split
      · next heq => exact dialCase (by simp [heq])
      · next heq =>
        split
        · exact dialCase (by simp [heq])
        · simp
      · simp [status_enqueue h]
      · next conn' heq =>
        rw [status_setWire h]
        have hd := (h.wired conn' to).mpr (by simp [heq])
        by_cases hc : conn' = conn
        · subst hc
          simp [Status.next, heq, status_dialed (h.dialed_lt _ (mem_of_getElem? hd)) hd]
        · simp [Status.next, heq, hc]
      · simp [status_enqueue h]
  | connected conn' =>
    rw [foldlM_told]
    simp only [Courier.step]
    split
    · next to hto =>
      split
      · next heq =>
        refine status_next h (by simp [heq]) conn _ ?_
        split
        · next hc => subst hc; simp [status_dialed (h.dialed_lt _ (mem_of_getElem? hto)) hto, heq]
        · rfl
      · simp
    · simp
  | written conn' =>
    simp only [Courier.step]
    split
    · next to hto =>
      have hst := status_dialed (h.dialed_lt _ (mem_of_getElem? hto)) hto
      split
      · next heq =>
        rw [foldlM_told]
        refine status_next h (by simp [heq]) conn _ ?_
        by_cases hc : conn' = conn
        · subst hc; simp [hst, heq, Status.written]
        · simp [hc, Ne.symm hc]
      · next hne =>
        rw [foldlM_told]
        simp only [List.map_nil, List.foldlM_nil]
        by_cases hc : conn' = conn
        · subst hc; simp [hst, hne, Status.written]
        · simp [hc]
    · next hd =>
      rw [foldlM_told]
      simp only [List.map_nil, List.foldlM_nil]
      by_cases hc : conn' = conn
      · subst hc
        rw [status_of_none hd]
        simp only [↓reduceIte]
        split <;> (try split) <;> rfl
      · simp [hc]
  | broken conn' now =>
    rw [foldlM_told]
    simp only [Courier.step]
    split
    · next to hto =>
      have hline := (h.wired _ _).mp hto
      have hst := status_dialed (h.dialed_lt _ (mem_of_getElem? hto)) hto
      split
      · rw [status_broken h hto]
        by_cases hc : conn' = conn
        · subst hc; simp [Status.next, hst, Status.close]
        · simp [Status.next, hc, Ne.symm hc]
      · next hnot =>
        exfalso
        apply hnot
        simp only [wire_mk]
        revert hline
        cases (c.wire to).line <;> simp_all
    · next hd =>
      split
      · next hin =>
        have hin : conn' ∈ c.inbound := Std.HashMap.contains_iff_mem.mp hin
        rw [status_eraseInbound h hin]
        by_cases hc : conn' = conn
        · subst hc
          simp [Status.next, Status.close, status_adopted (h.inbound_lt _ hin) hd hin]
        · simp [Status.next, hc, Ne.symm hc]
      · simp
  | accepted =>
    rw [foldlM_told]
    simp only [Courier.step]
    split
    · simp [Status.next]
    · rw [status_accept h]
      by_cases hc : c.nextConn = conn
      · subst hc; simp [Status.next, status_fresh (Nat.le_refl _)]
      · simp [Status.next, hc, Ne.symm hc]
  | received conn' bytes =>
    rw [foldlM_told]
    simp only [Courier.step]
    split
    · next earlier hearlier =>
      have hin := mem_of_getElem? hearlier
      have hd : c.dialed[conn']? = none :=
        Std.HashMap.getElem?_eq_none (fun hm => h.apart _ hm hin)
      split
      · next parcels taken _ =>
        split
        · rw [status_eraseInbound h hin, List.map_append, List.foldlM_append, foldlM_delivers]
          by_cases hc : conn' = conn
          · subst hc
            simp [Status.next, Status.close, status_adopted (h.inbound_lt _ hin) hd hin]
          · simp [Status.next, hc, Ne.symm hc]
        · rw [status_insertInbound hin, foldlM_delivers]
      · rw [status_eraseInbound h hin]
        by_cases hc : conn' = conn
        · subst hc
          simp [Status.next, Status.close, status_adopted (h.inbound_lt _ hin) hd hin]
        · simp [Status.next, hc, Ne.symm hc]
    · next hnone =>
      split
      · simp
      · next hnd =>
        have hd : c.dialed[conn']? = none :=
          Std.HashMap.getElem?_eq_none (fun hm => hnd (Std.HashMap.contains_iff_mem.mpr hm))
        by_cases hc : conn' = conn
        · subst hc
          rw [status_of_none hd]
          have : conn' ∉ c.inbound := fun hm => by
            simp [Std.HashMap.mem_iff_isSome_getElem?, hnone] at hm
          simp only [this, ↓reduceIte]
          split <;> simp [Status.next, Status.close]
        · simp [Status.next, hc]
  | stop =>
    rw [foldlM_told]
    simp only [Courier.step]
    rw [foldlM_closes, status_stopped]
    split
    · next hk =>
      simp only [List.mem_append, Std.HashMap.mem_keys] at hk
      have hlt : conn < c.nextConn := hk.elim (h.dialed_lt _) (h.inbound_lt _)
      simp only [Nat.not_le.mpr hlt, ↓reduceIte]
      cases hd : c.dialed[conn]? with
      | some to => simp [status_dialed hlt hd, Status.close]
      | none =>
        have hin : conn ∈ c.inbound := hk.resolve_left fun hm => by
          simp [Std.HashMap.mem_iff_isSome_getElem?, hd] at hm
        simp [status_adopted hlt hd hin, Status.close]
    · next hk =>
      simp only [List.mem_append, Std.HashMap.mem_keys, not_or] at hk
      have hd : c.dialed[conn]? = none := Std.HashMap.getElem?_eq_none hk.1
      rw [status_of_none hd]
      simp [hk.2]

end Status


section Runs

theorem exec_cons (c : Courier) (e : Event) (es : List Event) :
    (exec limits read c (e :: es)).2
      = (Entry.told e :: (c.step limits read e).2.map Entry.did)
        ++ (exec limits read (c.step limits read e).1 es).2 := rfl

theorem exec_append (c : Courier) (es es' : List Event) :
    exec limits read c (es ++ es')
      = ((exec limits read (exec limits read c es).1 es').1,
        (exec limits read c es).2 ++ (exec limits read (exec limits read c es).1 es').2) := by
  induction es generalizing c with
  | nil => rfl
  | cons e es ih =>
    simp only [List.cons_append, exec, ih, List.append_assoc]

/-- A property of runs that a monitor (`δ`, failing with `none`) checks entry by entry holds of
every run, if each step keeps the monitor in a state that `R` relates to the courier's. -/
theorem exec_foldlM {M : Type} {δ : M → Entry σ → Option M} {R : Courier → M → Prop}
    (hstep : ∀ c m e, Sound limits c → R c m → ∃ m',
      (Entry.told e :: (c.step limits read e).2.map Entry.did).foldlM δ m = some m'
        ∧ R (c.step limits read e).1 m')
    {c : Courier} (hc : Sound limits c) {m : M} (hR : R c m) (es : List Event) :
    ∃ m', (exec limits read c es).2.foldlM δ m = some m' ∧ R (exec limits read c es).1 m' := by
  induction es generalizing c m with
  | nil => exact ⟨m, rfl, hR⟩
  | cons e es ih =>
    obtain ⟨m₁, h₁, hR₁⟩ := hstep c m e hc hR
    obtain ⟨m₂, h₂, hR₂⟩ := ih (hc.step e) hR₁
    refine ⟨m₂, ?_, hR₂⟩
    rw [exec_cons, List.foldlM_append, h₁]
    exact h₂

theorem status_exec {c : Courier} (h : Sound limits c) (conn : Conn) (es : List Event) :
    (exec limits read c es).2.foldlM (Status.next conn) (c.status conn)
      = some ((exec limits read c es).1.status conn) := by
  obtain ⟨m, hm, rfl⟩ := exec_foldlM (R := fun c m => m = c.status conn)
    (fun c m e hc hR => ⟨_, hR ▸ status_step hc conn e, rfl⟩) h rfl es
  exact hm

end Runs

section Monitor

attribute [local simp] Status.written Status.close

theorem Status.next_busy {conn : Conn} {s s' : Status} {x : Entry σ}
    (h : Status.next conn s x = some s') (hx : x ≠ .told (.written conn))
    (hs : s = .dialed true ∨ s = .closed) : s' = .dialed true ∨ s' = .closed := by
  rcases hs with rfl | rfl <;> cases x with
  | told e =>
    cases e <;> simp_all [Status.next] <;> (try split at h) <;> simp_all
  | did a =>
    cases a <;> simp only [Status.next] at h <;> (try split at h) <;> (try split at h) <;>
      simp_all

theorem Status.foldlM_busy {conn : Conn} {s s' : Status} {l : List (Entry σ)}
    (h : l.foldlM (Status.next conn) s = some s') (hl : .told (.written conn) ∉ l)
    (hs : s = .dialed true ∨ s = .closed) : s' = .dialed true ∨ s' = .closed := by
  induction l generalizing s with
  | nil => simp at h; exact h ▸ hs
  | cons x l ih =>
    simp only [List.foldlM_cons] at h
    cases hx : Status.next conn s x with
    | none => simp [hx] at h
    | some s₁ =>
      simp only [hx, Option.bind_eq_bind, Option.bind_some] at h
      exact ih h (fun hm => hl (List.mem_cons_of_mem _ hm))
        (Status.next_busy hx (fun he => hl (he ▸ List.mem_cons_self)) hs)

theorem Status.next_dialed {conn : Conn} {s : Status} {b : Bool} {x : Entry σ}
    (h : Status.next conn s x = some (.dialed b)) :
    (∃ to, x = .did (.dial conn to)) ∨ (x ≠ .did (.close conn) ∧ ∃ b', s = .dialed b') := by
  cases x with
  | told e =>
    right
    refine ⟨by simp, ?_⟩
    cases e <;> simp only [Status.next] at h <;> (try split at h) <;> cases s <;>
      simp_all
  | did a =>
    cases a with
    | dial k to =>
      simp only [Status.next] at h
      split at h
      · next hk => exact Or.inl ⟨to, by rw [hk]⟩
      · exact Or.inr ⟨by simp, _, Option.some.inj h⟩
    | close k =>
      right
      simp only [Status.next, Option.some.injEq] at h
      split at h
      · cases s <;> simp_all
      · exact ⟨by simp_all, _, h⟩
    | _ =>
      right
      simp only [Status.next] at h
      refine ⟨by simp, ?_⟩
      (try split at h) <;> (try split at h) <;> simp_all

theorem Status.foldlM_dialed' {conn : Conn} {b : Bool} {l : List (Entry σ)} {s : Status}
    (h : l.foldlM (Status.next conn) s = some (.dialed b)) :
    (∃ q₁ to q₂, l = q₁ ++ .did (.dial conn to) :: q₂ ∧ .did (.close conn) ∉ q₂)
      ∨ ((∃ b', s = .dialed b') ∧ .did (.close conn) ∉ l) := by
  induction l generalizing s with
  | nil =>
    simp only [List.foldlM_nil] at h
    exact Or.inr ⟨⟨b, Option.some.inj h⟩, by simp⟩
  | cons x l ih =>
    simp only [List.foldlM_cons] at h
    cases hx : Status.next conn s x with
    | none => simp [hx] at h
    | some s₁ =>
      simp only [hx, Option.bind_eq_bind, Option.bind_some] at h
      rcases ih h with ⟨q₁, to, q₂, rfl, hq⟩ | ⟨⟨b', rfl⟩, hl⟩
      · exact Or.inl ⟨x :: q₁, to, q₂, rfl, hq⟩
      · rcases Status.next_dialed hx with ⟨to, rfl⟩ | ⟨hne, hs⟩
        · exact Or.inl ⟨[], to, l, rfl, hl⟩
        · refine Or.inr ⟨hs, ?_⟩
          simp only [List.mem_cons, not_or]
          exact ⟨fun he => hne he.symm, hl⟩

theorem Status.foldlM_dialed {conn : Conn} {b : Bool} {l : List (Entry σ)}
    (h : l.foldlM (Status.next conn) .fresh = some (.dialed b)) :
    ∃ q₁ to q₂, l = q₁ ++ .did (.dial conn to) :: q₂ ∧ .did (.close conn) ∉ q₂ := by
  rcases Status.foldlM_dialed' h with h | ⟨⟨_, h⟩, _⟩
  · exact h
  · cases h

def Status.isOpen : Status → Bool
  | .dialed _ | .adopted => true
  | _ => false

theorem Status.next_open {conn : Conn} {s s' : Status} {x : Entry σ}
    (h : Status.next conn s x = some s') (hx : x ≠ .did (.close conn))
    (hs : s.isOpen = true) : s'.isOpen = true := by
  cases s <;> simp only [Status.isOpen, Bool.false_eq_true] at hs <;> cases x with
  | told e =>
    cases e <;> simp only [Status.next, Option.some.injEq] at h <;> (try split at h) <;>
      subst h <;> simp [Status.isOpen]
  | did a =>
    cases a <;> simp only [Status.next] at h <;> (try split at h) <;> (try split at h) <;>
      simp only [Option.some.injEq, reduceCtorEq] at h <;> (try subst h) <;>
      simp_all [Status.isOpen]

theorem Status.foldlM_open {conn : Conn} {s s' : Status} {l : List (Entry σ)}
    (h : l.foldlM (Status.next conn) s = some s') (hl : .did (.close conn) ∉ l)
    (hs : s.isOpen = true) : s'.isOpen = true := by
  induction l generalizing s with
  | nil => simp at h; exact h ▸ hs
  | cons x l ih =>
    simp only [List.foldlM_cons] at h
    cases hx : Status.next conn s x with
    | none => simp [hx] at h
    | some s₁ =>
      simp only [hx, Option.bind_eq_bind, Option.bind_some] at h
      exact ih h (fun hm => hl (List.mem_cons_of_mem _ hm))
        (Status.next_open hx (fun he => hl (he ▸ List.mem_cons_self)) hs)

end Monitor

section Promises

theorem status_empty (conn : Conn) : ({} : Courier).status conn = .fresh :=
  status_fresh (Nat.zero_le _)

theorem status_run (es : List Event) (conn : Conn) :
    (exec limits read {} es).2.foldlM (Status.next conn) .fresh
      = some ((exec limits read {} es).1.status conn) := by
  rw [← status_empty conn]
  exact status_exec sound_empty conn es

/-- At most one write is under way on a connection: between two writes the courier asks for on
it, the handler has said that the first was written. -/
theorem written_between {es : List Event} {p₁ p₂ p₃ : List (Entry σ)} {conn : Conn}
    {a b : ByteArray}
    (h : (exec limits read {} es).2
      = p₁ ++ .did (.write conn a) :: p₂ ++ .did (.write conn b) :: p₃) :
    .told (.written conn) ∈ p₂ := by
  have hrun := status_run (limits := limits) (read := read) es conn
  rw [h] at hrun
  obtain ⟨m, h₁, h₂⟩ := foldlM_append_some hrun
  obtain ⟨s₁, h₁₁, h₁₂⟩ := foldlM_append_some h₁
  obtain ⟨s₂, h₂₁, h₂₂⟩ := foldlM_cons_some h₁₂
  obtain ⟨s₃, h₃₁, -⟩ := foldlM_cons_some h₂
  have hs₂ : s₂ = .dialed true := by
    simp only [Status.next, ↓reduceIte] at h₂₁
    split at h₂₁ <;> simp_all
  refine Classical.byContradiction fun hn => ?_
  have := Status.foldlM_busy h₂₂ hn (Or.inl hs₂)
  rcases this with rfl | rfl <;> simp [Status.next] at h₃₁

/-- The courier asks for a write only on a connection it asked for and has not closed since. -/
theorem write_dialed {es : List Event} {p₁ p₂ : List (Entry σ)} {conn : Conn} {b : ByteArray}
    (h : (exec limits read {} es).2 = p₁ ++ .did (.write conn b) :: p₂) :
    ∃ q₁ to q₂, p₁ = q₁ ++ .did (.dial conn to) :: q₂ ∧ .did (.close conn) ∉ q₂ := by
  have hrun := status_run (limits := limits) (read := read) es conn
  rw [h] at hrun
  obtain ⟨s, h₁, h₂⟩ := foldlM_append_some hrun
  obtain ⟨s', h₂₁, -⟩ := foldlM_cons_some h₂
  have hs : s = .dialed false := by
    simp only [Status.next, ↓reduceIte] at h₂₁
    split at h₂₁ <;> simp_all
  exact Status.foldlM_dialed (hs ▸ h₁)

/-- The courier never answers `write` on a connection whose line is `.up _ true`, unless what it
was told is that the write under way there was written. -/
theorem Reachable.write_not_busy {c : Courier} (hc : Reachable (σ := σ) limits read c) {e : Event}
    {conn : Conn} {b : ByteArray} (he : e ≠ .written conn)
    (hw : .write conn b ∈ (c.step limits read e).2) (to : Address) :
    (c.wire to).line ≠ .up conn true := by
  intro hline
  have h := hc.sound
  have hd := (h.wired conn to).mpr (by simp [hline])
  have hs : c.status conn = .dialed true := by
    rw [status_dialed (h.dialed_lt _ (mem_of_getElem? hd)) hd, hline]; simp
  have hrun : ∃ t, ((c.step limits read e).2.map Entry.did).foldlM (Status.next conn)
      (.dialed true) = some t := by
    have := status_step (read := read) h conn e
    rw [hs, foldlM_told] at this
    cases e with
    | written k =>
      have hk : k ≠ conn := fun hk => he (hk ▸ rfl)
      simp only [hk, ↓reduceIte] at this
      exact ⟨_, this⟩
    | _ => exact ⟨_, this⟩
  obtain ⟨t, hrun⟩ := hrun
  obtain ⟨acts₁, acts₂, hsplit⟩ := List.append_of_mem hw
  rw [hsplit, List.map_append, List.map_cons] at hrun
  obtain ⟨s, h₁, h₂⟩ := foldlM_append_some hrun
  obtain ⟨s', h₂₁, -⟩ := foldlM_cons_some h₂
  have hnot : .told (.written conn) ∉ acts₁.map (Entry.did (σ := σ)) := by simp
  rcases Status.foldlM_busy h₁ hnot (Or.inl rfl) with rfl | rfl <;> simp [Status.next] at h₂₁

/-- `stop` closes every connection the courier asked for or adopted: one that was not closed
before is closed by the time the courier has answered `stop`. -/
theorem stop_closes {es : List Event} {p₁ p₂ : List (Entry σ)} {x : Entry σ} {conn : Conn}
    (h : (exec limits read {} (es ++ [.stop])).2 = p₁ ++ x :: p₂)
    (hx : (∃ to, x = .did (.dial conn to)) ∨ x = .did (.adopt conn)) :
    .did (.close conn) ∈ p₂ := by
  have hrun := status_run (limits := limits) (read := read) (es ++ [.stop]) conn
  have hfinal : ((exec limits read {} (es ++ [.stop])).1.status conn).isOpen = false := by
    rw [exec_append]
    simp only [exec, Courier.step, status_stopped]
    split <;> rfl
  rw [h] at hrun
  obtain ⟨s, -, h₂⟩ := foldlM_append_some hrun
  obtain ⟨s', h₂₁, h₂₂⟩ := foldlM_cons_some h₂
  have hs' : s'.isOpen = true := by
    rcases hx with ⟨to, rfl⟩ | rfl <;> simp only [Status.next, ↓reduceIte] at h₂₁ <;>
      split at h₂₁ <;> simp only [Option.some.injEq, reduceCtorEq] at h₂₁ <;> subst h₂₁ <;> rfl
  refine Classical.byContradiction fun hn => ?_
  have := Status.foldlM_open h₂₂ hn hs'
  simp_all

/-- Follows whether `stop` has been told; `none` when anything but a close or a refusal is
answered after it. -/
def Stopped.next (stopped : Bool) : Entry σ → Option Bool
  | .told .stop => some true
  | .told _ => some stopped
  | .did (.close _) | .did .refuse => some stopped
  | .did _ => if stopped then none else some false

theorem stopped_step {c : Courier} {e : Event} (he : e ≠ .stop) :
    (c.step limits read e).1.stopped = c.stopped := by
  cases e with
  | stop => exact absurd rfl he
  | send to bytes now =>
    simp only [Courier.step]
    split
    · rfl
    · split
      · rfl
      · split <;> rfl
      all_goals simp
  | connected conn | written conn =>
    simp only [Courier.step]
    split
    · split
      · simp
      · rfl
    · rfl
  | broken conn now =>
    simp only [Courier.step]
    split
    · split <;> rfl
    · split <;> rfl
  | accepted =>
    simp only [Courier.step]
    split <;> rfl
  | received conn bytes =>
    simp only [Courier.step]
    split
    · split
      · split <;> rfl
      · rfl
    · split <;> rfl

theorem Stopped.foldlM_false {l : List (Entry σ)} (hl : .told .stop ∉ l) :
    l.foldlM Stopped.next false = some false := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    have ih := ih (fun hm => hl (List.mem_cons_of_mem _ hm))
    rcases x with e | a
    · cases e <;> simp_all [Stopped.next]
    · cases a <;> simp_all [Stopped.next]

theorem Stopped.foldlM_closes (ks : List Conn) (b : Bool) :
    (ks.map (Entry.did (σ := σ) ∘ Action.close)).foldlM Stopped.next b = some b := by
  induction ks with
  | nil => rfl
  | cons k ks ih => simpa [Stopped.next] using ih

theorem stopped_step_monitor {c : Courier} (h : Sound limits c) (e : Event) :
    (Entry.told e :: (c.step limits read e).2.map Entry.did).foldlM Stopped.next c.stopped
      = some (c.step limits read e).1.stopped := by
  by_cases he : e = .stop
  · subst he
    simp only [Courier.step, List.map_append, List.map_map, List.foldlM_cons, Stopped.next,
      List.foldlM_append, Stopped.foldlM_closes, Option.bind_eq_bind, Option.bind_some]
  · cases hs : c.stopped
    · rw [stopped_step he, hs]
      refine Stopped.foldlM_false ?_
      simp only [List.mem_cons, Entry.told.injEq, List.mem_map]
      rintro (he' | ⟨_, _, he'⟩)
      · exact he he'.symm
      · cases he'
    · rw [stopped_step he, hs]
      have hq := h.stopped_quiet hs
      have hd (conn : Conn) : c.dialed[conn]? = none := Std.HashMap.getElem?_eq_none (hq conn).1
      have hi (conn : Conn) : c.inbound[conn]? = none := Std.HashMap.getElem?_eq_none (hq conn).2
      have hic (conn : Conn) : c.inbound.contains conn = false :=
        Std.HashMap.contains_eq_false_iff_not_mem.mpr (hq conn).2
      have hdc (conn : Conn) : c.dialed.contains conn = false :=
        Std.HashMap.contains_eq_false_iff_not_mem.mpr (hq conn).1
      cases e <;> simp_all [Courier.step, Stopped.next]

/-- After `stop` the courier only closes connections and refuses new ones: nothing more is
dialed, adopted, written or delivered. -/
theorem after_stop {es : List Event} {p₁ p₂ : List (Entry σ)} {a : Action σ}
    (h : (exec limits read {} es).2 = p₁ ++ .told .stop :: p₂) (ha : .did a ∈ p₂) :
    (∃ conn, a = .close conn) ∨ a = .refuse := by
  obtain ⟨m, hm, -⟩ := exec_foldlM (δ := Stopped.next) (R := fun c b => b = c.stopped)
    (fun c m e hc hR => ⟨_, hR ▸ stopped_step_monitor hc e, rfl⟩) (sound_empty (limits := limits))
    (m := false) rfl es
  rw [h] at hm
  obtain ⟨b, -, h₂⟩ := foldlM_append_some hm
  obtain ⟨b', hb', h₃⟩ := foldlM_cons_some h₂
  simp only [Stopped.next, Option.some.injEq] at hb'
  subst hb'
  clear h hm h₂
  induction p₂ with
  | nil => simp at ha
  | cons x l ih =>
    obtain ⟨b'', hx, hl⟩ := foldlM_cons_some h₃
    rcases List.mem_cons.mp ha with rfl | ha
    · cases a <;> simp_all [Stopped.next]
    · have : b'' = true := by
        rcases x with e | a' <;> (first | cases e | cases a') <;> simp_all [Stopped.next]
      exact ih ha (this ▸ hl)

end Promises

section Rest

/-- What a run says of one process: the connection to it the courier holds, until when it is to
be left alone after that connection broke, and when the courier was last told to send to it,
if that was the last thing it was told. -/
structure Watch where
  current : Option Conn := none
  until_ms : Option Nat := none
  sentAt : Option Nat := none

def Watch.ready (w : Watch) : Bool :=
  w.current.isNone && match w.until_ms, w.sentAt with
    | none, _ => true
    | some until_ms, some now_ms => decide (until_ms ≤ now_ms)
    | some _, none => false

def Watch.told (retry_ms : Nat) (to : Address) (w : Watch) : Event → Watch
  | .send to' _ now_ms => { w with sentAt := if to' = to then some now_ms else none }
  | .broken k now_ms => { w with
      until_ms := if w.current = some k then some (max (w.until_ms.getD 0) (now_ms + retry_ms))
        else w.until_ms,
      sentAt := none }
  | _ => { w with sentAt := none }

/-- Follow one entry of a run, for the process at `to`. `none` when the courier dials it while it
holds a connection to it, or before it has been left alone for `retry_ms` after a connection to
it broke. -/
def Watch.next (retry_ms : Nat) (to : Address) (w : Watch) : Entry σ → Option Watch
  | .told e => some (w.told retry_ms to e)
  | .did (.dial k to') =>
    if to' = to then (if w.ready then some { w with current := some k, until_ms := none } else none)
    else some w
  | .did (.close k) => some (if w.current = some k then { w with current := none } else w)
  | .did _ => some w

def Watch.Holds (to : Address) (c : Courier) (w : Watch) : Prop :=
  w.current = (c.wire to).line.conn? ∧ (c.stopped = false → w.until_ms = (c.wire to).line.until?)

theorem Watch.foldlM_quiet {retry_ms : Nat} {to : Address} {w : Watch} {acts : List (Action σ)}
    (h : ∀ a ∈ acts, (∀ k, a ≠ .dial k to) ∧ ∀ k, w.current = some k → a ≠ .close k) :
    (acts.map Entry.did).foldlM (Watch.next retry_ms to) w = some w := by
  induction acts with
  | nil => rfl
  | cons a acts ih =>
    have ih := ih fun a ha => h a (List.mem_cons_of_mem _ ha)
    obtain ⟨hd, hc⟩ := h a List.mem_cons_self
    simp only [List.map_cons, List.foldlM_cons]
    cases a with
    | dial k to' =>
      have : to' ≠ to := fun e => hd k (e ▸ rfl)
      simpa [Watch.next, this] using ih
    | close k =>
      have : w.current ≠ some k := fun e => hc k e rfl
      simpa [Watch.next, this] using ih
    | _ => simpa [Watch.next] using ih

theorem Watch.foldlM_closes {retry_ms : Nat} {to : Address} (ks : List Conn) (w : Watch) :
    (ks.map (Entry.did (σ := σ) ∘ Action.close)).foldlM (Watch.next retry_ms to) w
      = some (match w.current with
        | some k => if k ∈ ks then { w with current := none } else w
        | none => w) := by
  induction ks generalizing w with
  | nil => cases h : w.current <;> simp
  | cons k ks ih =>
    simp only [List.map_cons, Function.comp, List.foldlM_cons, Watch.next, Option.bind_eq_bind,
      Option.bind_some]
    by_cases hk : w.current = some k
    · simp only [hk, ↓reduceIte]
      rw [show (Function.comp Entry.did Action.close : Conn → Entry σ) = _ from rfl] at ih
      simp [ih]
    · simp only [hk, ↓reduceIte]
      rw [ih]
      cases hc : w.current with
      | none => rfl
      | some k' =>
        have : k' ≠ k := fun e => hk (e ▸ hc)
        simp [this]

end Rest

section RestStep

variable {c : Courier}

theorem Watch.not_current (h : Sound limits c) {to : Address} {w : Watch} (hw : Watch.Holds to c w)
    {conn : Conn} (hd : c.dialed[conn]? ≠ some to) : w.current ≠ some conn := fun he =>
  hd ((h.wired _ _).mpr (hw.1 ▸ he))

theorem Watch.quiet_of_not_dialed (h : Sound limits c) {to : Address} {w : Watch}
    (hw : Watch.Holds to c w) {acts : List (Action σ)}
    (hacts : ∀ a ∈ acts, (∀ k to', a ≠ .dial k to') ∧ ∀ k, a = .close k → c.dialed[k]? = none) :
    (acts.map Entry.did).foldlM (Watch.next limits.retry_ms to) w = some w :=
  Watch.foldlM_quiet fun a ha => ⟨fun k => (hacts a ha).1 k to, fun k hk he =>
    Watch.not_current h hw (conn := k) (by rw [(hacts a ha).2 k he]; simp) hk⟩

theorem Watch.told_of_ne {r : Nat} {to : Address} {w : Watch} {e : Event}
    (he : ∀ k now_ms, e ≠ .broken k now_ms) :
    (w.told r to e).current = w.current ∧ (w.told r to e).until_ms = w.until_ms := by
  cases e with
  | broken k now_ms => exact absurd rfl (he k now_ms)
  | _ => exact ⟨rfl, rfl⟩

theorem watch_step (h : Sound limits c) {to : Address} {w : Watch} (hw : Watch.Holds to c w)
    (e : Event) :
    ∃ w', (Entry.told e :: (c.step limits read e).2.map Entry.did).foldlM
        (Watch.next limits.retry_ms to) w = some w'
      ∧ Watch.Holds to (c.step limits read e).1 w' := by
  have htold : ∀ l : List (Entry σ), (Entry.told e :: l).foldlM (Watch.next limits.retry_ms to) w
      = l.foldlM (Watch.next limits.retry_ms to) (w.told limits.retry_ms to e) := fun _ => rfl
  simp only [htold]
  by_cases hbroken : ∃ k now_ms, e = .broken k now_ms
  · obtain ⟨conn, now, rfl⟩ := hbroken
    simp only [Courier.step]
    split
    · next to'' hto =>
      have hline := (h.wired _ _).mp hto
      have hs : c.stopped = false := by
        cases hs : c.stopped
        · rfl
        · exact absurd (mem_of_getElem? hto) (h.stopped_quiet hs conn).1
      have hcond : (c.wire to'').line = .dialing conn ∨ (c.wire to'').line = .up conn true
          ∨ (c.wire to'').line = .up conn false := by
        revert hline; cases (c.wire to'').line with
        | up k b => cases b <;> simp_all
        | _ => simp_all
      simp only [wire_mk, hcond, ↓reduceIte]
      by_cases ht : to'' = to
      · subst ht
        have hcur : w.current = some conn := hw.1.trans hline
        have hun : w.until_ms = none := by
          rw [hw.2 hs]; rcases hcond with h' | h' | h' <;> simp [h', Line.until?]
        refine ⟨{ w.told limits.retry_ms to'' (.broken conn now) with current := none },
          by simp [Watch.next, Watch.told, hcur], ⟨by simp, fun _ => ?_⟩⟩
        simp [Watch.told, hcur, hun]
      · have hcur : w.current ≠ some conn := Watch.not_current h hw (by rw [hto]; simpa using ht)
        refine ⟨w.told limits.retry_ms to (.broken conn now), by simp [Watch.next, Watch.told, hcur],
          ⟨?_, fun hs' => ?_⟩⟩
        · simpa [Watch.told, ht] using hw.1
        · simpa [Watch.told, ht, hcur] using hw.2 hs'
    · next hd =>
      have hcur : w.current ≠ some conn := Watch.not_current h hw (by rw [hd]; simp)
      have hw' : Watch.Holds to c (w.told limits.retry_ms to (.broken conn now)) := by
        refine ⟨?_, fun hs' => ?_⟩
        · simpa [Watch.told] using hw.1
        · simpa [Watch.told, hcur] using hw.2 hs'
      split
      · exact ⟨w.told limits.retry_ms to (.broken conn now), by simp [Watch.next, Watch.told, hcur], hw'⟩
      · exact ⟨_, rfl, hw'⟩
  have hne : ∀ k now_ms, e ≠ .broken k now_ms := fun k now_ms he => hbroken ⟨k, now_ms, he⟩
  obtain ⟨hcur₁, hun₁⟩ := Watch.told_of_ne (r := limits.retry_ms) (to := to) (w := w) hne
  have hw₁ : Watch.Holds to c (w.told limits.retry_ms to e) := ⟨hcur₁ ▸ hw.1, hun₁ ▸ hw.2⟩
  have hsent : ∀ to' bytes now, e = .send to' bytes now →
      (w.told limits.retry_ms to e).sentAt = if to' = to then some now else none := by
    rintro _ _ _ rfl; rfl
  generalize w.told limits.retry_ms to e = w₁ at hw₁ hsent ⊢
  have quiet {c' : Courier} {acts : List (Action σ)}
      (hacts : ∀ a ∈ acts, (∀ k to', a ≠ .dial k to') ∧ ∀ k, a = .close k → c.dialed[k]? = none)
      (hc' : (c'.wire to).line = (c.wire to).line) (hs' : c'.stopped = c.stopped) :
      ∃ w', (acts.map Entry.did).foldlM (Watch.next limits.retry_ms to) w₁ = some w'
        ∧ Watch.Holds to c' w' :=
    ⟨w₁, Watch.quiet_of_not_dialed h hw₁ hacts, ⟨by rw [hc']; exact hw₁.1,
      fun hs'' => by rw [hc']; exact hw₁.2 (hs' ▸ hs'')⟩⟩
  have none_acts : ∀ a ∈ ([] : List (Action σ)), (∀ k to', a ≠ .dial k to')
      ∧ ∀ k, a = .close k → c.dialed[k]? = none := by simp
  cases e with
  | broken k now_ms => exact absurd rfl (hne k now_ms)
  | send to' bytes now =>
    have hsent := hsent to' bytes now rfl
    simp only [Courier.step]
    split
    · exact quiet none_acts rfl rfl
    · next hs =>
      have hs : c.stopped = false := by simpa using hs
      have enqueueLine : (enqueue limits c to' (c.wire to') bytes |>.wire to).line = (c.wire to).line := by
        rw [wire_enqueue]
        split
        · next hcond => obtain ⟨rfl, -⟩ := hcond; rfl
        · rfl
      have dialCase (hl : (c.wire to').line.conn? = none)
          (hready : to' = to → (c.wire to').line.until? = none
            ∨ ∃ u, (c.wire to').line.until? = some u ∧ u ≤ now) :
          ∃ w', ((dial (σ := σ) limits c to' bytes).2.map Entry.did).foldlM
              (Watch.next limits.retry_ms to) w₁ = some w'
            ∧ Watch.Holds to (dial (σ := σ) limits c to' bytes).1 w' := by
        by_cases ht : to' = to
        · subst ht
          have hcur : w₁.current = none := hw₁.1.trans hl
          have hun := hw₁.2 hs
          have hrd : w₁.ready = true := by
            simp only [Watch.ready, hcur, Option.isNone_none, Bool.true_and, hun, hsent,
              ↓reduceIte]
            rcases hready rfl with hu | ⟨u, hu, hle⟩
            · simp [hu]
            · simp [hu, hle]
          refine ⟨{ w₁ with current := some c.nextConn, until_ms := none },
            by simp [Watch.next, hrd], ⟨by simp, fun _ => by simp [Line.until?]⟩⟩
        · refine ⟨w₁, by simp [Watch.next, ht], ?_⟩
          exact ⟨by simpa [ht] using hw₁.1, fun hs' => by simpa [ht] using hw₁.2 hs'⟩
      split
      · next heq => exact dialCase (by simp [heq]) (fun _ => Or.inl (by simp [heq, Line.until?]))
      · next until_ms heq =>
        split
        · next hle => exact dialCase (by simp [heq]) (fun _ => Or.inr ⟨until_ms, by simp [heq], hle⟩)
        · exact quiet none_acts rfl rfl
      · exact quiet none_acts enqueueLine (by simp)
      · next conn heq =>
        refine ⟨w₁, by simp [Watch.next], ⟨?_, fun hs' => ?_⟩⟩
        · rw [wire_setWire]
          split
          · next ht => subst ht; rw [hw₁.1, heq]; rfl
          · exact hw₁.1
        · rw [wire_setWire]
          split
          · next ht => subst ht; rw [hw₁.2 hs', heq]; rfl
          · exact hw₁.2 hs'
      · exact quiet none_acts enqueueLine (by simp)
  | stop =>
    simp only [Courier.step, List.map_append, List.map_map, List.foldlM_append,
      Watch.foldlM_closes, Option.bind_eq_bind, Option.bind_some]
    refine ⟨_, rfl, ⟨?_, fun hs => by simp at hs⟩⟩
    simp only [wire_stopped]
    cases hcur : w₁.current with
    | none => simp [hcur]
    | some k =>
      have hk : k ∈ c.dialed.keys := Std.HashMap.mem_keys.mpr
        (mem_of_getElem? ((h.wired _ _).mpr (hw₁.1 ▸ hcur)))
      simp [hk]
  | connected conn' | written conn' =>
    have viaNext {to'' : Address} (hl : (c.wire to'').line.conn? = some conn') :
        ∃ w', ((next (σ := σ) c to'' conn' (c.wire to'')).2.map Entry.did).foldlM
            (Watch.next limits.retry_ms to) w₁ = some w'
          ∧ Watch.Holds to (next (σ := σ) c to'' conn' (c.wire to'')).1 w' := by
      have hu : (c.wire to'').line.until? = none := by
        revert hl; cases (c.wire to'').line <;> simp [Line.until?]
      have holds {wire : Wire} (hwl : wire.line.conn? = some conn') (hwu : wire.line.until? = none) :
          Watch.Holds to (c.setWire to'' wire) w₁ := by
        refine ⟨?_, fun hs' => ?_⟩
        · rw [wire_setWire]
          split
          · next ht => subst ht; rw [hw₁.1, hl, hwl]
          · exact hw₁.1
        · rw [wire_setWire]
          split
          · next ht => subst ht; rw [hw₁.2 hs', hu, hwu]
          · exact hw₁.2 hs'
      cases hp : (c.wire to'').waiting.pop? with
      | none =>
        rw [next_of_none _ _ _ _ hp]
        exact ⟨w₁, rfl, holds (by simp) (by simp [Line.until?])⟩
      | some p =>
        obtain ⟨bytes', rest⟩ := p
        rw [next_of_pop _ _ _ _ _ hp]
        exact ⟨w₁, by simp [Watch.next], holds (by simp) (by simp [Line.until?])⟩
    simp only [Courier.step]
    split
    · split
      · next heq => exact viaNext (by simp [heq])
      · exact quiet none_acts rfl rfl
    · exact quiet none_acts rfl rfl
  | accepted =>
    simp only [Courier.step]
    split
    · exact quiet (by simp) rfl rfl
    · exact quiet (by simp) (by simp) rfl
  | received conn' bytes =>
    simp only [Courier.step]
    split
    · next earlier hearlier =>
      have hd : c.dialed[conn']? = none :=
        Std.HashMap.getElem?_eq_none (fun hm => h.apart _ hm (mem_of_getElem? hearlier))
      have hacts {ps : List (Parcel σ)} {extra : List (Action σ)}
          (he : ∀ a ∈ extra, a = .close conn') :
          ∀ a ∈ ps.map Action.deliver ++ extra, (∀ k to', a ≠ .dial k to')
            ∧ ∀ k, a = .close k → c.dialed[k]? = none := by
        intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · obtain ⟨p, -, rfl⟩ := List.mem_map.mp ha
          exact ⟨by simp, by simp⟩
        · cases he a ha
          exact ⟨by simp, fun k hk => by cases hk; exact hd⟩
      split
      · split
        · exact quiet (hacts (by simp)) (by simp) rfl
        · exact quiet (by simp) (by simp) rfl
      · exact quiet (by simpa using hacts (ps := []) (extra := [.close conn']) (by simp)) (by simp) rfl
    · split
      · exact quiet none_acts rfl rfl
      · next hnd =>
        have hnm : conn' ∉ c.dialed := fun hm => hnd (Std.HashMap.contains_iff_mem.mpr hm)
        exact quiet (by simp [hnm]) rfl rfl

theorem watch_run (es : List Event) (to : Address) :
    ∃ w', (exec limits read {} es).2.foldlM (Watch.next limits.retry_ms to) {} = some w' :=
  (exec_foldlM (R := Watch.Holds to) (fun _ _ e hc hR => watch_step hc hR e)
    (sound_empty (limits := limits)) (m := {}) ⟨by simp, fun _ => by simp [Line.until?]⟩ es).imp
    fun _ h => h.1

theorem Watch.told_current {r : Nat} {to : Address} (w : Watch) (e : Event) :
    (w.told r to e).current = w.current := by
  cases e <;> rfl

/-- A process whose connection broke at `broke_ms` is not dialed again before `retry_ms` has
passed in the courier's clock: the first dial after the break answers a `send` told at
`broke_ms + retry_ms` or later. The connection is one the courier dialed and had not closed
when the break was reported; a break reported again later, or a connection already given up,
is not a new break. -/
theorem rest_after_break {es : List Event} {q₁ q₂ p₂ p₃ : List (Entry σ)} {conn k : Conn}
    {to : Address} {broke_ms now_ms : Nat} {bytes : ByteArray}
    (h : (exec limits read {} es).2 = q₁ ++ .did (.dial conn to) :: q₂
      ++ .told (.broken conn broke_ms) :: p₂ ++ .told (.send to bytes now_ms) :: .did (.dial k to) :: p₃)
    (hopen : .did (.close conn) ∉ q₂) (hfirst : ∀ k', .did (.dial k' to) ∉ p₂) :
    broke_ms + limits.retry_ms ≤ now_ms := by
  obtain ⟨w, hw⟩ := watch_run (limits := limits) (read := read) es to
  rw [h] at hw
  obtain ⟨w₃, hw₃, hlast⟩ := foldlM_append_some hw
  obtain ⟨w₂, hw₂, hp₂⟩ := foldlM_append_some hw₃
  obtain ⟨w₁, hq, hq₂⟩ := foldlM_append_some hw₂
  obtain ⟨wa, hdial, hq₂'⟩ := foldlM_cons_some hq₂
  have hwa : wa.current = some conn := by
    simp only [Watch.next, ↓reduceIte] at hdial
    split at hdial
    · cases hdial; rfl
    · cases hdial
  have hopen' : ∀ w, w.current = some conn → ∀ x ∈ q₂, ∀ w',
      Watch.next limits.retry_ms to w x = some w' → w'.current = some conn := by
    intro w hcur x hx w' hnext
    rcases x with e | a
    · cases hnext; rw [Watch.told_current]; exact hcur
    · cases a with
      | dial k' to' =>
        simp only [Watch.next] at hnext
        split at hnext
        · simp [Watch.ready, hcur] at hnext
        · cases hnext; exact hcur
      | close k' =>
        simp only [Watch.next, Option.some.injEq] at hnext
        split at hnext
        · next hk =>
          rw [hcur] at hk
          cases Option.some.inj hk
          exact absurd hx hopen
        · cases hnext; exact hcur
      | _ => cases hnext; exact hcur
  have hb := foldlM_some_inv (fun w => w.current = some conn)
    (fun w x w' hx hcur hnext => hopen' w hcur x hx w' hnext) hwa hq₂'
  obtain ⟨wc, hbroke, hp₂'⟩ := foldlM_cons_some hp₂
  have hwc : ∃ u, wc.until_ms = some u ∧ broke_ms + limits.retry_ms ≤ u := by
    cases hbroke
    exact ⟨max (w₂.until_ms.getD 0) (broke_ms + limits.retry_ms), by simp [Watch.told, hb],
      Nat.le_max_right _ _⟩
  have hrest := foldlM_some_inv (fun w => ∃ u, w.until_ms = some u ∧ broke_ms + limits.retry_ms ≤ u)
    (fun w x w' hx ⟨u, hu, hle⟩ hnext => by
      rcases x with e | a
      · cases hnext
        cases e with
        | broken k' t =>
          simp only [Watch.told]
          split
          · exact ⟨_, rfl, by rw [hu]; exact Nat.le_trans hle (Nat.le_max_left _ _)⟩
          · exact ⟨u, hu, hle⟩
        | _ => exact ⟨u, hu, hle⟩
      · cases a with
        | dial k' to' =>
          simp only [Watch.next] at hnext
          split at hnext
          · next ht => subst ht; exact absurd hx (hfirst k')
          · cases hnext; exact ⟨u, hu, hle⟩
        | close k' =>
          simp only [Watch.next, Option.some.injEq] at hnext
          split at hnext <;> (cases hnext; exact ⟨u, hu, hle⟩)
        | _ => cases hnext; exact ⟨u, hu, hle⟩) hwc hp₂'
  obtain ⟨u, hu, hle⟩ := hrest
  obtain ⟨wd, hsend, hlast'⟩ := foldlM_cons_some hlast
  obtain ⟨we, hdial', -⟩ := foldlM_cons_some hlast'
  cases hsend
  simp only [Watch.next, ↓reduceIte] at hdial'
  split at hdial'
  · next hready =>
    simp only [Watch.ready, Watch.told, hu, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hready
    exact Nat.le_trans hle hready.2
  · cases hdial'

end RestStep

section Order

/-- The bytes the courier was told to send to `to`, in order. -/
def sentTo (to : Address) : List (Entry σ) → List ByteArray
  | [] => []
  | .told (.send to' bytes _) :: log => if to' = to then bytes :: sentTo to log else sentTo to log
  | _ :: log => sentTo to log

/-- The bytes the courier asked to be written on connections it dialed to `to`, in order;
`conns` are those dialed before. -/
def writtenTo (to : Address) (conns : List Conn) : List (Entry σ) → List ByteArray
  | [] => []
  | .did (.dial k to') :: log => writtenTo to (if to' = to then k :: conns else conns) log
  | .did (.write k bytes) :: log =>
    if k ∈ conns then bytes :: writtenTo to conns log else writtenTo to conns log
  | _ :: log => writtenTo to conns log

/-- What a run says of the parcels for one process: the connections dialed to it, and what was
sent to it and is not yet written, oldest first (with what was dropped among it). -/
structure Order where
  conns : List Conn := []
  pending : List ByteArray := []

def Order.told (to : Address) (o : Order) : Event → Order
  | .send to' bytes _ => if to' = to then { o with pending := o.pending ++ [bytes] } else o
  | _ => o

/-- `none` when a write to `to` is not of a parcel sent to it and not yet written. -/
def Order.next (to : Address) (o : Order) : Entry σ → Option Order
  | .told e => some (o.told to e)
  | .did (.dial k to') => some (if to' = to then { o with conns := k :: o.conns } else o)
  | .did (.write k bytes) =>
    if k ∈ o.conns then (afterFirst bytes o.pending).map fun rest => { o with pending := rest }
    else some o
  | _ => some o

theorem Order.foldlM_sublist {to : Address} {log : List (Entry σ)} {o o' : Order}
    (h : log.foldlM (Order.next to) o = some o') :
    (writtenTo to o.conns log).Sublist (o.pending ++ sentTo to log) := by
  induction log generalizing o with
  | nil => simp [writtenTo]
  | cons x log ih =>
    obtain ⟨o₁, hx, hlog⟩ := foldlM_cons_some h
    have ih := ih hlog
    rcases x with e | a
    · cases e with
      | send to' bytes now =>
        simp only [Order.next, Order.told, Option.some.injEq] at hx
        subst hx
        simp only [writtenTo, sentTo]
        split
        · next ht => simpa [ht] using ih
        · next ht => simpa [ht] using ih
      | _ =>
        simp only [Order.next, Order.told, Option.some.injEq] at hx
        subst hx
        simpa [writtenTo, sentTo] using ih
    · cases a with
      | dial k to' =>
        simp only [Order.next, Option.some.injEq] at hx
        subst hx
        simp only [writtenTo, sentTo]
        split
        · next ht => simpa [ht] using ih
        · next ht => simpa [ht] using ih
      | write k bytes =>
        simp only [Order.next] at hx
        simp only [writtenTo, sentTo]
        split
        · next hk =>
          simp only [hk, ↓reduceIte] at hx
          cases hr : afterFirst bytes o.pending with
          | none => simp [hr] at hx
          | some rest =>
            simp only [hr, Option.map_some, Option.some.injEq] at hx
            subst hx
            obtain ⟨skipped, hp⟩ := eq_of_afterFirst hr
            rw [hp, List.append_assoc, List.cons_append]
            exact (List.Sublist.cons_cons _ ih).trans (List.sublist_append_right _ _)
        · next hk =>
          simp only [hk, ↓reduceIte, Option.some.injEq] at hx
          subst hx
          exact ih
      | _ =>
        simp only [Order.next, Option.some.injEq] at hx
        subst hx
        simpa [writtenTo, sentTo] using ih

def Order.Holds (to : Address) (c : Courier) (o : Order) : Prop :=
  (∀ k, c.dialed[k]? = some to → k ∈ o.conns)
    ∧ (∀ k ∈ o.conns, k < c.nextConn ∧ (c.dialed[k]? = none ∨ c.dialed[k]? = some to))
    ∧ (c.wire to).waiting.toList.Sublist o.pending
    ∧ (∀ k, (c.wire to).line = .up k false → (c.wire to).waiting.toList = [])

end Order

section OrderStep

variable {c : Courier}

theorem Order.foldlM_quiet {to : Address} {o : Order} {acts : List (Action σ)}
    (h : ∀ a ∈ acts, (∀ k to', a ≠ .dial k to') ∧ ∀ k bytes, a ≠ .write k bytes) :
    (acts.map Entry.did).foldlM (Order.next to) o = some o := by
  induction acts with
  | nil => rfl
  | cons a acts ih =>
    have ih := ih fun a ha => h a (List.mem_cons_of_mem _ ha)
    obtain ⟨hd, hw⟩ := h a List.mem_cons_self
    cases a with
    | dial k to' => exact absurd rfl (hd k to')
    | write k bytes => exact absurd rfl (hw k bytes)
    | _ => simpa [Order.next] using ih

theorem Order.holds_frame {c' : Courier} {to : Address} {o : Order} (ho : Order.Holds to c o)
    (hd : c'.dialed = c.dialed) (hw : c'.wire to = c.wire to) (hn : c.nextConn ≤ c'.nextConn) :
    Order.Holds to c' o := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := ho
  refine ⟨fun k hk => h₁ k (hd ▸ hk), fun k hk => ?_, hw ▸ h₃, hw ▸ h₄⟩
  obtain ⟨hlt, hk⟩ := h₂ k hk
  exact ⟨Nat.lt_of_lt_of_le hlt hn, hd ▸ hk⟩

theorem Order.holds_told {to : Address} {o : Order} (ho : Order.Holds to c o) (e : Event) :
    Order.Holds to c (o.told to e) := by
  cases e with
  | send to' bytes now =>
    simp only [Order.told]
    split
    · exact ⟨ho.1, ho.2.1, ho.2.2.1.trans (List.sublist_append_left _ _), ho.2.2.2⟩
    · exact ho
  | _ => exact ho

theorem Order.not_mem {to to' : Address} {o : Order} (ho : Order.Holds to c o)
    {k : Conn} (hk : c.dialed[k]? = some to') (ht : to' ≠ to) : k ∉ o.conns := fun hm => by
  rcases (ho.2.1 k hm).2 with hn | hs
  · rw [hk] at hn; cases hn
  · rw [hk] at hs; exact ht (Option.some.inj hs)

theorem order_step (h : Sound limits c) {to : Address} {o : Order} (ho : Order.Holds to c o)
    (e : Event) :
    ∃ o', (Entry.told e :: (c.step limits read e).2.map Entry.did).foldlM (Order.next to) o
        = some o'
      ∧ Order.Holds to (c.step limits read e).1 o' := by
  have htold : ∀ l : List (Entry σ), (Entry.told e :: l).foldlM (Order.next to) o
      = l.foldlM (Order.next to) (o.told to e) := fun _ => rfl
  simp only [htold]
  have ho₁ := Order.holds_told ho e
  have hpend : ∀ to' bytes now, e = .send to' bytes now → to' = to →
      (o.told to e).pending = o.pending ++ [bytes] := by
    rintro _ _ _ rfl ht; simp [Order.told, ht]
  have hconns : (o.told to e).conns = o.conns := by cases e <;> simp only [Order.told] <;> split <;> rfl
  generalize o.told to e = o₁ at ho₁ hpend hconns
  have frame {c' : Courier} {acts : List (Action σ)}
      (hacts : ∀ a ∈ acts, (∀ k to', a ≠ .dial k to') ∧ ∀ k bytes, a ≠ .write k bytes)
      (hd : c'.dialed = c.dialed) (hw : c'.wire to = c.wire to) (hn : c.nextConn ≤ c'.nextConn) :
      ∃ o', (acts.map Entry.did).foldlM (Order.next to) o₁ = some o' ∧ Order.Holds to c' o' :=
    ⟨o₁, Order.foldlM_quiet hacts, Order.holds_frame ho₁ hd hw hn⟩
  have hnone : ∀ a ∈ ([] : List (Action σ)), (∀ k to', a ≠ .dial k to')
      ∧ ∀ k bytes, a ≠ .write k bytes := by simp
  have writeTo {conn : Conn} {bytes : ByteArray} {rest : Fifo ByteArray} {line : Line}
      (hd : c.dialed[conn]? = some to) (hrest : (bytes :: rest.toList).Sublist o₁.pending)
      (hline : ∀ k, line ≠ .up k false) :
      ∃ o', ([Entry.did (Action.write conn bytes)] : List (Entry σ)).foldlM (Order.next to) o₁
          = some o'
        ∧ Order.Holds to (c.setWire to { line, waiting := rest }) o' := by
    obtain ⟨r, hr, hsub⟩ := afterFirst_of_cons_sublist hrest
    have hm : conn ∈ o₁.conns := ho₁.1 conn hd
    refine ⟨{ o₁ with pending := r }, by simp [Order.next, hm, hr], ?_⟩
    refine ⟨ho₁.1, ho₁.2.1, by simpa using hsub, fun k hk => ?_⟩
    simp only [wire_setWire, ↓reduceIte] at hk
    exact absurd hk (hline k)
  cases e with
  | send to' bytes now =>
    have hpend := hpend to' bytes now rfl
    simp only [Courier.step]
    split
    · exact frame hnone rfl rfl (Nat.le_refl _)
    · next hs =>
      have hs : c.stopped = false := by simpa using hs
      have enqueueCase (hl : ∀ k, (c.wire to').line ≠ .up k false) :
          ∃ o', (([] : List (Action σ)).map Entry.did).foldlM (Order.next to) o₁ = some o'
            ∧ Order.Holds to (enqueue limits c to' (c.wire to') bytes) o' := by
        refine ⟨o₁, rfl, by simpa using ho₁.1, by simpa using ho₁.2.1, ?_, ?_⟩
        · rw [wire_enqueue]
          split
          · next hc =>
            obtain ⟨rfl, -⟩ := hc
            rw [hpend rfl, Fifo.toList_push]
            exact ho.2.2.1.append (List.Sublist.refl _)
          · exact ho₁.2.2.1
        · rw [wire_enqueue]
          split
          · next hc => obtain ⟨rfl, -⟩ := hc; exact fun k hk => absurd hk (hl k)
          · exact ho₁.2.2.2
      have dialCase (hl : (c.wire to').line.conn? = none) :
          ∃ o', ((dial (σ := σ) limits c to' bytes).2.map Entry.did).foldlM (Order.next to) o₁
              = some o'
            ∧ Order.Holds to (dial (σ := σ) limits c to' bytes).1 o' := by
        have hfresh : c.nextConn ∉ o₁.conns := fun hm => by
          have := (ho₁.2.1 _ hm).1; unfold Conn at *; omega
        by_cases ht : to' = to
        · subst ht
          refine ⟨{ o₁ with conns := c.nextConn :: o₁.conns }, by simp [Order.next], ?_⟩
          refine ⟨fun k hk => ?_, fun k hk => ?_, ?_, fun k hk => by simp at hk⟩
          · simp only [dialed_dial, Std.HashMap.getElem?_insert, beq_iff_eq] at hk
            split at hk
            · next he => exact he ▸ List.mem_cons_self
            · exact List.mem_cons_of_mem _ (ho₁.1 k hk)
          · simp only [List.mem_cons] at hk
            simp only [dialed_dial, nextConn_dial, Std.HashMap.getElem?_insert, beq_iff_eq]
            rcases hk with rfl | hk
            · simp
            · obtain ⟨hlt, hk'⟩ := ho₁.2.1 k hk
              have : c.nextConn ≠ k := fun e => by unfold Conn at *; omega
              simp only [this, ↓reduceIte]
              exact ⟨Nat.lt_succ_of_lt hlt, hk'⟩
          · simp only [wire_dial, ↓reduceIte, hpend rfl]
            split
            · simp
            · simp
        · refine ⟨o₁, by simp [Order.next, ht], ?_⟩
          refine ⟨fun k hk => ?_, fun k hk => ?_, ?_, ?_⟩
          · simp only [dialed_dial, Std.HashMap.getElem?_insert, beq_iff_eq] at hk
            split at hk
            · exact absurd (Option.some.inj hk) ht
            · exact ho₁.1 k hk
          · obtain ⟨hlt, hk'⟩ := ho₁.2.1 k hk
            have : c.nextConn ≠ k := fun e => by unfold Conn at *; omega
            simp only [dialed_dial, nextConn_dial, Std.HashMap.getElem?_insert, beq_iff_eq, this,
              ↓reduceIte]
            exact ⟨Nat.lt_succ_of_lt hlt, hk'⟩
          · simpa [ht] using ho₁.2.2.1
          · simpa [ht] using ho₁.2.2.2
      split
      · next heq => exact dialCase (by simp [heq])
      · next heq =>
        split
        · exact dialCase (by simp [heq])
        · exact frame hnone rfl rfl (Nat.le_refl _)
      · next conn heq => exact enqueueCase (by simp [heq])
      · next conn heq =>
        have hd := (h.wired conn to').mpr (by simp [heq])
        by_cases ht : to' = to
        · subst ht
          have hempty := ho₁.2.2.2 conn heq
          have := writeTo (line := .up conn true) (rest := (c.wire to').waiting) hd
            (by rw [hempty, hpend rfl]; exact List.sublist_append_right _ _) (by simp)
          simpa using this
        · refine ⟨o₁, by simp [Order.next, Order.not_mem ho₁ hd ht], ?_⟩
          exact Order.holds_frame ho₁ rfl (by simp [ht]) (Nat.le_refl _)
      · next conn heq => exact enqueueCase (by simp [heq])
  | connected conn' | written conn' =>
    have viaNext {to'' : Address} (hd : c.dialed[conn']? = some to'') :
        ∃ o', ((next (σ := σ) c to'' conn' (c.wire to'')).2.map Entry.did).foldlM (Order.next to) o₁
            = some o'
          ∧ Order.Holds to (next (σ := σ) c to'' conn' (c.wire to'')).1 o' := by
      by_cases ht : to'' = to
      · subst ht
        cases hp : (c.wire to'').waiting.pop? with
        | none =>
          rw [next_of_none _ _ _ _ hp]
          refine ⟨o₁, rfl, ho₁.1, ho₁.2.1, by simpa using ho₁.2.2.1, fun k _ => ?_⟩
          simpa using Fifo.pop?_eq_none.mp hp
        | some p =>
          obtain ⟨bytes, rest⟩ := p
          rw [next_of_pop _ _ _ _ _ hp]
          have hsub := ho₁.2.2.1
          rw [Fifo.toList_of_pop? hp] at hsub
          simpa using writeTo (line := .up conn' true) hd hsub (by simp)
      · cases hp : (c.wire to'').waiting.pop? with
        | none =>
          rw [next_of_none _ _ _ _ hp]
          exact ⟨o₁, rfl, Order.holds_frame ho₁ rfl (by simp [ht]) (Nat.le_refl _)⟩
        | some p =>
          obtain ⟨bytes, rest⟩ := p
          rw [next_of_pop _ _ _ _ _ hp]
          refine ⟨o₁, by simp [Order.next, Order.not_mem ho₁ hd ht], ?_⟩
          exact Order.holds_frame ho₁ rfl (by simp [ht]) (Nat.le_refl _)
    simp only [Courier.step]
    split
    · next to'' hto =>
      split
      · exact viaNext hto
      · exact frame hnone rfl rfl (Nat.le_refl _)
    · exact frame hnone rfl rfl (Nat.le_refl _)
  | broken conn' now =>
    simp only [Courier.step]
    have erased {c' : Courier} (hd' : c'.dialed = c.dialed.erase conn')
        (hn : c'.nextConn = c.nextConn)
        (hw : (c'.wire to).waiting.toList = [] ∧ (∀ k, (c'.wire to).line ≠ .up k false)
          ∨ c'.wire to = c.wire to) :
        Order.Holds to c' o₁ := by
      refine ⟨fun k hk => ?_, fun k hk => ?_, ?_, ?_⟩
      · rw [hd', Std.HashMap.getElem?_erase] at hk
        split at hk
        · cases hk
        · exact ho₁.1 k hk
      · obtain ⟨hlt, hk'⟩ := ho₁.2.1 k hk
        refine ⟨hn ▸ hlt, ?_⟩
        rw [hd', Std.HashMap.getElem?_erase]
        split
        · exact Or.inl rfl
        · exact hk'
      · rcases hw with ⟨hw, -⟩ | hw
        · rw [hw]; exact List.nil_sublist _
        · rw [hw]; exact ho₁.2.2.1
      · rcases hw with ⟨-, hw⟩ | hw
        · exact fun k hk => absurd hk (hw k)
        · rw [hw]; exact ho₁.2.2.2
    split
    · next to'' hto =>
      split
      · refine ⟨o₁, Order.foldlM_quiet (by simp), erased (by simp) (by simp) ?_⟩
        rw [wire_setWire]
        split
        · exact Or.inl ⟨by simp [Fifo.toList], by simp⟩
        · exact Or.inr (by simp)
      · exact ⟨o₁, Order.foldlM_quiet (by simp), erased rfl rfl (Or.inr (by simp))⟩
    · split
      · exact frame (by simp) rfl (by simp) (Nat.le_refl _)
      · exact frame hnone rfl rfl (Nat.le_refl _)
  | accepted =>
    simp only [Courier.step]
    split
    · exact frame (by simp) rfl rfl (Nat.le_refl _)
    · exact frame (by simp) rfl (by simp) (Nat.le_succ _)
  | received conn' bytes =>
    have hacts {ps : List (Parcel σ)} {extra : List (Action σ)}
        (he : ∀ a ∈ extra, a = .close conn') :
        ∀ a ∈ ps.map Action.deliver ++ extra, (∀ k to', a ≠ .dial k to')
          ∧ ∀ k bytes, a ≠ .write k bytes := by
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨p, -, rfl⟩ := List.mem_map.mp ha
        exact ⟨by simp, by simp⟩
      · cases he a ha
        exact ⟨by simp, by simp⟩
    simp only [Courier.step]
    split
    · split
      · split
        · exact frame (hacts (by simp)) rfl (by simp) (Nat.le_refl _)
        · exact frame (by simp) rfl (by simp) (Nat.le_refl _)
      · exact frame (by simp) rfl (by simp) (Nat.le_refl _)
    · split
      · exact frame hnone rfl rfl (Nat.le_refl _)
      · exact frame (by simp) rfl rfl (Nat.le_refl _)
  | stop =>
    simp only [Courier.step]
    refine ⟨o₁, Order.foldlM_quiet ?_, fun k hk => by simp at hk, fun k hk => ?_,
      by simp [Fifo.toList], fun k hk => by simp at hk⟩
    · intro a ha
      obtain ⟨k, -, rfl⟩ := List.mem_map.mp ha
      exact ⟨by simp, by simp⟩
    · exact ⟨(ho₁.2.1 k hk).1, Or.inl (by simp)⟩


/-- What the courier asks to be written on connections to a process is what it was told to send
there, in the order it was told, each parcel at most once: some may be dropped, none is
repeated or reordered. -/
theorem written_sublist_sent (es : List Event) (to : Address) :
    (writtenTo to [] (exec limits read {} es).2).Sublist
      (sentTo to (exec limits read {} es).2) := by
  obtain ⟨o, ho, -⟩ := exec_foldlM (R := Order.Holds to) (fun _ _ e hc hR => order_step hc hR e)
    (sound_empty (limits := limits)) (m := {})
    ⟨by simp, by simp, by simp [Fifo.toList], fun k hk => by simp at hk⟩ es
  simpa using Order.foldlM_sublist ho

end OrderStep

section Reading

variable {c : Courier}

/-- What a reader that uses `read` makes of bytes arriving in pieces, as the courier reads them:
each time, all that has arrived and was not yet taken, until `read` refuses it or too much is
left over. -/
def readPieces (limits : Limits) (read : ByteArray → Option (List (Parcel σ) × Nat))
    (buffer : ByteArray) : List ByteArray → List (Parcel σ)
  | [] => []
  | piece :: pieces =>
    match read (buffer ++ piece) with
    | some (parcels, taken) =>
      if ((buffer ++ piece).extract taken (buffer ++ piece).size).size > limits.maxParcelBytes then
        parcels
      else parcels ++ readPieces limits read ((buffer ++ piece).extract taken (buffer ++ piece).size)
        pieces
    | none => []

def _root_.Lanes.Peers.Event.receives (conn : Conn) : Event → Bool
  | .received k _ => k == conn
  | _ => false

def _root_.Lanes.Peers.Entry.closes (conn : Conn) : Entry σ → Bool
  | .did (.close k) => k == conn
  | _ => false

/-- The bytes the courier was told of on `conn`, in order. -/
def receivedOn (conn : Conn) : List (Entry σ) → List ByteArray
  | [] => []
  | .told (.received k bytes) :: log => if k = conn then bytes :: receivedOn conn log
    else receivedOn conn log
  | _ :: log => receivedOn conn log

/-- The parcels the courier delivered on being told of bytes on `conn`, in order. -/
def deliveredFrom (conn : Conn) (reading : Bool) : List (Entry σ) → List (Parcel σ)
  | [] => []
  | .told e :: log => deliveredFrom conn (e.receives conn) log
  | .did (.deliver p) :: log => if reading then p :: deliveredFrom conn reading log
    else deliveredFrom conn reading log
  | .did _ :: log => deliveredFrom conn reading log

def _root_.Lanes.Peers.Action.parcel? : Action σ → Option (Parcel σ)
  | .deliver p => some p
  | _ => none

theorem deliveredFrom_did (conn : Conn) (b : Bool) (acts : List (Action σ)) (l : List (Entry σ)) :
    deliveredFrom conn b (acts.map Entry.did ++ l)
      = (if b then acts.filterMap Action.parcel? else []) ++ deliveredFrom conn b l := by
  induction acts with
  | nil => cases b <;> rfl
  | cons a acts ih =>
    cases a <;> cases b <;> simp_all [deliveredFrom, Action.parcel?, List.filterMap_cons]

theorem receivedOn_did (conn : Conn) (acts : List (Action σ)) (l : List (Entry σ)) :
    receivedOn conn (acts.map Entry.did ++ l) = receivedOn conn l := by
  induction acts with
  | nil => rfl
  | cons a acts ih => simpa [receivedOn] using ih

theorem takeWhile_did_of_not_closes {conn : Conn} {acts : List (Action σ)} (l : List (Entry σ))
    (h : ∀ a ∈ acts, a ≠ .close conn) :
    (acts.map Entry.did ++ l).takeWhile (!·.closes conn)
      = acts.map Entry.did ++ l.takeWhile (!·.closes conn) := by
  induction acts with
  | nil => rfl
  | cons a acts ih =>
    have ha := h a List.mem_cons_self
    have : (Entry.did (σ := σ) a).closes conn = false := by
      cases a <;> simp_all [Entry.closes]
    simp [this, ih fun a' ha' => h a' (List.mem_cons_of_mem _ ha')]

theorem receivedOn_takeWhile_closes {conn : Conn} {acts : List (Action σ)} (l : List (Entry σ))
    (h : .close conn ∈ acts) :
    receivedOn conn ((acts.map Entry.did ++ l).takeWhile (!·.closes conn)) = [] := by
  induction acts with
  | nil => simp at h
  | cons a acts ih =>
    by_cases ha : a = .close conn
    · subst ha; simp [Entry.closes, receivedOn]
    · have hm : .close conn ∈ acts := (List.mem_cons.mp h).resolve_left (Ne.symm ha)
      have : (Entry.did (σ := σ) a).closes conn = false := by
        cases a <;> simp_all [Entry.closes]
      simp [this, receivedOn, ih hm]

end Reading

section ReadingSteps

variable {c : Courier}

theorem nextConn_le_step (e : Event) : c.nextConn ≤ (c.step limits read e).1.nextConn := by
  cases e with
  | send to bytes now =>
    simp only [Courier.step]
    split
    · exact Nat.le_refl _
    · split
      · simp
      · split
        · simp
        · exact Nat.le_refl _
      all_goals simp
  | connected conn | written conn =>
    simp only [Courier.step]
    split
    · split
      · simp
      · exact Nat.le_refl _
    · exact Nat.le_refl _
  | broken conn now =>
    simp only [Courier.step]
    split
    · split <;> exact Nat.le_refl _
    · split <;> exact Nat.le_refl _
  | accepted =>
    simp only [Courier.step]
    split
    · exact Nat.le_refl _
    · exact Nat.le_succ _
  | received conn bytes =>
    simp only [Courier.step]
    split
    · split
      · split <;> exact Nat.le_refl _
      · exact Nat.le_refl _
    · split <;> exact Nat.le_refl _
  | stop => exact Nat.le_refl _

/-- What a step that is not told of bytes on `conn` does to it, while the courier reads it:
closes it and forgets it, or leaves it as it was. -/
theorem inbound_step (h : Sound limits c) {conn : Conn} {buf : ByteArray}
    (hbuf : c.inbound[conn]? = some buf) {e : Event} (he : e.receives conn = false) :
    (.close conn ∈ (c.step limits read e).2 ∧ conn ∉ (c.step limits read e).1.inbound)
      ∨ ((∀ a ∈ (c.step limits read e).2, a ≠ .close conn)
        ∧ (c.step limits read e).1.inbound[conn]? = some buf) := by
  have hin := mem_of_getElem? hbuf
  have hnd : conn ∉ c.dialed := fun hm => h.apart _ hm hin
  cases e with
  | send to bytes now =>
    right
    simp only [Courier.step]
    split
    · simp [hbuf]
    · split
      · simp [hbuf]
      · split
        · simp [hbuf]
        · simp [hbuf]
      all_goals simp [hbuf]
  | connected k | written k =>
    right
    simp only [Courier.step]
    split
    · split
      · next to hto _ =>
        cases hp : (c.wire to).waiting.pop? with
        | none => rw [next_of_none _ _ _ _ hp]; simp [hbuf]
        | some p =>
          obtain ⟨bytes, rest⟩ := p
          rw [next_of_pop _ _ _ _ _ hp]; simp [hbuf]
      · simp [hbuf]
    · simp [hbuf]
  | broken k now =>
    simp only [Courier.step]
    split
    · next to hto =>
      right
      have hk : k ≠ conn := fun e => hnd (e ▸ mem_of_getElem? hto)
      split <;> simp [hbuf, hk]
    · split
      · by_cases hk : k = conn
        · subst hk; left; simp
        · right; simp [hk, hbuf, Std.HashMap.getElem?_erase]
      · right; simp [hbuf]
  | accepted =>
    right
    simp only [Courier.step]
    split
    · simp [hbuf]
    · have hne : c.nextConn ≠ conn := fun e => by
        have := h.inbound_lt _ hin; unfold Conn at *; omega
      simp [hbuf, Std.HashMap.getElem?_insert, hne]
  | received k bytes =>
    have hk : k ≠ conn := by simpa [Event.receives] using he
    right
    simp only [Courier.step]
    split
    · split
      · split
        · refine ⟨?_, by simp [hbuf, hk, Std.HashMap.getElem?_erase]⟩
          intro a ha
          simp only [List.mem_append, List.mem_map, List.mem_singleton] at ha
          rcases ha with ⟨p, -, rfl⟩ | rfl <;> simp [hk]
        · simp [hbuf, hk, Std.HashMap.getElem?_insert]
      · simp [hbuf, hk, Std.HashMap.getElem?_erase]
    · split <;> simp [hbuf, hk]
  | stop =>
    left
    simp [Courier.step, Std.HashMap.mem_keys, hin]

/-- A connection the courier has stopped reading stays so, and bytes on it deliver nothing. -/
theorem closed_step {conn : Conn} (hlt : conn < c.nextConn)
    (hnot : conn ∉ c.inbound) (e : Event) :
    conn < (c.step limits read e).1.nextConn ∧ conn ∉ (c.step limits read e).1.inbound
      ∧ (e.receives conn = true → (c.step limits read e).2.filterMap Action.parcel? = []) := by
  refine ⟨Nat.lt_of_lt_of_le hlt (nextConn_le_step e), ?_, ?_⟩
  · cases e with
    | send to bytes now =>
      simp only [Courier.step]
      split
      · exact hnot
      · split
        · simpa using hnot
        · split
          · simpa using hnot
          · exact hnot
        all_goals simpa using hnot
    | connected k | written k =>
      simp only [Courier.step]
      split
      · split
        · simpa using hnot
        · exact hnot
      · exact hnot
    | broken k now =>
      simp only [Courier.step]
      split
      · split <;> simpa using hnot
      · split
        · simp [Std.HashMap.mem_erase, hnot]
        · exact hnot
    | accepted =>
      simp only [Courier.step]
      split
      · exact hnot
      · have hne : c.nextConn ≠ conn := fun e => by unfold Conn at *; omega
        simp [Std.HashMap.mem_insert, hne, hnot]
    | received k bytes =>
      simp only [Courier.step]
      split
      · next earlier hearlier =>
        have hk : k ≠ conn := fun e => hnot (e ▸ mem_of_getElem? hearlier)
        split
        · split
          · simp [Std.HashMap.mem_erase, hnot]
          · simp [Std.HashMap.mem_insert, hk, hnot]
        · simp [Std.HashMap.mem_erase, hnot]
      · split <;> exact hnot
    | stop => exact Std.HashMap.not_mem_empty
  · intro hr
    cases e with
    | received k bytes =>
      have hk : k = conn := by simpa [Event.receives] using hr
      subst hk
      have hnone : c.inbound[k]? = none := Std.HashMap.getElem?_eq_none hnot
      simp only [Courier.step, hnone]
      split <;> rfl
    | _ => simp [Event.receives] at hr

end ReadingSteps

section Delivered

/-- What is left of `buf ++ bytes` once `taken` bytes of it are read. -/
def leftover (buf bytes : ByteArray) (taken : Nat) : ByteArray :=
  (buf ++ bytes).extract taken (buf ++ bytes).size

theorem deliveredFrom_exec (conn : Conn) (b : Bool) (c : Courier) (es : List Event) :
    deliveredFrom conn b (exec limits read c es).2 = deliveredFrom conn false (exec limits read c es).2 := by
  cases es with
  | nil => rfl
  | cons e es => simp [exec, deliveredFrom]

theorem receivedOn_told {conn : Conn} {e : Event} (he : e.receives conn = false) (l : List (Entry σ)) :
    receivedOn conn (.told e :: l) = receivedOn conn l := by
  cases e with
  | received k bytes =>
    have hk : k ≠ conn := by simpa [Event.receives] using he
    simp [receivedOn, hk]
  | _ => rfl

theorem delivered_closed {c : Courier} {conn : Conn} (hlt : conn < c.nextConn)
    (hnot : conn ∉ c.inbound) (es : List Event) :
    deliveredFrom conn false (exec limits read c es).2 = [] := by
  induction es generalizing c with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨h₁, h₂, h₃⟩ := closed_step (limits := limits) (read := read) hlt hnot e
    rw [exec_cons, List.cons_append]
    simp only [deliveredFrom]
    rw [deliveredFrom_did, deliveredFrom_exec, ih h₁ h₂]
    cases hr : e.receives conn
    · rfl
    · simp [h₃ hr]

/-- While the courier reads `conn` with `buf` not yet a whole parcel, what it delivers on bytes
told of on `conn` is what `read` makes of them, from `buf` on, until it closes `conn`. -/
theorem delivered_reading {c : Courier} (h : Sound limits c) {conn : Conn} {buf : ByteArray}
    (hbuf : c.inbound[conn]? = some buf) (es : List Event) :
    deliveredFrom conn false (exec limits read c es).2
      = readPieces limits read buf
          (receivedOn conn ((exec limits read c es).2.takeWhile (!·.closes conn))) := by
  induction es generalizing c buf with
  | nil => rfl
  | cons e es ih =>
    have hlt := h.inbound_lt _ (mem_of_getElem? hbuf)
    rw [exec_cons, List.cons_append]
    have htold : (Entry.told (σ := σ) e).closes conn = false := rfl
    simp only [deliveredFrom, List.takeWhile_cons, htold, Bool.not_false, ↓reduceIte]
    cases hr : e.receives conn
    · rw [receivedOn_told hr, deliveredFrom_did]
      simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append]
      rcases inbound_step h hbuf hr with ⟨hclose, hgone⟩ | ⟨hkeep, hbuf'⟩
      · rw [receivedOn_takeWhile_closes _ hclose,
          delivered_closed (Nat.lt_of_lt_of_le hlt (nextConn_le_step e)) hgone]
        rfl
      · rw [takeWhile_did_of_not_closes _ hkeep, receivedOn_did]
        exact ih (h.step e) hbuf'
    · cases e with
      | received k bytes =>
        have hk : k = conn := by simpa [Event.receives] using hr
        subst hk
        have hs := h.step (read := read) (.received k bytes)
        simp only [receivedOn, ↓reduceIte, readPieces]
        cases hread : read (buf ++ bytes) with
        | none =>
          have hstep : c.step limits read (.received k bytes)
              = ({ c with inbound := c.inbound.erase k }, [.close k]) := by
            simp [Courier.step, hbuf, hread]
          rw [hstep, deliveredFrom_did]
          simp only [↓reduceIte, List.filterMap_cons, Action.parcel?, List.filterMap_nil,
            List.nil_append]
          rw [deliveredFrom_exec, delivered_closed (c := { c with inbound := c.inbound.erase k }) hlt
            (by simp)]
        | some r =>
          obtain ⟨parcels, taken⟩ := r
          have hparcels : (parcels.map Action.deliver).filterMap (Action.parcel? (σ := σ)) = parcels := by
            simp [List.filterMap_map, Function.comp_def, Action.parcel?]
          simp only
          split
          · next hlarge =>
            have hstep : c.step limits read (.received k bytes)
                = ({ c with inbound := c.inbound.erase k }, parcels.map .deliver ++ [.close k]) := by
              simp only [Courier.step, hbuf, hread, hlarge, ↓reduceIte]
            rw [hstep, deliveredFrom_did, deliveredFrom_exec,
              delivered_closed (c := { c with inbound := c.inbound.erase k }) hlt (by simp)]
            simp [List.filterMap_append, hparcels, Action.parcel?]
          · next hsmall =>
            have hstep : c.step limits read (.received k bytes)
                = ({ c with inbound := c.inbound.insert k (leftover buf bytes taken) },
                  parcels.map .deliver) := by
              simp only [Courier.step, hbuf, hread, hsmall, ↓reduceIte, leftover]
            rw [hstep] at hs ⊢
            rw [deliveredFrom_did, deliveredFrom_exec]
            simp only [↓reduceIte]
            rw [hparcels, takeWhile_did_of_not_closes _ (by simp), receivedOn_did]
            congr 1
            simpa [leftover] using ih (buf := leftover buf bytes taken) hs (by simp)
      | _ => simp [Event.receives] at hr

/-- Every answer in a run is one of the answers to one step of it. -/
theorem exec_eq_did {c : Courier} {es : List Event} {p₁ p₂ : List (Entry σ)} {a : Action σ}
    (h : (exec limits read c es).2 = p₁ ++ .did a :: p₂) :
    ∃ es₁ e es₂ acts₁ acts₂, es = es₁ ++ e :: es₂
      ∧ ((exec limits read c es₁).1.step limits read e).2 = acts₁ ++ a :: acts₂
      ∧ p₂ = acts₂.map Entry.did
        ++ (exec limits read ((exec limits read c es₁).1.step limits read e).1 es₂).2 := by
  induction es generalizing c p₁ with
  | nil => simp [exec] at h
  | cons e es ih =>
    rw [exec_cons, List.cons_append] at h
    cases p₁ with
    | nil => simp at h
    | cons x p₁ =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨-, h⟩ := h
      rcases List.append_eq_append_iff.mp h.symm with ⟨a', hacts, hrest⟩ | ⟨c', hp, hlog⟩
      · cases a' with
        | nil =>
          simp only [List.nil_append] at hrest
          obtain ⟨es₁, e', es₂, acts₁, acts₂, rfl, hstep, hp₂⟩ :=
            ih (c := (c.step limits read e).1) (p₁ := []) (by simpa using hrest.symm)
          exact ⟨e :: es₁, e', es₂, acts₁, acts₂, rfl, hstep, hp₂⟩
        | cons y a'' =>
          simp only [List.cons_append, List.cons.injEq] at hrest
          obtain ⟨rfl, rfl⟩ := hrest
          obtain ⟨acts₁, rest, hsplit, h₁, h₂⟩ := List.map_eq_append_iff.mp hacts
          obtain ⟨b, acts₂, rfl, hb, h₂'⟩ := List.map_eq_cons_iff.mp h₂
          cases hb
          exact ⟨[], e, es, acts₁, acts₂, rfl, hsplit, by rw [h₂']; rfl⟩
      · obtain ⟨es₁, e', es₂, acts₁, acts₂, rfl, hstep, hp₂⟩ := ih hlog
        exact ⟨e :: es₁, e', es₂, acts₁, acts₂, rfl, hstep, hp₂⟩

theorem adopt_step {c : Courier} {e : Event} {conn : Conn}
    (h : .adopt conn ∈ (c.step limits read e).2) :
    c.step limits read e
        = ({ c with nextConn := c.nextConn + 1, inbound := c.inbound.insert c.nextConn .empty },
          [.adopt c.nextConn])
      ∧ conn = c.nextConn := by
  cases e with
  | accepted =>
    simp only [Courier.step] at h ⊢
    split at h
    · simp at h
    · next hs => simp only [List.mem_singleton, Action.adopt.injEq] at h; simp [hs, h]
  | send to bytes now =>
    exfalso
    simp only [Courier.step] at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · split at h <;> simp at h
      · simp at h
      · simp at h
      · simp at h
  | connected k | written k =>
    exfalso
    simp only [Courier.step] at h
    split at h
    · split at h
      · unfold Courier.next at h; split at h <;> simp at h
      · simp at h
    · simp at h
  | broken k now =>
    exfalso
    simp only [Courier.step] at h
    split at h
    · split at h <;> simp at h
    · split at h <;> simp at h
  | received k bytes =>
    exfalso
    simp only [Courier.step] at h
    split at h
    · split at h
      · split at h <;> simp at h
      · simp at h
    · split at h <;> simp at h
  | stop => simp [Courier.step] at h

/-- What the courier delivers from a connection it adopted is what `read` makes of the bytes it
was told of on that connection, in the order they came, until it closes the connection; after
that, nothing. Nothing that came on another connection, and nothing else it was told, changes
it. With `Parcel.receive` as `read` this is `Parcel.receive` applied to the bytes received on the
connection (`Parcel.receive_send` says what that is for a stream of parcels). -/
theorem delivered_read {es : List Event} {p₁ p₂ : List (Entry σ)} {conn : Conn}
    (h : (exec limits read {} es).2 = p₁ ++ .did (.adopt conn) :: p₂) :
    deliveredFrom conn false p₂
      = readPieces limits read .empty (receivedOn conn (p₂.takeWhile (!·.closes conn))) := by
  obtain ⟨es₁, e, es₂, acts₁, acts₂, rfl, hstep, rfl⟩ := exec_eq_did h
  have hc : Sound limits (exec limits read {} es₁).1 := sound_empty.exec es₁
  obtain ⟨hs, rfl⟩ := adopt_step (hstep ▸ List.mem_append_right _ List.mem_cons_self)
  rw [hs] at hstep ⊢
  have hacts₂ : acts₂ = [] := by
    simp only at hstep
    cases acts₁ with
    | nil => simpa using hstep.symm
    | cons a acts₁ => simp at hstep
  subst hacts₂
  have hs' := hc.step (read := read) e
  rw [hs] at hs'
  simpa using delivered_reading hs' (buf := .empty) (by simp) es₂

end Delivered

end Courier

end Lanes.Peers
