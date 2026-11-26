/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std.Data.TreeMap.Lemmas
public import Lanes.Actors.KernelSound
import Std.Data.DTreeMap.Internal.WF.Lemmas

/-!
The kernel's agenda holds exactly the timers its actors have pending (`Kernel.WellFormed`),
from boot and whatever a shell does (`Kernel.exec_wellFormed`). So, by the theorems of
`Kernel.WellFormed`: a timer that is due is not slept through (`wait_of_due`), a kernel that
says there is work does some (`step_events_ne_nil`), idle means nothing queued and nothing
pending (`quiet_iff`), and the shell sleeps until the earliest deadline, no longer and no
shorter (`wait_for_ms`).

Timers and messages take turns, so neither starves the other: the oldest message is served by
the next step or the one after (`step_of_queued`), and so is a timer that is due
(`step_of_due`). Each has one exception, which is the semantics' and not the scheduler's: the
step that went first stopped the message's receiver, or disarmed the timer.
-/

public section

namespace Lanes

private theorem minEntry?_eq_head?_toList {α β : Type} {cmp : α → α → Ordering}
    (t : Std.TreeMap α β cmp) : t.minEntry? = t.toList.head? := by
  open Std.DTreeMap.Internal in
  show Impl.Const.minEntry? t.inner.inner = (Impl.Const.toList t.inner.inner).head?
  rw [Impl.Const.toList_eq_toListModel_map]
  induction t.inner.inner with
  | leaf => simp [Impl.Const.minEntry?]
  | inner _ k v l r ihl _ =>
    cases l with
    | leaf => simp [Impl.Const.minEntry?, Impl.toListModel_inner]
    | inner => simpa [Impl.Const.minEntry?, Impl.toListModel_inner] using ihl

private theorem minKey?_eq_map_minEntry? {α β : Type} {cmp : α → α → Ordering}
    [Std.TransCmp cmp] (t : Std.TreeMap α β cmp) : t.minKey? = t.minEntry?.map (·.1) := by
  rw [Std.TreeMap.minKey?_eq_head?_keys, ← Std.TreeMap.map_fst_toList_eq_keys,
    minEntry?_eq_head?_toList, List.head?_map]

private theorem getElem?_of_minEntry? {α β : Type} {cmp : α → α → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] {t : Std.TreeMap α β cmp} {a : α} {b : β}
    (h : t.minEntry? = some (a, b)) : t[a]? = some b := by
  rw [minEntry?_eq_head?_toList] at h
  exact Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp (List.mem_of_head? h)

private theorem getElem?_ofList_toList {α β : Type} {cmp : α → α → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] (t : Std.TreeMap α β cmp) (a : α) :
    (Std.TreeMap.ofList t.toList cmp)[a]? = t[a]? := by
  cases h : t[a]? with
  | some b =>
    exact Std.TreeMap.getElem?_ofList_of_mem (k := a) Std.ReflCmp.compare_self
      Std.TreeMap.distinct_keys_toList (Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr h)
  | none =>
    cases h' : (Std.TreeMap.ofList t.toList cmp)[a]? with
    | none => rfl
    | some b =>
      have hmem : a ∈ Std.TreeMap.ofList t.toList cmp :=
        Std.TreeMap.mem_iff_isSome_getElem?.mpr (by simp [h'])
      have : a ∈ t := by
        letI : BEq α := ⟨fun x y => cmp x y == .eq⟩
        haveI : Std.LawfulBEqCmp cmp :=
          ⟨fun {x y} => (beq_iff_eq (a := cmp x y) (b := .eq)).symm⟩
        rw [Std.TreeMap.mem_ofList, Std.TreeMap.map_fst_toList_eq_keys,
          Std.TreeMap.contains_keys] at hmem
        exact Std.TreeMap.contains_iff_mem.mp hmem
      rw [Std.TreeMap.mem_iff_isSome_getElem?, h] at this
      cases this

/-! Lists of pairs with no first component twice, as a cell's timers are. -/

private theorem snd_eq_of_nodup_fst {α β : Type} {l : List (α × β)}
    (hl : (l.map (·.1)).Nodup) {a : α} {b b' : β} (h : (a, b) ∈ l) (h' : (a, b') ∈ l) :
    b = b' := by
  induction l with
  | nil => cases h
  | cons t l ih =>
    rw [List.map_cons, List.nodup_cons] at hl
    have hnot : ∀ c, (a, c) ∈ l → t.1 ≠ a := fun c hc heq =>
      hl.1 (List.mem_map.mpr ⟨(a, c), hc, heq.symm⟩)
    rcases List.mem_cons.mp h with heq | hb
    · rcases List.mem_cons.mp h' with heq' | hb'
      · exact (Prod.mk.inj (heq.trans heq'.symm)).2
      · exact absurd (heq ▸ rfl) (hnot _ hb')
    · rcases List.mem_cons.mp h' with heq' | hb'
      · exact absurd (heq' ▸ rfl) (hnot _ hb)
      · exact ih hl.2 hb hb'

private theorem mem_eraseP_fst {α β : Type} [DecidableEq α] {l : List (α × β)}
    (hl : (l.map (·.1)).Nodup) (a₀ a : α) (b : β) :
    (a, b) ∈ l.eraseP (·.1 = a₀) ↔ ¬ a = a₀ ∧ (a, b) ∈ l := by
  induction l with
  | nil => simp
  | cons t l ih =>
    rw [List.map_cons, List.nodup_cons] at hl
    by_cases ht : t.1 = a₀
    · rw [List.eraseP_cons_of_pos (by simpa using ht)]
      constructor
      · intro hm
        exact ⟨fun ha => hl.1 (List.mem_map.mpr ⟨(a, b), hm, by simp [ha, ht]⟩),
          List.mem_cons_of_mem _ hm⟩
      · rintro ⟨ha, hm⟩
        rcases List.mem_cons.mp hm with rfl | hm
        · exact absurd ht ha
        · exact hm
    · rw [List.eraseP_cons_of_neg (by simpa using ht), List.mem_cons, List.mem_cons, ih hl.2]
      constructor
      · rintro (rfl | h)
        · exact ⟨ht, .inl rfl⟩
        · exact ⟨h.1, .inr h.2⟩
      · rintro ⟨ha, rfl | h⟩
        · exact .inl rfl
        · exact .inr ⟨ha, h⟩

private theorem nodup_fst_eraseP {α β : Type} {l : List (α × β)} (hl : (l.map (·.1)).Nodup)
    (p : α × β → Bool) : ((l.eraseP p).map (·.1)).Nodup :=
  hl.sublist ((List.eraseP_sublist).map _)

private theorem mem_find?_fst {α β : Type} [DecidableEq α] {l : List (α × β)}
    (hl : (l.map (·.1)).Nodup) (a : α) (b : β) :
    b ∈ ((l.find? fun t => t.1 = a).toList.map Prod.snd) ↔ (a, b) ∈ l := by
  simp only [List.mem_map, Option.mem_toList]
  constructor
  · rintro ⟨t, ht, rfl⟩
    have := List.find?_some ht
    simp only [decide_eq_true_eq] at this
    exact this ▸ List.mem_of_find?_eq_some ht
  · intro hm
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp
      (List.find?_isSome.mpr ⟨(a, b), hm, by simp⟩ : (l.find? fun t => t.1 = a).isSome)
    have hfst := List.find?_some ht
    simp only [decide_eq_true_eq] at hfst
    have hmem : (a, t.2) ∈ l := hfst ▸ List.mem_of_find?_eq_some ht
    exact ⟨t, ht, snd_eq_of_nodup_fst hl hmem hm⟩

private theorem mem_arm {α β : Type} [DecidableEq α] (l : List (α × β)) (a : α) (b : β)
    (t : α × β) : t ∈ (if l.any (·.1 = a) then l.map fun t => if t.1 = a then (a, b) else t
      else l ++ [(a, b)]) ↔ t = (a, b) ∨ (¬ t.1 = a ∧ t ∈ l) := by
  split
  · rename_i hany
    obtain ⟨u, hu, hua⟩ := List.any_eq_true.mp hany
    simp only [decide_eq_true_eq] at hua
    simp only [List.mem_map]
    constructor
    · rintro ⟨s, hs, rfl⟩
      by_cases hsa : s.1 = a
      · exact .inl (by simp [hsa])
      · exact .inr (by simp [hsa, hs])
    · rintro (rfl | ⟨hta, ht⟩)
      · exact ⟨u, hu, by simp [hua]⟩
      · exact ⟨t, ht, by simp [hta]⟩
  · rename_i hany
    have hnone : ∀ s ∈ l, ¬ s.1 = a := fun s hs hsa =>
      hany (List.any_eq_true.mpr ⟨s, hs, by simp [hsa]⟩)
    simp only [List.mem_append, List.mem_singleton]
    constructor
    · rintro (ht | rfl)
      · exact .inr ⟨hnone t ht, ht⟩
      · exact .inl rfl
    · rintro (rfl | ⟨-, ht⟩)
      · exact .inr rfl
      · exact .inl ht

namespace Kernel

theorem Due.compare_eq : (compare : Due → Due → Ordering)
    = compareLex (compareOn (·.deadline_ms)) (compareOn (·.token)) := by
  funext a b
  cases a
  cases b
  simp [compare, instOrdDue.ord, compareLex, compareOn]

instance : Std.TransOrd Due := by
  unfold Std.TransOrd
  rw [Due.compare_eq]
  infer_instance

instance : Std.LawfulEqOrd Due where
  eq_of_compare {a b} h := by
    rw [Due.compare_eq, compareLex_eq_eq] at h
    cases a
    cases b
    simp_all [compareOn]

theorem Due.deadline_le_of_isLE {a b : Due} (h : (compare a b).isLE) :
    a.deadline_ms ≤ b.deadline_ms := by
  rw [Due.compare_eq] at h
  simp only [compareLex, compareOn] at h
  rcases Nat.lt_trichotomy a.deadline_ms b.deadline_ms with hlt | heq | hgt
  · exact Nat.le_of_lt hlt
  · exact Nat.le_of_eq heq
  · rw [Nat.compare_eq_gt.mpr hgt] at h
    cases h

variable {sys : System σ} [Hashable σ.Id] {k k' : Kernel sys}

theorem agenda_unschedule {dues : List Due} {d : Due} {entry : (i : σ.Id) × σ.Msg i} :
    (k.unschedule dues).agenda[d]? = some entry ↔ d ∉ dues ∧ k.agenda[d]? = some entry := by
  show (dues.foldl (·.erase ·) k.agenda)[d]? = _ ↔ _
  generalize k.agenda = agenda
  induction dues generalizing agenda with
  | nil => simp
  | cons a dues ih =>
    rw [List.foldl_cons, ih, Std.TreeMap.getElem?_erase]
    by_cases ha : a = d
    · simp [ha]
    · have hd : ¬ d = a := fun hd => ha hd.symm
      simp [ha, hd]

private theorem forall_cell {P : (j : σ.Id) → Cell sys j → Prop} {i : σ.Id} {c : Cell sys i}
    (hcell : k'.cell = update k.cell i c) (hi : P i c) (hrest : ∀ j, j ≠ i → P j (k.cell j))
    (j : σ.Id) : P j (k'.cell j) := by
  rw [hcell]
  by_cases hj : j = i
  · subst hj
    rw [update_self]
    exact hi
  · rw [update_of_ne _ _ hj]
    exact hrest j hj

/-- `k'` is `k` at the same time and turn, with messages added at the back of the queue. -/
private structure Sent (k k' : Kernel sys) : Prop where
  clock : k'.clock_ms = k.clock_ms
  turn : k'.timerTurn = k.timerTurn
  queue : ∃ sent, k'.queue.toList = k.queue.toList ++ sent

private theorem performAll_sent (k : Kernel sys) (i : σ.Id) (effs : List (Effect σ i)) :
    Sent k (k.performAll i effs).1 := by
  rw [performAll_eq]
  generalize ([] : List σ.Out) = outs
  induction effs generalizing k outs with
  | nil => exact ⟨rfl, rfl, [], (List.append_nil _).symm⟩
  | cons eff effs ih =>
    obtain ⟨hclock, hturn, later, hlater⟩ := ih (k.perform i eff).1 (outs ++ (k.perform i eff).2)
    have hone : Sent k (k.perform i eff).1 := by
      cases eff with
      | send to msg => exact ⟨rfl, rfl, [_], Fifo.toList_push _ _⟩
      | _ => exact ⟨rfl, rfl, [], (List.append_nil _).symm⟩
    obtain ⟨sent, hsent⟩ := hone.queue
    exact ⟨hclock.trans hone.clock, hturn.trans hone.turn, sent ++ later,
      by rw [List.foldl_cons, hlater, hsent, List.append_assoc]⟩

/-- What actor `i` handling a message leaves as it was: the clock, whose turn it is, and the
oldest message, unless that one was for `i` and `i` stopped. -/
private structure Kept (i : σ.Id) (k k' : Kernel sys) : Prop where
  clock : k'.clock_ms = k.clock_ms
  turn : k'.timerTurn = k.timerTurn
  oldest : ∀ e rest, k.queue.toList = e :: rest →
    (∃ rest', k'.queue.toList = e :: rest') ∨ e.dst = i ∧ (k'.cell i).up = false

private theorem settle_kept (k : Kernel sys) (i : σ.Id) (r : sys.State i × List (Effect σ i)) :
    Kept i k (k.settle i r).1 := by
  obtain ⟨hclock, hturn, sent, hsent⟩ :=
    performAll_sent (k.setCell i { (k.cell i) with state := r.1 }) i r.2
  replace hsent : _ = k.queue.toList ++ sent := hsent
  rw [settle_eq]
  generalize (k.setCell i { (k.cell i) with state := r.1 }).performAll i r.2 = p
    at hclock hturn hsent ⊢
  dsimp only
  split
  · refine ⟨hclock, hturn, fun e rest hq => ?_⟩
    by_cases hi : e.dst = i
    · exact .inr ⟨hi, by simp [down, cell_setCell]⟩
    · refine .inl ⟨(rest ++ sent).filter fun e => decide (e.dst ≠ i), ?_⟩
      show (p.1.queue.filter fun e => decide (e.dst ≠ i)).toList = _
      rw [Fifo.toList_filter, hsent, hq, List.cons_append,
        List.filter_cons_of_pos (by simpa using hi)]
  · exact ⟨hclock, hturn, fun e rest hq => .inl ⟨rest ++ sent, by rw [hsent, hq]; rfl⟩⟩

private theorem handle_kept (k : Kernel sys) (i : σ.Id) (msg : σ.Msg i) :
    Kept i k (k.handle i msg).1 :=
  settle_kept k i _

private theorem fire_kept (k : Kernel sys) (i : σ.Id) (msg : σ.Msg i) (due : Due) :
    Kept i k (k.fire i msg due).kernel := by
  rw [fire_eq]
  split
  · obtain ⟨hclock, hturn, holdest⟩ := handle_kept ((k.unschedule [due]).setCell i
      { (k.cell i) with timers := (k.cell i).timers.eraseP (·.1 = msg) }) i msg
    exact ⟨hclock, hturn, holdest⟩
  · exact ⟨rfl, rfl, fun e rest hq => .inl ⟨rest, hq⟩⟩

private theorem run1_kept (k : Kernel sys) :
    k.run1.kernel.clock_ms = k.clock_ms ∧ k.run1.kernel.timerTurn = k.timerTurn := by
  rw [run1_eq]
  split
  · exact ⟨rfl, rfl⟩
  · rename_i e rest _
    split
    · exact ⟨(handle_kept { k with queue := rest } e.dst e.msg).clock,
        (handle_kept { k with queue := rest } e.dst e.msg).turn⟩
    · exact ⟨(settle_kept (k.setCell e.dst { (k.cell e.dst) with up := true }) e.dst _).clock,
        (settle_kept (k.setCell e.dst { (k.cell e.dst) with up := true }) e.dst _).turn⟩

private theorem run1_serves {e : Envelope σ} {rest : List (Envelope σ)}
    (hq : k.queue.toList = e :: rest) :
    k.run1.events = .deliver e :: k.run1.outputs.map .output
      ∨ k.run1.events = .start e.dst :: k.run1.outputs.map .output := by
  rw [run1_eq]
  split
  · rename_i hpop
    rw [Fifo.pop?_eq_none.mp hpop] at hq
    cases hq
  · rename_i e' rest' hpop
    obtain ⟨rfl, -⟩ := List.cons.inj ((Fifo.toList_of_pop? hpop).symm.trans hq)
    split
    · exact .inl rfl
    · exact .inr rfl

theorem timerNext_eq_some_iff {t : Due × (i : σ.Id) × σ.Msg i} :
    k.timerNext = some t ↔ k.agenda.minEntry? = some t ∧ t.1.deadline_ms ≤ k.clock_ms
      ∧ (k.timerTurn = true ∨ k.queue.isEmpty = true) := by
  simp [timerNext, Option.filter_eq_some_iff]

theorem timerNext_of_minKey? {first : Due} (hmin : k.agenda.minKey? = some first)
    (hdue : first.deadline_ms ≤ k.clock_ms)
    (hturn : k.timerTurn = true ∨ k.queue.isEmpty = true) :
    ∃ i msg, k.timerNext = some (first, ⟨i, msg⟩) := by
  rw [minKey?_eq_map_minEntry?] at hmin
  obtain ⟨⟨first, i, msg⟩, hentry, rfl⟩ := Option.map_eq_some_iff.mp hmin
  exact ⟨i, msg, timerNext_eq_some_iff.mpr ⟨hentry, hdue, hturn⟩⟩

theorem timerNext_eq_none (hturn : ¬ (k.timerTurn = true ∨ k.queue.isEmpty = true)) :
    k.timerNext = none :=
  Option.eq_none_iff_forall_ne_some.mpr fun _ hnext => hturn (timerNext_eq_some_iff.mp hnext).2.2

theorem step_of_timerNext {due : Due} {i : σ.Id} {msg : σ.Msg i}
    (hnext : k.timerNext = some (due, ⟨i, msg⟩)) :
    k.step = ({ k with timerTurn := false }).fire i msg due := by
  unfold Kernel.step
  rw [hnext]

theorem step_of_timerNext_none (hnext : k.timerNext = none) :
    k.step = ({ k with timerTurn := true }).run1 := by
  unfold Kernel.step
  rw [hnext]

theorem step_clock (k : Kernel sys) : k.step.kernel.clock_ms = k.clock_ms := by
  unfold Kernel.step
  split
  · exact (fire_kept { k with timerTurn := false } _ _ _).clock
  · exact (run1_kept { k with timerTurn := true }).1

/-- The next turn goes to the side that did not just have one. -/
theorem step_timerTurn (k : Kernel sys) : k.step.kernel.timerTurn = k.timerNext.isNone := by
  unfold Kernel.step
  split
  · rename_i hnext
    rw [hnext]
    exact (fire_kept { k with timerTurn := false } _ _ _).turn
  · rename_i hnext
    rw [hnext]
    exact (run1_kept { k with timerTurn := true }).2

/-- The next step handles `e`, or starts its receiver so that it can be handled. -/
@[expose] def Serves (k : Kernel sys) (e : Envelope σ) : Prop :=
  k.step.events = .deliver e :: k.step.outputs.map .output
    ∨ k.step.events = .start e.dst :: k.step.outputs.map .output

/-- The next step fires a timer due no later than `due`. -/
@[expose] def Fires (k : Kernel sys) (due : Due) : Prop :=
  ∃ i msg first, (msg, first) ∈ (k.cell i).timers ∧ first.deadline_ms ≤ due.deadline_ms
    ∧ k.step.events = .timeout i msg :: k.step.outputs.map .output

/-- On the queue's turn the oldest message is served, whatever is due. -/
theorem serves_of_queueTurn {e : Envelope σ} {rest : List (Envelope σ)}
    (hq : k.queue.toList = e :: rest) (hturn : k.timerTurn = false) : k.Serves e := by
  have hqueue : k.queue.isEmpty = false := by
    cases hempty : k.queue.isEmpty
    · rfl
    · rw [(Fifo.isEmpty_iff _).mp hempty] at hq
      cases hq
  unfold Serves
  rw [step_of_timerNext_none (timerNext_eq_none (by simp [hturn, hqueue]))]
  exact run1_serves hq

/-- The agenda and the cells agree on which timers are pending. -/
structure WellFormed (k : Kernel sys) : Prop where
  /-- Every pending timer is on the agenda. -/
  scheduled : ∀ i msg due, (msg, due) ∈ (k.cell i).timers → k.agenda[due]? = some ⟨i, msg⟩
  /-- Every agenda entry is a pending timer. -/
  pending : ∀ due i msg, k.agenda[due]? = some ⟨i, msg⟩ → (msg, due) ∈ (k.cell i).timers
  /-- No token on the agenda will be issued again. -/
  fresh : ∀ (due : Due) entry, k.agenda[due]? = some entry → due.token < k.nextToken
  /-- An actor has at most one timer for a message. -/
  distinct : ∀ i, ((k.cell i).timers.map (·.1)).Nodup
  /-- An actor that is down has no timers. -/
  idle : ∀ i, (k.cell i).up = false → (k.cell i).timers = []

namespace WellFormed

theorem congr (h : k.WellFormed) (hcell : k'.cell = k.cell) (hagenda : k'.agenda = k.agenda)
    (htoken : k'.nextToken = k.nextToken) : k'.WellFormed where
  scheduled := by rw [hcell, hagenda]; exact h.scheduled
  pending := by rw [hcell, hagenda]; exact h.pending
  fresh := by rw [hagenda, htoken]; exact h.fresh
  distinct := by rw [hcell]; exact h.distinct
  idle := by rw [hcell]; exact h.idle

theorem agenda_image_kernel (k : Kernel sys) (due : Due) :
    k.image.kernel.agenda[due]? = k.agenda[due]? :=
  getElem?_ofList_toList k.agenda due

/-- A kernel restored from its image has the timers on its agenda that the original had. -/
theorem image (h : k.WellFormed) : k.image.kernel.WellFormed where
  scheduled := by simpa only [cell_image_kernel, agenda_image_kernel] using h.scheduled
  pending := by simpa only [cell_image_kernel, agenda_image_kernel] using h.pending
  fresh due entry hd := h.fresh due entry (by rwa [agenda_image_kernel] at hd)
  distinct := by simpa only [cell_image_kernel] using h.distinct
  idle := by simpa only [cell_image_kernel] using h.idle

/-- A `Due` names one timer. -/
theorem same (h : k.WellFormed) {i j : σ.Id} {m : σ.Msg i} {m' : σ.Msg j} {d : Due}
    (hi : (m, d) ∈ (k.cell i).timers) (hj : (m', d) ∈ (k.cell j).timers) :
    (⟨i, m⟩ : (i : σ.Id) × σ.Msg i) = ⟨j, m'⟩ :=
  Option.some.inj ((h.scheduled i m d hi).symm.trans (h.scheduled j m' d hj))

theorem up_of_mem (h : k.WellFormed) {i : σ.Id} {msg : σ.Msg i} {due : Due}
    (hm : (msg, due) ∈ (k.cell i).timers) : (k.cell i).up = true := by
  cases hup : (k.cell i).up
  · rw [h.idle i hup] at hm
    cases hm
  · rfl

/-- Cell `i` drops its timers for the messages in `p`, and their entries leave the agenda. -/
theorem disarm (h : k.WellFormed) {i : σ.Id} {c : Cell sys i} {dues : List Due}
    (p : σ.Msg i → Prop) (hcell : k'.cell = update k.cell i c)
    (hagenda : k'.agenda = (k.unschedule dues).agenda) (htoken : k'.nextToken = k.nextToken)
    (hkept : ∀ m d, (m, d) ∈ c.timers ↔ ¬ p m ∧ (m, d) ∈ (k.cell i).timers)
    (hdues : ∀ d, d ∈ dues ↔ ∃ m, p m ∧ (m, d) ∈ (k.cell i).timers)
    (hdistinct : (c.timers.map (·.1)).Nodup) (hidle : c.up = false → c.timers = []) :
    k'.WellFormed := by
  have hget : ∀ {d entry}, k'.agenda[d]? = some entry ↔ d ∉ dues ∧ k.agenda[d]? = some entry :=
    hagenda ▸ agenda_unschedule
  refine ⟨
    forall_cell (P := fun j c => ∀ m d, (m, d) ∈ c.timers → k'.agenda[d]? = some ⟨j, m⟩) hcell
      (fun m d hm => ?_) (fun j hj m d hm => ?_),
    fun d j => forall_cell (P := fun j c => ∀ m, k'.agenda[d]? = some ⟨j, m⟩ → (m, d) ∈ c.timers)
      hcell (fun m hd => ?_) (fun j _ m hd => h.pending d j m (hget.mp hd).2) j,
    fun d entry hd => htoken ▸ h.fresh d entry (hget.mp hd).2,
    forall_cell (P := fun _ c => (c.timers.map (·.1)).Nodup) hcell hdistinct fun j _ =>
      h.distinct j,
    forall_cell (P := fun _ c => c.up = false → c.timers = []) hcell hidle fun j _ => h.idle j⟩
  · obtain ⟨hp, hm⟩ := (hkept m d).mp hm
    refine hget.mpr ⟨fun hd => ?_, h.scheduled i m d hm⟩
    obtain ⟨m', hp', hm'⟩ := (hdues d).mp hd
    exact hp (eq_of_heq (Sigma.mk.inj (h.same hm hm')).2 ▸ hp')
  · refine hget.mpr ⟨fun hd => ?_, h.scheduled j m d hm⟩
    obtain ⟨m', -, hm'⟩ := (hdues d).mp hd
    exact hj (Sigma.mk.inj (h.same hm hm')).1
  · obtain ⟨hnot, hd⟩ := hget.mp hd
    have hm := h.pending d i m hd
    exact (hkept m d).mpr ⟨fun hp => hnot ((hdues d).mpr ⟨m, hp, hm⟩), hm⟩

/-- Cell `i` gains a timer for `msg` with the next token, and the agenda gains its entry. -/
theorem arm (h : k.WellFormed) {i : σ.Id} {c : Cell sys i} {msg : σ.Msg i} {due : Due}
    (hcell : k'.cell = update k.cell i c) (hagenda : k'.agenda = k.agenda.insert due ⟨i, msg⟩)
    (htoken : k'.nextToken = k.nextToken + 1) (hdue : due.token = k.nextToken)
    (hadded : ∀ m d, (m, d) ∈ c.timers ↔ (m, d) = (msg, due) ∨ (m, d) ∈ (k.cell i).timers)
    (hdistinct : (c.timers.map (·.1)).Nodup) (hup : c.up = true) : k'.WellFormed := by
  have hget : ∀ d, k'.agenda[d]? = if due = d then some ⟨i, msg⟩ else k.agenda[d]? := fun d => by
    rw [hagenda, Std.TreeMap.getElem?_insert]
    simp
  have hold : ∀ {d entry}, k.agenda[d]? = some entry → k'.agenda[d]? = some entry :=
    fun {d entry} hd => by
      rw [hget, ite_eq_right, hd]
      rintro rfl
      have := h.fresh _ _ hd
      omega
  refine ⟨
    forall_cell (P := fun j c => ∀ m d, (m, d) ∈ c.timers → k'.agenda[d]? = some ⟨j, m⟩) hcell
      (fun m d hm => ?_) (fun j _ m d hm => hold (h.scheduled j m d hm)),
    fun d j => forall_cell (P := fun j c => ∀ m, k'.agenda[d]? = some ⟨j, m⟩ → (m, d) ∈ c.timers)
      hcell (fun m hd => ?_) (fun j hj m hd => ?_) j,
    fun d entry hd => ?_,
    forall_cell (P := fun _ c => (c.timers.map (·.1)).Nodup) hcell hdistinct fun j _ =>
      h.distinct j,
    forall_cell (P := fun _ c => c.up = false → c.timers = []) hcell
      (fun hdown => absurd (hdown.symm.trans hup) (by decide)) fun j _ => h.idle j⟩
  · rcases (hadded m d).mp hm with heq | hm
    · cases heq
      simp [hget]
    · exact hold (h.scheduled i m d hm)
  · rw [hget] at hd
    split at hd
    · rename_i heq
      subst heq
      cases eq_of_heq (Sigma.mk.inj (Option.some.inj hd)).2
      exact (hadded _ _).mpr (.inl rfl)
    · exact (hadded _ _).mpr (.inr (h.pending d i m hd))
  · rw [hget] at hd
    split at hd
    · exact absurd (Sigma.mk.inj (Option.some.inj hd)).1.symm hj
    · exact h.pending d j m hd
  · rw [hget] at hd
    rw [htoken]
    split at hd
    · rename_i heq
      subst heq
      omega
    · exact Nat.lt_succ_of_lt (h.fresh d entry hd)

theorem setCell (h : k.WellFormed) {i : σ.Id} {c : Cell sys i}
    (htimers : c.timers = (k.cell i).timers) (hidle : c.up = false → c.timers = []) :
    (k.setCell i c).WellFormed :=
  h.disarm (dues := []) (fun _ => False) (cell_setCell k i c) rfl rfl (by simp [htimers])
    (by simp) (htimers ▸ h.distinct i) hidle

theorem perform (h : k.WellFormed) {i : σ.Id} (hup : (k.cell i).up = true) (eff : Effect σ i) :
    (k.perform i eff).1.WellFormed ∧ ((k.perform i eff).1.cell i).up = true := by
  have hidle : ∀ {timers : List (σ.Msg i × Due)},
      ({ (k.cell i) with timers } : Cell sys i).up = false → timers = [] :=
    fun hdown => absurd (hdown.symm.trans hup) (by decide)
  cases eff with
  | send to msg => exact ⟨h.congr rfl rfl rfl, hup⟩
  | emit out => exact ⟨h, hup⟩
  | stop => exact ⟨h, hup⟩
  | cancel msg =>
    refine ⟨h.disarm (· = msg) (cell_setCell _ i _) rfl rfl (mem_eraseP_fst (h.distinct i) msg)
      (fun d => ?_) (nodup_fst_eraseP (h.distinct i) _) hidle, ?_⟩
    · simpa using mem_find?_fst (h.distinct i) msg d
    · simp only [Kernel.perform, cell_setCell, update_self]
      exact hup
  | after delay_ms msg =>
    let due : Due := ⟨k.clock_ms + delay_ms, k.nextToken⟩
    let olds := ((k.cell i).timers.filter fun t => t.1 = msg).map Prod.snd
    let kept := (k.cell i).timers.filter fun t => ¬ t.1 = msg
    have h₁ : ((k.unschedule olds).setCell i { (k.cell i) with timers := kept }).WellFormed :=
      h.disarm (· = msg) (cell_setCell _ i _) rfl rfl (by simp [kept, and_comm])
        (by simp [olds]) ((h.distinct i).sublist (List.filter_sublist.map _)) hidle
    let armed := if (k.cell i).timers.any (·.1 = msg)
      then (k.cell i).timers.map fun t => if t.1 = msg then (msg, due) else t
      else (k.cell i).timers ++ [(msg, due)]
    refine ⟨h₁.arm (c := { (k.cell i) with timers := armed }) (msg := msg) (due := due) ?_ rfl rfl
      rfl (fun m d => ?_) ?_ hup, ?_⟩
    · simp only [Kernel.perform, cell_setCell, update_update]
      rfl
    · simp only [cell_setCell, update_self, kept, List.mem_filter, decide_eq_true_eq,
        and_comm (a := (m, d) ∈ _)]
      exact mem_arm (k.cell i).timers msg due (m, d)
    · rw [map_fst_arm]
      split
      · exact h.distinct i
      · rename_i hnew
        refine List.nodup_append.mpr
          ⟨h.distinct i, by simp, fun a ha b hb heq => ?_⟩
        rw [List.mem_singleton.mp hb] at heq
        exact hnew (heq ▸ ha)
    · simp only [Kernel.perform, cell_setCell, update_self]
      exact hup

theorem performAll (h : k.WellFormed) {i : σ.Id} (hup : (k.cell i).up = true)
    (effs : List (Effect σ i)) :
    (k.performAll i effs).1.WellFormed ∧ ((k.performAll i effs).1.cell i).up = true := by
  rw [performAll_eq]
  generalize ([] : List σ.Out) = outs
  induction effs generalizing k outs with
  | nil => exact ⟨h, hup⟩
  | cons eff effs ih => exact ih (h.perform hup eff).1 (h.perform hup eff).2 _

theorem down (h : k.WellFormed) (i : σ.Id) : (k.down i).WellFormed :=
  h.disarm (fun _ => True) (cell_setCell _ i _) rfl rfl (by simp) (by simp) (by simp)
    (fun _ => rfl)

theorem settle (h : k.WellFormed) {i : σ.Id} (hup : (k.cell i).up = true)
    (r : sys.State i × List (Effect σ i)) : (k.settle i r).1.WellFormed := by
  have h₀ : (k.setCell i { (k.cell i) with state := r.1 }).WellFormed :=
    h.setCell rfl fun hdown => absurd (hdown.symm.trans hup) (by decide)
  have hall := h₀.performAll (by rw [cell_setCell, update_self]; exact hup) r.2
  rw [settle_eq]
  dsimp only
  split
  · exact hall.1.down i
  · exact hall.1

theorem handle (h : k.WellFormed) {i : σ.Id} (hup : (k.cell i).up = true) (msg : σ.Msg i) :
    (k.handle i msg).1.WellFormed :=
  h.settle hup _

theorem startActor (h : k.WellFormed) (i : σ.Id) : (k.startActor i).1.WellFormed :=
  (h.setCell (c := { (k.cell i) with up := true }) rfl (fun hdown => nomatch hdown)).settle
    (by rw [cell_setCell, update_self]) _

theorem accept (h : k.WellFormed) (x : σ.In) : (k.accept x).kernel.WellFormed :=
  h.congr rfl rfl rfl

theorem advance (h : k.WellFormed) (now_ms : Nat) : (k.advance now_ms).WellFormed :=
  h.congr rfl rfl rfl

theorem run1 (h : k.WellFormed) : k.run1.kernel.WellFormed := by
  rw [run1_eq]
  split
  · exact h
  · rename_i e rest _
    split
    · rename_i hup
      exact handle (k := { k with queue := rest }) (h.congr rfl rfl rfl) hup e.msg
    · exact h.startActor _

theorem fire (h : k.WellFormed) (i : σ.Id) (msg : σ.Msg i) (due : Due) :
    (k.fire i msg due).kernel.WellFormed := by
  rw [fire_eq]
  split
  · rename_i hfire
    simp only [Bool.and_eq_true, List.contains_iff_mem] at hfire
    dsimp only
    apply handle
    · refine h.disarm (· = msg) (cell_setCell _ i _) rfl rfl (mem_eraseP_fst (h.distinct i) msg)
        (fun d => ?_) (nodup_fst_eraseP (h.distinct i) _)
        fun hdown => absurd (hdown.symm.trans hfire.1) (by decide)
      simp only [List.mem_singleton, exists_eq_left]
      exact ⟨fun hd => hd ▸ hfire.2, fun hd => snd_eq_of_nodup_fst (h.distinct i) hd hfire.2⟩
    · rw [cell_setCell, update_self]
      exact hfire.1
  · exact h

theorem turn (h : k.WellFormed) (timerTurn : Bool) : ({ k with timerTurn }).WellFormed :=
  h.congr rfl rfl rfl

theorem step (h : k.WellFormed) : k.step.kernel.WellFormed := by
  unfold Kernel.step
  split
  · exact (h.turn false).fire _ _ _
  · exact (h.turn true).run1

theorem runBatch (h : k.WellFormed) (fuel : Nat) : (k.runBatch fuel).kernel.WellFormed := by
  induction fuel generalizing k with
  | zero => exact h
  | succ fuel ih =>
    rw [runBatch_succ]
    split
    · exact ih h.step
    · exact h

/-- Every operation a shell can perform keeps the agenda and the cells in agreement. -/
theorem apply (h : k.WellFormed) (op : Op σ) : (k.apply op).kernel.WellFormed := by
  cases op with
  | input x => exact h.accept x
  | advance now_ms => exact h.advance now_ms
  | step => exact h.step
  | batch fuel => exact h.runBatch fuel
  | fire i msg due => exact h.fire i msg due
  | snapshot => exact h.image

theorem exec (h : k.WellFormed) (ops : List (Op σ)) : (k.exec ops).kernel.WellFormed := by
  induction ops generalizing k with
  | nil => exact h
  | cons op ops ih =>
    rw [exec_cons]
    exact ih (h.apply op)

end WellFormed

theorem empty_wellFormed : ({} : Kernel sys).WellFormed := by
  have hcell : ∀ i, (({} : Kernel sys).cell i).timers = [] := fun i => by simp [cell]
  have hagenda : ∀ due : Due, ({} : Kernel sys).agenda[due]? = none := fun _ =>
    Std.TreeMap.getElem?_emptyc
  refine ⟨fun i msg due hm => ?_, fun due i msg hd => ?_, fun due entry hd => ?_, fun i => ?_,
    fun i _ => hcell i⟩
  · rw [hcell] at hm
    cases hm
  · rw [hagenda] at hd
    cases hd
  · rw [hagenda] at hd
    cases hd
  · rw [hcell]
    exact List.nodup_nil

omit [Hashable σ.Id] in
theorem boot_wellFormed (sys : System σ) [Hashable σ.Id] : (boot sys).1.WellFormed := by
  have hempty := empty_wellFormed (sys := sys)
  rw [boot_eq]
  generalize ([] : List σ.Out) = outs
  generalize ({} : Kernel sys) = k at hempty
  induction sys.boot generalizing k outs with
  | nil => exact hempty
  | cons i l ih => exact ih _ _ (hempty.startActor i)

omit [Hashable σ.Id] in
/-- Whatever a shell does with a kernel, in any order, its agenda holds exactly the timers its
actors have pending. -/
theorem exec_wellFormed (sys : System σ) [Hashable σ.Id] (ops : List (Op σ)) :
    ((boot sys).1.exec ops).kernel.WellFormed :=
  (boot_wellFormed sys).exec ops

namespace WellFormed

theorem agenda_isEmpty (h : k.WellFormed) :
    k.agenda.isEmpty = true ↔ ∀ i, (k.cell i).timers = [] := by
  constructor
  · intro hempty i
    refine List.eq_nil_iff_forall_not_mem.mpr fun (msg, due) hm => ?_
    exact Std.TreeMap.isEmpty_iff_forall_not_mem.mp hempty due
      (Std.TreeMap.mem_iff_isSome_getElem?.mpr (by rw [h.scheduled i msg due hm]; rfl))
  · intro hnone
    refine Std.TreeMap.isEmpty_iff_forall_not_mem.mpr fun due hmem => ?_
    obtain ⟨⟨i, msg⟩, hd⟩ := Option.isSome_iff_exists.mp
      (Std.TreeMap.mem_iff_isSome_getElem?.mp hmem)
    have hm := h.pending due i msg hd
    rw [hnone i] at hm
    cases hm

/-- The agenda's first key is a pending timer, and none is due before it. -/
theorem earliest (h : k.WellFormed) {first : Due} (hmin : k.agenda.minKey? = some first) :
    (∃ i msg, (msg, first) ∈ (k.cell i).timers) ∧
      ∀ i msg due, (msg, due) ∈ (k.cell i).timers → first.deadline_ms ≤ due.deadline_ms := by
  obtain ⟨hmem, hle⟩ := Std.TreeMap.minKey?_eq_some_iff_mem_and_forall.mp hmin
  constructor
  · obtain ⟨⟨i, msg⟩, hd⟩ := Option.isSome_iff_exists.mp
      (Std.TreeMap.mem_iff_isSome_getElem?.mp hmem)
    exact ⟨i, msg, h.pending first i msg hd⟩
  · intro i msg due hm
    exact Due.deadline_le_of_isLE (hle due
      (Std.TreeMap.mem_iff_isSome_getElem?.mpr (by rw [h.scheduled i msg due hm]; rfl)))

theorem minKey?_of_mem (h : k.WellFormed) {i : σ.Id} {msg : σ.Msg i} {due : Due}
    (hm : (msg, due) ∈ (k.cell i).timers) :
    ∃ first, k.agenda.minKey? = some first ∧ first.deadline_ms ≤ due.deadline_ms := by
  cases hmin : k.agenda.minKey? with
  | none =>
    rw [h.agenda_isEmpty.mp (Std.TreeMap.minKey?_eq_none_iff.mp hmin) i] at hm
    cases hm
  | some first => exact ⟨first, rfl, (h.earliest hmin).2 i msg due hm⟩

theorem fire_events (h : k.WellFormed) {i : σ.Id} {msg : σ.Msg i} {due : Due}
    (hm : (msg, due) ∈ (k.cell i).timers) :
    (k.fire i msg due).events = .timeout i msg :: (k.fire i msg due).outputs.map .output := by
  rw [fire_eq, ite_eq_left (by simp [h.up_of_mem hm, hm])]

theorem timerNext_pending (h : k.WellFormed) {due : Due} {i : σ.Id} {msg : σ.Msg i}
    (hnext : k.timerNext = some (due, ⟨i, msg⟩)) : (msg, due) ∈ (k.cell i).timers :=
  h.pending _ i msg (getElem?_of_minEntry? (timerNext_eq_some_iff.mp hnext).1)

theorem step_events_of_timerNext (h : k.WellFormed) {due : Due} {i : σ.Id} {msg : σ.Msg i}
    (hnext : k.timerNext = some (due, ⟨i, msg⟩)) :
    k.step.events = .timeout i msg :: k.step.outputs.map .output := by
  rw [step_of_timerNext hnext]
  exact (h.turn false).fire_events (h.timerNext_pending hnext)

/-- No lost timer: while a pending timer is due, the shell is told not to sleep. -/
theorem wait_of_due (h : k.WellFormed) {i : σ.Id} {msg : σ.Msg i} {due : Due}
    (hm : (msg, due) ∈ (k.cell i).timers) (hdue : due.deadline_ms ≤ k.clock_ms) :
    k.wait = .none := by
  obtain ⟨first, hmin, hle⟩ := h.minKey?_of_mem hm
  unfold wait
  split
  · rfl
  · rw [hmin]
    exact ite_eq_left (Nat.le_trans hle hdue)

/-- On the timers' turn, or with no message queued, a timer that is due means one due no later
fires. -/
theorem fires_of_timerTurn (h : k.WellFormed) {i : σ.Id} {msg : σ.Msg i} {due : Due}
    (hm : (msg, due) ∈ (k.cell i).timers) (hdue : due.deadline_ms ≤ k.clock_ms)
    (hturn : k.timerTurn = true ∨ k.queue.isEmpty = true) : k.Fires due := by
  obtain ⟨first, hmin, hle⟩ := h.minKey?_of_mem hm
  obtain ⟨j, m, hnext⟩ := timerNext_of_minKey? hmin (Nat.le_trans hle hdue) hturn
  exact ⟨j, m, first, h.timerNext_pending hnext, hle, h.step_events_of_timerNext hnext⟩

/--
Messages are not starved. The oldest message is served by the next step, or by the one after
when a timer went first. The exception is the semantics' own: that timer's handler stopped the
message's receiver, and a stopped actor's mail is lost.
-/
theorem step_of_queued (h : k.WellFormed) {e : Envelope σ} {rest : List (Envelope σ)}
    (hq : k.queue.toList = e :: rest) :
    k.Serves e ∨ k.step.kernel.Serves e
      ∨ (k.step.kernel.cell e.dst).up = false
        ∧ ∃ msg, k.step.events = .timeout e.dst msg :: k.step.outputs.map .output := by
  cases hnext : k.timerNext with
  | none =>
    refine .inl ?_
    unfold Serves
    rw [step_of_timerNext_none hnext]
    exact run1_serves hq
  | some t =>
    obtain ⟨first, i, msg⟩ := t
    have hkept := fire_kept { k with timerTurn := false } i msg first
    rw [← step_of_timerNext hnext] at hkept
    rcases hkept.oldest e rest hq with ⟨rest', hq'⟩ | ⟨rfl, hdown⟩
    · exact .inr (.inl (serves_of_queueTurn hq' hkept.turn))
    · exact .inr (.inr ⟨hdown, msg, h.step_events_of_timerNext hnext⟩)

/--
Timers are not starved. While a pending timer is due, a timer due no later is fired by the next
step, or by the one after when a message went first. The exception: handling that message
disarmed the timer, by cancelling it, arming it again or stopping its actor.
-/
theorem step_of_due (h : k.WellFormed) {i : σ.Id} {msg : σ.Msg i} {due : Due}
    (hm : (msg, due) ∈ (k.cell i).timers) (hdue : due.deadline_ms ≤ k.clock_ms) :
    k.Fires due ∨ k.step.kernel.Fires due ∨ (msg, due) ∉ (k.step.kernel.cell i).timers := by
  by_cases hturn : k.timerTurn = true ∨ k.queue.isEmpty = true
  · exact .inl (h.fires_of_timerTurn hm hdue hturn)
  · have hturn' : k.step.kernel.timerTurn = true := by
      rw [step_timerTurn, timerNext_eq_none hturn]
      rfl
    by_cases hm' : (msg, due) ∈ (k.step.kernel.cell i).timers
    · exact .inr (.inl (h.step.fires_of_timerTurn hm' (by rw [step_clock]; exact hdue)
        (.inl hturn')))
    · exact .inr (.inr hm')

/-- No lost timer: while a pending timer is due, a batch of two steps or more fires a timer,
unless its first step handled a message that disarmed that one. -/
theorem runBatch_of_due (h : k.WellFormed) {i : σ.Id} {msg : σ.Msg i} {due : Due}
    (hm : (msg, due) ∈ (k.cell i).timers) (hdue : due.deadline_ms ≤ k.clock_ms) (fuel : Nat) :
    (∃ j m, .timeout j m ∈ (k.runBatch (fuel + 2)).events)
      ∨ (msg, due) ∉ (k.step.kernel.cell i).timers := by
  by_cases hm' : (msg, due) ∈ (k.step.kernel.cell i).timers
  · have hwait := h.step.wait_of_due hm' (by rw [step_clock]; exact hdue)
    rw [runBatch_succ, ite_eq_left (h.wait_of_due hm hdue), runBatch_succ, ite_eq_left hwait]
    rcases h.step_of_due hm hdue with ⟨j, m, -, -, -, hstep⟩ | ⟨j, m, -, -, -, hstep⟩ | hgone
    · exact .inl ⟨j, m, by simp [hstep]⟩
    · exact .inl ⟨j, m, by simp [hstep]⟩
    · exact absurd hm' hgone
  · exact .inr hm'

theorem wait_eq_none_iff : k.wait = .none ↔
    k.queue.isEmpty = false
      ∨ ∃ first, k.agenda.minKey? = some first ∧ first.deadline_ms ≤ k.clock_ms := by
  unfold wait
  cases k.queue.isEmpty
  · simp
  · cases k.agenda.minKey? with
    | none => simp
    | some first => by_cases hdue : first.deadline_ms ≤ k.clock_ms <;> simp [hdue]

/-- No spin: when the shell is told not to sleep, `step` does something. -/
theorem step_events_ne_nil (h : k.WellFormed) (hwait : k.wait = .none) : k.step.events ≠ [] := by
  cases hnext : k.timerNext with
  | some t =>
    obtain ⟨first, i, msg⟩ := t
    rw [h.step_events_of_timerNext hnext]
    exact List.cons_ne_nil _ _
  | none =>
    have hqueue : k.queue.isEmpty = false := by
      rcases wait_eq_none_iff.mp hwait with hqueue | ⟨first, hmin, hdue⟩
      · exact hqueue
      · refine Bool.not_eq_true _ ▸ fun hempty => ?_
        obtain ⟨i, msg, hsome⟩ := timerNext_of_minKey? hmin hdue (.inr hempty)
        cases hnext.symm.trans hsome
    rw [step_of_timerNext_none hnext]
    intro hnil
    rw [run1_events_eq_nil_iff, abs_net, ← Fifo.isEmpty_iff] at hnil
    exact Bool.noConfusion (hqueue.symm.trans hnil)

/-- Idle means idle: no message is queued and no timer is pending. -/
theorem quiet_iff (h : k.WellFormed) :
    k.quiet true = true ↔ (k.abs).net = [] ∧ ∀ i, (k.abs).timers i = [] := by
  simp [quiet, Fifo.isEmpty_iff, h.agenda_isEmpty]

/-- Sleep is right: the shell is told to sleep until the earliest pending deadline. -/
theorem wait_for_ms (h : k.WellFormed) {ms : Nat} (hwait : k.wait = .for_ms ms) :
    (∀ i msg due, (msg, due) ∈ (k.cell i).timers → k.clock_ms + ms ≤ due.deadline_ms)
      ∧ ∃ i msg due, (msg, due) ∈ (k.cell i).timers ∧ due.deadline_ms = k.clock_ms + ms := by
  unfold wait at hwait
  split at hwait
  · cases hwait
  · split at hwait
    · rename_i first hmin
      split at hwait
      · cases hwait
      · rename_i hdue
        obtain rfl : first.deadline_ms - k.clock_ms = ms := by simpa using hwait
        obtain ⟨⟨i, msg, hfirst⟩, hle⟩ := h.earliest hmin
        exact ⟨fun i msg due hm => by have := hle i msg due hm; omega,
          i, msg, first, hfirst, by omega⟩
    · cases hwait

/-- The shell is told to sleep until an input arrives only when nothing is queued and no timer
is pending. -/
theorem wait_forever (h : k.WellFormed) (hwait : k.wait = .forever) :
    (k.abs).net = [] ∧ ∀ i, (k.abs).timers i = [] := by
  refine h.quiet_iff.mp ?_
  unfold wait at hwait
  split at hwait
  · cases hwait
  · rename_i hqueue
    split at hwait
    · split at hwait <;> cases hwait
    · rename_i hmin
      have hempty : k.queue.isEmpty = true := by simpa using hqueue
      simp [quiet, hempty, Std.TreeMap.minKey?_eq_none_iff.mp hmin]

end WellFormed

end Kernel

end Lanes
