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
`Kernel.WellFormed`: a timer that is due is fired and not slept through (`wait_of_due`,
`step_of_due`), a kernel that says there is work does some (`step_events_ne_nil`), idle means
nothing queued and nothing pending (`quiet_iff`), and the shell sleeps until the earliest
deadline, no longer and no shorter (`wait_for_ms`).
-/

public section

namespace Lanes

private theorem update_update {ι : Type} [DecidableEq ι] {β : ι → Type} (f : (i : ι) → β i)
    (i : ι) (a b : β i) : update (update f i a) i b = update f i b := by
  funext j
  by_cases h : j = i
  · subst h; simp
  · simp [h]

/-! `Std` proves nothing about `minEntry?`, so this looks inside the tree, once. -/

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

theorem step (h : k.WellFormed) : k.step.kernel.WellFormed := by
  unfold Kernel.step
  split
  · split
    · exact h.fire _ _ _
    · exact h.run1
  · exact h.run1

/-- Every operation a shell can perform keeps the agenda and the cells in agreement. -/
theorem apply (h : k.WellFormed) (op : Op σ) : (k.apply op).kernel.WellFormed := by
  cases op with
  | input x => exact h.accept x
  | advance now_ms => exact h.advance now_ms
  | step => exact h.step
  | fire i msg due => exact h.fire i msg due

theorem exec (h : k.WellFormed) (ops : List (Op σ)) : (k.exec ops).kernel.WellFormed := by
  induction ops generalizing k with
  | nil => exact h
  | cons op ops ih =>
    rw [exec_cons]
    exact ih (h.apply op)

theorem runBatch (h : k.WellFormed) (fuel : Nat) : (k.runBatch fuel).kernel.WellFormed := by
  induction fuel generalizing k with
  | zero => exact h
  | succ fuel ih =>
    rw [runBatch_succ]
    split
    · exact ih h.step
    · exact h

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

/-- When the agenda's first timer is due, `step` fires it. -/
theorem step_of_minKey? (h : k.WellFormed) {first : Due} (hmin : k.agenda.minKey? = some first)
    (hdue : first.deadline_ms ≤ k.clock_ms) :
    ∃ i msg, (msg, first) ∈ (k.cell i).timers
      ∧ k.step.events = .timeout i msg :: k.step.outputs.map .output := by
  rw [minKey?_eq_map_minEntry?] at hmin
  obtain ⟨⟨due, i, msg⟩, hentry, rfl⟩ := Option.map_eq_some_iff.mp hmin
  have hm := h.pending _ i msg (getElem?_of_minEntry? hentry)
  refine ⟨i, msg, hm, ?_⟩
  unfold Kernel.step
  rw [hentry]
  dsimp only
  rw [ite_eq_left hdue, fire_eq, ite_eq_left (by simp [h.up_of_mem hm, hm])]

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

/-- No lost timer: while a pending timer is due, `step` fires a timer, one due no later. -/
theorem step_of_due (h : k.WellFormed) {i : σ.Id} {msg : σ.Msg i} {due : Due}
    (hm : (msg, due) ∈ (k.cell i).timers) (hdue : due.deadline_ms ≤ k.clock_ms) :
    ∃ j m first, (m, first) ∈ (k.cell j).timers ∧ first.deadline_ms ≤ due.deadline_ms
      ∧ k.step.events = .timeout j m :: k.step.outputs.map .output := by
  obtain ⟨first, hmin, hle⟩ := h.minKey?_of_mem hm
  obtain ⟨j, m, hfirst, hstep⟩ := h.step_of_minKey? hmin (Nat.le_trans hle hdue)
  exact ⟨j, m, first, hfirst, hle, hstep⟩

/-- No lost timer: while a pending timer is due, a batch of work begins by firing a timer. -/
theorem runBatch_of_due (h : k.WellFormed) {i : σ.Id} {msg : σ.Msg i} {due : Due}
    (hm : (msg, due) ∈ (k.cell i).timers) (hdue : due.deadline_ms ≤ k.clock_ms) (fuel : Nat) :
    ∃ j m later, (k.runBatch (fuel + 1)).events = .timeout j m :: later := by
  obtain ⟨j, m, -, -, -, hstep⟩ := h.step_of_due hm hdue
  rw [runBatch_succ, ite_eq_left (h.wait_of_due hm hdue)]
  exact ⟨j, m, _, by rw [hstep]; rfl⟩

/-- No spin: when the shell is told not to sleep, `step` does something. -/
theorem step_events_ne_nil (h : k.WellFormed) (hwait : k.wait = .none) : k.step.events ≠ [] := by
  have hrun1 : k.queue.isEmpty = false → k.run1.events ≠ [] := fun hqueue hnil => by
    rw [run1_events_eq_nil_iff, abs_net, ← Fifo.isEmpty_iff, hqueue] at hnil
    cases hnil
  cases hmin : k.agenda.minKey? with
  | none =>
    have hentry : k.agenda.minEntry? = none := by
      simpa [minKey?_eq_map_minEntry?] using hmin
    have hqueue : k.queue.isEmpty = false := by
      cases hq : k.queue.isEmpty
      · rfl
      · simp [wait, hq, hmin] at hwait
    unfold Kernel.step
    rw [hentry]
    exact hrun1 hqueue
  | some first =>
    by_cases hdue : first.deadline_ms ≤ k.clock_ms
    · obtain ⟨i, msg, -, hstep⟩ := h.step_of_minKey? hmin hdue
      rw [hstep]
      exact List.cons_ne_nil _ _
    · have hqueue : k.queue.isEmpty = false := by
        cases hq : k.queue.isEmpty
        · rfl
        · simp [wait, hq, hmin, hdue] at hwait
      rw [minKey?_eq_map_minEntry?] at hmin
      obtain ⟨⟨due, i, msg⟩, hentry, rfl⟩ := Option.map_eq_some_iff.mp hmin
      unfold Kernel.step
      rw [hentry]
      dsimp only
      rw [ite_eq_right hdue]
      exact hrun1 hqueue

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
