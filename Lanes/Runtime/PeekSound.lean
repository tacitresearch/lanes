/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Runtime.Batch
public import Lanes.Runtime.KernelSound

/-!
What a peek sees and what it leaves, which is what answering a request from the state of an
actor rests on (the proposal `docs/decisions/new-reads.md`).

A peek leaves nothing: a batch with its peeks taken out appends the same journal, hands over the
same outputs and leaves the same kernel (`run_erase_peeks`), so replay, recovery and every
theorem about the journal are those of the requests that entered the system.

Over the shard's whole history, `chain` (the batches one after another, as the shell runs them),
every act is sound where it falls (`chain_sound`): a peek is answered with the state of the
kernel the journal so far describes, once every output that journal produced is handed over. So
a peek never shows a state a crash could take back, and one asked after an output was handed
over is answered with the state of a world the semantics reaches by a run that put out that
output first (`chain_peek_after`).
-/

@[expose] public section

namespace Lanes.Batch

variable {σ : Signature} {sys : System σ} {P : σ.Id → Type} {W : Type}

def Command.isPeek : Command σ P W → Bool
  | .peek .. => true
  | _ => false

variable [Hashable σ.Id]

/-- The batches one after another, as the shell runs them: each from the kernel, the entries
written since the last save and the waiters the one before left. -/
def chain (k : Kernel sys) (written : Nat) (waiting : Array (Bool × W)) :
    List (Config × List (Command σ P W)) → List (Act sys P)
  | [] => []
  | (c, commands) :: rest =>
    let r := run c k written waiting commands
    r.acts.toList ++ chain r.kernel r.written r.waiting rest

/-! A peek leaves nothing. What a scan has appended, handed over and recorded, counting what
it keeps back, is all that the rest of a batch reads of it besides the kernel. -/

private structure Seen (σ : Signature) (W : Type) where
  count : Nat
  ops : List (Kernel.Op σ)
  handed : List σ.Out
  recorded : List (Event σ)
  waiting : Array (Bool × W)
  worked : Bool

private def seen (s : Scan sys P W) : Seen σ W where
  count := s.written + s.entries.size
  ops := journal s.acts.toList ++ Journal.ops s.entries.toList
  handed := handed s.acts.toList ++ s.outputs.toList
  recorded := recorded s.acts.toList ++ s.events.toList
  waiting := s.waiting
  worked := s.worked

omit [Hashable σ.Id] in
private theorem flatMap_put {β : Type} (g : Act sys P → List β) (acts : Array (Act sys P))
    (skip : Bool) (act : Act sys P) (h : skip = true → g act = []) :
    (put acts skip act).toList.flatMap g = acts.toList.flatMap g ++ g act := by
  unfold put
  cases skip
  · simp
  · simp [h rfl]

omit [Hashable σ.Id] in
private theorem empty_of_isEmpty {α : Type} {a : Array α} (h : a.isEmpty = true) : a.toList = [] := by
  simpa using h

private theorem seen_flush (c : Config) (k : Kernel sys) (s : Scan sys P W) :
    (flush c (k, s)).1 = (if due c (seen s).count then k.image.kernel else k)
      ∧ seen (flush c (k, s)).2 = if due c (seen s).count
          then { seen s with count := 0, ops := (seen s).ops ++ [.snapshot] } else seen s := by
  obtain ⟨written, waiting, acts, entries, events, outputs, worked⟩ := s
  have hj := flatMap_put Act.ops (put (put acts entries.isEmpty (.append entries)) events.isEmpty
    (.record events)) outputs.isEmpty (.handOver outputs) (fun _ => rfl)
  have hj2 := flatMap_put Act.ops (put acts entries.isEmpty (.append entries)) events.isEmpty
    (.record events) (fun _ => rfl)
  have hj1 := flatMap_put Act.ops acts entries.isEmpty (.append entries)
    (fun h => by simp [Act.ops, empty_of_isEmpty h, Journal.ops])
  have hh := flatMap_put Act.outputs (put (put acts entries.isEmpty (.append entries))
    events.isEmpty (.record events)) outputs.isEmpty (.handOver outputs)
    (fun h => by simp [Act.outputs, empty_of_isEmpty h])
  have hh2 := flatMap_put Act.outputs (put acts entries.isEmpty (.append entries)) events.isEmpty
    (.record events) (fun _ => rfl)
  have hh1 := flatMap_put Act.outputs acts entries.isEmpty (.append entries) (fun _ => rfl)
  have hr := flatMap_put Act.events (put (put acts entries.isEmpty (.append entries))
    events.isEmpty (.record events)) outputs.isEmpty (.handOver outputs) (fun _ => rfl)
  have hr2 := flatMap_put Act.events (put acts entries.isEmpty (.append entries)) events.isEmpty
    (.record events) (fun h => by simp [Act.events, empty_of_isEmpty h])
  have hr1 := flatMap_put Act.events acts entries.isEmpty (.append entries) (fun _ => rfl)
  simp only [Act.ops, Act.outputs, Act.events, List.append_nil] at hj hj2 hj1 hh hh2 hh1 hr hr2 hr1
  by_cases hd : due c (written + entries.size) = true
  · simp only [flush, seen, hd, ↓reduceIte, journal, handed, recorded, Array.toList_push,
      List.flatMap_append, hj, hj2, hj1, hh, hh2, hh1, hr, hr2, hr1, Act.ops, Act.outputs,
      Act.events, List.flatMap_cons, List.flatMap_nil, List.append_nil, Array.toList_empty,
      Array.size_empty, Nat.add_zero, Journal.ops, List.filterMap_nil, true_and]
  · simp only [Bool.not_eq_true] at hd
    simp only [flush, seen, hd, Bool.false_eq_true, ↓reduceIte, journal, handed, recorded, hj, hj2, hj1, hh, hh2, hh1, hr, hr2,
      hr1, Array.toList_empty, List.append_nil, Array.size_empty, Nat.add_zero, Journal.ops,
      List.filterMap_nil, true_and]

private theorem seen_workWith (turn : Kernel sys → Journal.Turn sys) (k : Kernel sys)
    (s : Scan sys P W) :
    (workWith turn (k, s)).1 = (turn k).kernel
      ∧ seen (workWith turn (k, s)).2 =
        { count := (seen s).count + (turn k).entries.length
          ops := (seen s).ops ++ Journal.ops (turn k).entries
          handed := (seen s).handed ++ (turn k).outputs
          recorded := (seen s).recorded ++ (turn k).events
          waiting := (seen s).waiting, worked := true } := by
  obtain ⟨written, waiting, acts, entries, events, outputs, worked⟩ := s
  have hsize : (entries ++ (turn k).entries).size = entries.size + (turn k).entries.length := by
    rw [← Array.length_toList, Array.toList_appendList, List.length_append, Array.length_toList]
  simp only [workWith, seen, hsize, Array.toList_appendList, Journal.ops, List.filterMap_append,
    List.append_assoc, Nat.add_assoc, true_and]

/-- Two scans that agree in all a batch reads of them, the first's count not due for a save. -/
private structure Twin (c : Config) (a b : Kernel sys × Scan sys P W) : Prop where
  kernel : a.1 = b.1
  same : seen a.2 = seen b.2
  quiet : due c (seen a.2).count = false

private theorem due_zero (c : Config) : due c 0 = false := by
  unfold due
  cases c.snapshotEvery <;> simp

private theorem alike_flush (c : Config) {ka kb : Kernel sys} {sa sb : Scan sys P W}
    (hk : ka = kb) (hs : seen sa = seen sb) :
    (flush c (ka, sa)).1 = (flush c (kb, sb)).1 ∧ seen (flush c (ka, sa)).2 = seen (flush c (kb, sb)).2 := by
  obtain ⟨ha1, ha2⟩ := seen_flush c ka sa
  obtain ⟨hb1, hb2⟩ := seen_flush c kb sb
  rw [ha1, ha2, hb1, hb2, hk, hs]
  exact ⟨rfl, rfl⟩

/-- After a flush no save is due. -/
private theorem quiet_flush (c : Config) (k : Kernel sys) (s : Scan sys P W) :
    due c (seen (flush c (k, s)).2).count = false := by
  rw [(seen_flush c k s).2]
  split
  · exact due_zero c
  · next h => simpa using h

private theorem twin_flush (c : Config) {a b : Kernel sys × Scan sys P W} (h : Twin c a b) :
    Twin c (flush c a) (flush c b) :=
  let ⟨hk, hs⟩ := alike_flush c (sa := a.2) (sb := b.2) h.kernel h.same
  ⟨hk, hs, quiet_flush c a.1 a.2⟩

/-- A batch's turn for its inputs, and the save if one is due, from twins. -/
private theorem twin_work (c : Config) (turn : Kernel sys → Journal.Turn sys)
    {a b : Kernel sys × Scan sys P W} (h : Twin c a b) :
    Twin c
      (match workWith turn a with
        | (k, s) => if due c (s.written + s.entries.size) then flush c (k, s) else (k, s))
      (match workWith turn b with
        | (k, s) => if due c (s.written + s.entries.size) then flush c (k, s) else (k, s)) := by
  obtain ⟨ka, sa⟩ := a
  obtain ⟨kb, sb⟩ := b
  obtain ⟨hk, hs, -⟩ := h
  simp only at hk hs
  subst hk
  obtain ⟨wa1, wa2⟩ := seen_workWith turn ka sa
  obtain ⟨wb1, wb2⟩ := seen_workWith turn ka sb
  rw [hs] at wa2
  generalize workWith turn (ka, sa) = wa at wa1 wa2
  generalize workWith turn (ka, sb) = wb at wb1 wb2
  obtain ⟨ka', sa'⟩ := wa
  obtain ⟨kb', sb'⟩ := wb
  simp only at wa1 wa2 wb1 wb2 ⊢
  have hseen : seen sa' = seen sb' := wa2.trans wb2.symm
  have hcount : sa'.written + sa'.entries.size = sb'.written + sb'.entries.size :=
    congrArg Seen.count hseen
  rw [← hcount]
  have hk' : ka' = kb' := wa1.trans wb1.symm
  split
  · exact let ⟨h1, h2⟩ := alike_flush c hk' hseen; ⟨h1, h2, quiet_flush c ka' sa'⟩
  · next hdue => exact ⟨hk', hseen, by simp only [seen]; simpa using hdue⟩

omit [Hashable σ.Id] in
private theorem seen_waiting (s : Scan sys P W) (w : Array (Bool × W)) :
    seen { s with waiting := w } = { seen s with waiting := w } := rfl

omit [Hashable σ.Id] in
private theorem seen_answer (s : Scan sys P W) (i : σ.Id) (reply : P i) (state : sys.State i) :
    seen { s with acts := s.acts.push (.answer i reply state) } = seen s := by
  simp [seen, journal, handed, recorded, Act.ops, Act.outputs, Act.events]

private theorem twin_scan (c : Config) {a b : Kernel sys × Scan sys P W} (h : Twin c a b)
    (command : Command σ P W) (hc : command.isPeek = false) :
    Twin c (scan c a command) (scan c b command) := by
  cases command with
  | input x => exact twin_work c (fun k => Journal.turn k c.now_ms (some x) c.fuel) h
  | inputs xs =>
    exact twin_work c (fun k => Journal.turnAll k c.now_ms xs (c.fuel * max 1 xs.length) c.workers) h
  | idle timers waiter =>
    obtain ⟨hk, hs, hq⟩ := twin_flush c h
    simp only [scan]
    generalize flush c a = fa at hk hs hq
    generalize flush c b = fb at hk hs hq
    obtain ⟨ka, sa⟩ := fa
    obtain ⟨kb, sb⟩ := fb
    simp only [seen, Seen.mk.injEq] at hk hs hq ⊢
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hs
    exact ⟨hk, by simp only [seen, h1, h2, h3, h4, h5, h6], hq⟩
  | peek i reply => simp [Command.isPeek] at hc

/-- A peek where the other batch has none leaves the two alike. -/
private theorem twin_peek (c : Config) {a b : Kernel sys × Scan sys P W} (h : Twin c a b)
    (i : σ.Id) (reply : P i) : Twin c (scan c a (.peek i reply)) b := by
  obtain ⟨ka, sa⟩ := a
  obtain ⟨hk, hs, hq⟩ := h
  obtain ⟨h1, h2⟩ := seen_flush c ka sa
  simp only at hq hk hs
  rw [hq] at h1 h2
  simp only [Bool.false_eq_true, ↓reduceIte] at h1 h2
  simp only [scan]
  generalize flush c (ka, sa) = f at h1 h2
  obtain ⟨k, s⟩ := f
  simp only at h1 h2
  exact ⟨h1.trans hk, by rw [seen_answer, h2, hs], by simp only [seen_answer, h2]; exact hq⟩

private theorem twin_foldl (c : Config) (commands : List (Command σ P W)) :
    ∀ {a b : Kernel sys × Scan sys P W}, Twin c a b →
      Twin c (commands.foldl (scan c) a) ((commands.filter (!·.isPeek)).foldl (scan c) b) := by
  induction commands with
  | nil => exact id
  | cons command rest ih =>
    intro a b h
    cases hc : command.isPeek
    · rw [List.filter_cons_of_pos (by simp [hc]), List.foldl_cons, List.foldl_cons]
      exact ih (twin_scan c h command hc)
    · rw [List.filter_cons_of_neg (by simp [hc]), List.foldl_cons]
      cases command with
      | peek i reply => exact ih (twin_peek c h i reply)
      | _ => simp [Command.isPeek] at hc

private theorem flush_empty (c : Config) (k : Kernel sys) (s : Scan sys P W) :
    (flush c (k, s)).2.entries = #[] ∧ (flush c (k, s)).2.events = #[]
      ∧ (flush c (k, s)).2.outputs = #[] := by
  obtain ⟨_, _, _, _, _, _, _⟩ := s
  simp only [flush]; split <;> exact ⟨rfl, rfl, rfl⟩

/-- A peek leaves nothing: a batch without its peeks appends the same journal, hands over and
records the same, and leaves the same kernel, count and waiters. So the journal, and what replay
and recovery make of it, is that of the inputs alone, whatever was peeked and when. The batch
must not start with a save due, which the shell never does: every batch ends with none due. -/
theorem run_erase_peeks (c : Config) (k : Kernel sys) (written : Nat) (waiting : Array (Bool × W))
    (commands : List (Command σ P W)) (h : due c written = false) :
    let r := run c k written waiting commands
    let r' := run c k written waiting (commands.filter (!·.isPeek))
    r.kernel = r'.kernel ∧ journal r.acts.toList = journal r'.acts.toList
      ∧ handed r.acts.toList = handed r'.acts.toList
      ∧ recorded r.acts.toList = recorded r'.acts.toList
      ∧ r.written = r'.written ∧ r.resolved = r'.resolved ∧ r.waiting = r'.waiting := by
  have start : Twin c (k, ({ written, waiting } : Scan sys P W)) (k, { written, waiting }) :=
    ⟨rfl, rfl, by simpa [seen] using h⟩
  obtain ⟨hk, hs, -⟩ := twin_foldl c commands start
  simp only [run, finish]
  generalize commands.foldl (scan c) (k, { written, waiting }) = a at hk hs
  generalize (commands.filter (!·.isPeek)).foldl (scan c) (k, { written, waiting }) = b at hk hs
  obtain ⟨ka, sa⟩ := a
  obtain ⟨kb, sb⟩ := b
  simp only at hk hs
  subst hk
  have hworked : sa.worked = sb.worked := congrArg Seen.worked hs
  have pre : (if sa.worked then (ka, sa) else work c none (ka, sa)).1
        = (if sb.worked then (ka, sb) else work c none (ka, sb)).1
      ∧ seen (if sa.worked then (ka, sa) else work c none (ka, sa)).2
        = seen (if sb.worked then (ka, sb) else work c none (ka, sb)).2 := by
    rw [hworked]
    cases sb.worked
    · obtain ⟨a1, a2⟩ := seen_workWith (fun k => Journal.turn k c.now_ms none c.fuel) ka sa
      obtain ⟨b1, b2⟩ := seen_workWith (fun k => Journal.turn k c.now_ms none c.fuel) ka sb
      simp only [Bool.false_eq_true, ↓reduceIte, work]
      exact ⟨a1.trans b1.symm, by rw [a2, b2, hs]⟩
    · exact ⟨rfl, hs⟩
  obtain ⟨p1, p2⟩ := pre
  generalize (if sa.worked then (ka, sa) else work c none (ka, sa)) = x at p1 p2
  generalize (if sb.worked then (ka, sb) else work c none (ka, sb)) = y at p1 p2
  obtain ⟨kx, sx⟩ := x
  obtain ⟨ky, sy⟩ := y
  simp only at p1 p2
  obtain ⟨f1, f2⟩ := alike_flush c p1 p2
  obtain ⟨ex, vx, ox⟩ := flush_empty c kx sx
  obtain ⟨ey, vy, oy⟩ := flush_empty c ky sy
  generalize flush c (kx, sx) = fx at f1 f2 ex vx ox
  generalize flush c (ky, sy) = fy at f1 f2 ey vy oy
  obtain ⟨k1, s1⟩ := fx
  obtain ⟨k2, s2⟩ := fy
  simp only at f1 f2 ex vx ox ey vy oy ⊢
  subst f1
  have := congrArg Seen.ops f2
  have := congrArg Seen.handed f2
  have := congrArg Seen.recorded f2
  have := congrArg Seen.count f2
  have hw : s1.waiting = s2.waiting := congrArg Seen.waiting f2
  simp_all [seen, Journal.ops]

/-! Over the whole history. -/

theorem Sound.of_append {k : Kernel sys} {xs ys : List (Act sys P)} (h : Sound k (xs ++ ys)) :
    Sound k xs :=
  fun before act after hx => h before act (after ++ ys) (by rw [hx]; simp)

/-- What is sound after `before` from the kernel `xs` leads to is sound after `xs ++ before`
from where `xs` started, when everything `xs` produced has been handed over and recorded. -/
private theorem Act.Sound.shift {k : Kernel sys} {xs before : List (Act sys P)} {act : Act sys P}
    (hh : handed xs = (k.exec (journal xs)).outputs)
    (hr : recorded xs = (k.exec (journal xs)).events)
    (ha : act.Sound (k.exec (journal xs)).kernel before) : act.Sound k (xs ++ before) := by
  have hj : journal (xs ++ before) = journal xs ++ journal before := List.flatMap_append ..
  have hh' : handed (xs ++ before) = handed xs ++ handed before := List.flatMap_append ..
  have hr' : recorded (xs ++ before) = recorded xs ++ recorded before := List.flatMap_append ..
  cases act with
  | append _ => trivial
  | record events =>
    simp only [Act.Sound] at ha ⊢
    rw [hj, hr', Kernel.exec_append, List.append_assoc, ha, hr]
  | handOver outputs =>
    simp only [Act.Sound] at ha ⊢
    rw [hj, hh', Kernel.exec_append, List.append_assoc, ha, hh]
  | save image =>
    simp only [Act.Sound] at ha ⊢
    rw [hj, hh', Kernel.exec_append, ha.2, hh]
    exact ⟨ha.1, rfl⟩
  | answer i reply state =>
    simp only [Act.Sound] at ha ⊢
    rw [hj, hh', Kernel.exec_append, ha.2, hh]
    exact ⟨ha.1, rfl⟩

private theorem Sound.shift {k : Kernel sys} {xs ys : List (Act sys P)} (hx : Sound k xs)
    (hh : handed xs = (k.exec (journal xs)).outputs)
    (hr : recorded xs = (k.exec (journal xs)).events)
    (hy : Sound (k.exec (journal xs)).kernel ys) : Sound k (xs ++ ys) := by
  intro before act after h
  rcases List.append_eq_append_iff.mp h with ⟨rest, rfl, hys⟩ | ⟨rest, rfl, hrest⟩
  · exact Act.Sound.shift hh hr (hy rest act after hys)
  · cases rest with
    | nil =>
      simp only [List.nil_append] at hrest
      have := Act.Sound.shift hh hr (hy [] act after hrest.symm)
      simpa using this
    | cons d rest =>
      simp only [List.cons_append, List.cons.injEq] at hrest
      obtain ⟨rfl, -⟩ := hrest
      exact hx before act rest rfl

/-- Every act of the shard's history is sound where it falls, from the kernel it started from:
each batch's acts are, from the kernel the batches before it left, and those batches have
handed over and recorded everything they produced. -/
theorem chain_sound (k : Kernel sys) (written : Nat) (waiting : Array (Bool × W))
    (batches : List (Config × List (Command σ P W))) :
    Sound k (chain k written waiting batches)
      ∧ handed (chain k written waiting batches)
        = (k.exec (journal (chain k written waiting batches))).outputs
      ∧ recorded (chain k written waiting batches)
        = (k.exec (journal (chain k written waiting batches))).events := by
  induction batches generalizing k written waiting with
  | nil => exact ⟨fun before act after h => by simp [chain] at h, rfl, rfl⟩
  | cons batch rest ih =>
    obtain ⟨c, commands⟩ := batch
    simp only [chain]
    obtain ⟨hh, hr⟩ := run_handed c k written waiting commands
    have hx := run_sound c k written waiting commands
    have hk := run_kernel c k written waiting commands
    obtain ⟨ys, yh, yr⟩ := ih (run c k written waiting commands).kernel
      (run c k written waiting commands).written (run c k written waiting commands).waiting
    generalize chain (run c k written waiting commands).kernel
      (run c k written waiting commands).written (run c k written waiting commands).waiting rest
      = zs at ys yh yr
    rw [hk] at ys yh yr
    generalize (run c k written waiting commands).acts.toList = xs at hh hr hx ys yh yr
    have hj : journal (xs ++ zs) = journal xs ++ journal zs := List.flatMap_append ..
    refine ⟨Sound.shift hx hh hr ys, ?_, ?_⟩
    · rw [hj, Kernel.exec_append, ← yh, ← hh]; exact List.flatMap_append ..
    · rw [hj, Kernel.exec_append, ← yr, ← hr]; exact List.flatMap_append ..

/-- A peek anywhere in the shard's history is answered with the state of the kernel the journal
so far describes, once every output that journal produced is handed over. -/
theorem chain_peek {k : Kernel sys} {written : Nat} {waiting : Array (Bool × W)}
    {batches : List (Config × List (Command σ P W))} {before after : List (Act sys P)} {i : σ.Id}
    {reply : P i} {state : sys.State i}
    (h : chain k written waiting batches = before ++ .answer i reply state :: after) :
    state = ((k.exec (journal before)).kernel.cell i).state
      ∧ handed before = (k.exec (journal before)).outputs :=
  (chain_sound k written waiting batches).1 before _ after h

private theorem handed_prefix_reverse {k : Kernel sys} (rs : List (Act sys P))
    (h : Sound k rs.reverse) : handed rs.reverse <+: (k.exec (journal rs.reverse)).outputs := by
  induction rs with
  | nil => exact List.nil_prefix
  | cons act rs ih =>
    rw [List.reverse_cons] at h ⊢
    have hxs := ih (Sound.of_append h)
    have ha := h rs.reverse act [] rfl
    have hj : journal (rs.reverse ++ [act]) = journal rs.reverse ++ act.ops := by simp [journal]
    have hh : handed (rs.reverse ++ [act]) = handed rs.reverse ++ act.outputs := by simp [handed]
    rw [hj, hh, Kernel.exec_append]
    cases act with
    | handOver outputs =>
      simp only [Act.Sound] at ha
      simp only [Act.ops, Act.outputs, Kernel.exec, List.append_nil, ha]
      exact List.prefix_refl _
    | _ =>
      simp only [Act.outputs, List.append_nil]
      exact hxs.trans (List.prefix_append _ _)

/-- What has been handed over is a prefix of what the journal so far produced. -/
theorem Sound.handed_prefix {k : Kernel sys} {acts : List (Act sys P)} (h : Sound k acts) :
    handed acts <+: (k.exec (journal acts)).outputs := by
  have := handed_prefix_reverse acts.reverse (by rwa [List.reverse_reverse])
  rwa [List.reverse_reverse] at this

/-- A peek asked after an output was handed over is answered with the state of an actor in a
world the semantics reaches, up to actors at rest released (`SysState.Leads`), by a run that put
out that output first. The shard may have started from any journal (`past`), as recovery
gives (`Journal.recover_kernel`). With a request's response for `o`, this is a read issued after
a write's response seeing that write, and not only that write's effect on one actor: every
event the run had before it. -/
theorem chain_peek_after (past : List (Kernel.Op σ)) (written : Nat) (waiting : Array (Bool × W))
    (batches : List (Config × List (Command σ P W))) {shown before after : List (Act sys P)}
    {i : σ.Id} {reply : P i} {state : sys.State i} {o : σ.Out}
    (h : chain ((Kernel.boot sys).1.exec past).kernel written waiting batches
      = before ++ .answer i reply state :: after)
    (hshown : shown <+: before) (ho : o ∈ handed shown) :
    ∃ evs more c, (SysState.init sys Kernel.env).Leads Kernel.env
        ((Kernel.boot sys).2.map .output ++ evs ++ more) c
      ∧ o ∈ Event.outputs evs ∧ state = c.state i := by
  obtain ⟨hstate, -⟩ := chain_peek h
  obtain ⟨tail, rfl⟩ := hshown
  have hsound : Sound ((Kernel.boot sys).1.exec past).kernel shown :=
    Sound.of_append (Sound.of_append (xs := shown ++ tail)
      (h ▸ (chain_sound _ written waiting batches).1))
  have hj : journal (shown ++ tail) = journal shown ++ journal tail := List.flatMap_append ..
  have hreach := (Kernel.exec_reachable sys
    (past ++ journal shown ++ journal tail)).1
  rw [Kernel.exec_append, Kernel.exec_append] at hreach
  refine ⟨(((Kernel.boot sys).1.exec past).events
      ++ (((Kernel.boot sys).1.exec past).kernel.exec (journal shown)).events), _, _,
    by simpa only [List.append_assoc] using hreach, ?_, ?_⟩
  · rw [Event.outputs_append, Kernel.exec_outputs (((Kernel.boot sys).1.exec past).kernel)]
    apply List.mem_append_right
    exact hsound.handed_prefix.subset ho
  · rw [hstate, hj, Kernel.exec_append]
    rfl

end Lanes.Batch
