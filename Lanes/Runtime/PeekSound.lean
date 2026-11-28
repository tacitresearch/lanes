/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Runtime.Batch
public import Lanes.Runtime.KernelSound

/-!
What a peek sees over the shard's whole history, which answering a read from the state rests on
(`docs/decisions/new-reads-from-state.md`).

`chain` is the batches one after another, as the shell runs them. Every act of it is sound where
it falls (`chain_sound`): a peek is answered with the states of the kernel the requests so far
lead to, once every output they produced is handed over (`chain_peek`). So a read is
linearizable at the boundary where it is answered: it sees every request before it and none
after, and one asked after a write's response was handed over sees a world the semantics reaches
by a run that put that response out first (`chain_peek_after`).
-/

@[expose] public section

namespace Lanes.Batch

variable {σ : Signature} {sys : System σ} {P : List σ.Id → Type} {W : Type} [Hashable σ.Id]

/-- The batches one after another, as the shell runs them: each from the kernel and the waiters
the one before left. -/
def chain (k : Kernel sys) (waiting : Array (Bool × W)) :
    List (Config × List (Command σ P W)) → List (Act sys P)
  | [] => []
  | (c, commands) :: rest =>
    let r := run c k waiting commands
    r.acts.toList ++ chain r.kernel r.waiting rest

theorem Sound.of_append {k : Kernel sys} {xs ys : List (Act sys P)} (h : Sound k (xs ++ ys)) :
    Sound k xs :=
  fun before act after hx => h before act (after ++ ys) (by rw [hx]; simp)

/-- What is sound after `before` from the kernel `xs` leads to is sound after `xs ++ before`
from where `xs` started, when everything `xs` produced has been handed over and recorded. -/
private theorem Act.Sound.shift {k : Kernel sys} {xs before : List (Act sys P)} {act : Act sys P}
    (hh : handed xs = (k.exec (requests xs)).outputs)
    (hr : recorded xs = (k.exec (requests xs)).events)
    (ha : act.Sound (k.exec (requests xs)).kernel before) : act.Sound k (xs ++ before) := by
  have hj : requests (xs ++ before) = requests xs ++ requests before := List.flatMap_append ..
  have hh' : handed (xs ++ before) = handed xs ++ handed before := List.flatMap_append ..
  have hr' : recorded (xs ++ before) = recorded xs ++ recorded before := List.flatMap_append ..
  cases act with
  | work _ => trivial
  | record events =>
    simp only [Act.Sound] at ha ⊢
    rw [hj, hr', Kernel.exec_append, List.append_assoc, ha, hr]
  | handOver outputs =>
    simp only [Act.Sound] at ha ⊢
    rw [hj, hh', Kernel.exec_append, List.append_assoc, ha, hh]
  | answer ids reply peek =>
    simp only [Act.Sound] at ha ⊢
    rw [hj, hh', Kernel.exec_append, ha.2, hh]
    exact ⟨ha.1, rfl⟩

private theorem Sound.shift {k : Kernel sys} {xs ys : List (Act sys P)} (hx : Sound k xs)
    (hh : handed xs = (k.exec (requests xs)).outputs)
    (hr : recorded xs = (k.exec (requests xs)).events)
    (hy : Sound (k.exec (requests xs)).kernel ys) : Sound k (xs ++ ys) := by
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
theorem chain_sound (k : Kernel sys) (waiting : Array (Bool × W))
    (batches : List (Config × List (Command σ P W))) :
    Sound k (chain k waiting batches)
      ∧ handed (chain k waiting batches)
        = (k.exec (requests (chain k waiting batches))).outputs
      ∧ recorded (chain k waiting batches)
        = (k.exec (requests (chain k waiting batches))).events := by
  induction batches generalizing k waiting with
  | nil => exact ⟨fun before act after h => by simp [chain] at h, rfl, rfl⟩
  | cons batch rest ih =>
    obtain ⟨c, commands⟩ := batch
    simp only [chain]
    obtain ⟨hh, hr⟩ := run_handed c k waiting commands
    have hx := run_sound c k waiting commands
    have hk := run_kernel c k waiting commands
    obtain ⟨ys, yh, yr⟩ := ih (run c k waiting commands).kernel
      (run c k waiting commands).waiting
    generalize chain (run c k waiting commands).kernel
      (run c k waiting commands).waiting rest
      = zs at ys yh yr
    rw [hk] at ys yh yr
    generalize (run c k waiting commands).acts.toList = xs at hh hr hx ys yh yr
    have hj : requests (xs ++ zs) = requests xs ++ requests zs := List.flatMap_append ..
    refine ⟨Sound.shift hx hh hr ys, ?_, ?_⟩
    · rw [hj, Kernel.exec_append, ← yh, ← hh]; exact List.flatMap_append ..
    · rw [hj, Kernel.exec_append, ← yr, ← hr]; exact List.flatMap_append ..

/-- A peek anywhere in the shard's history is answered with the states of the kernel the requests
so far describes, once every output that requests produced is handed over. -/
theorem chain_peek {k : Kernel sys} {waiting : Array (Bool × W)}
    {batches : List (Config × List (Command σ P W))} {before after : List (Act sys P)}
    {ids : List σ.Id} {reply : P ids} {peek : Peek sys ids}
    (h : chain k waiting batches = before ++ .answer ids reply peek :: after) :
    peek = Peek.of (k.exec (requests before)).kernel ids peek.every
      ∧ handed before = (k.exec (requests before)).outputs :=
  (chain_sound k waiting batches).1 before _ after h

private theorem handed_prefix_reverse {k : Kernel sys} (rs : List (Act sys P))
    (h : Sound k rs.reverse) : handed rs.reverse <+: (k.exec (requests rs.reverse)).outputs := by
  induction rs with
  | nil => exact List.nil_prefix
  | cons act rs ih =>
    rw [List.reverse_cons] at h ⊢
    have hxs := ih (Sound.of_append h)
    have ha := h rs.reverse act [] rfl
    have hj : requests (rs.reverse ++ [act]) = requests rs.reverse ++ act.ops := by simp [requests]
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

/-- What has been handed over is a prefix of what the requests so far produced. -/
theorem Sound.handed_prefix {k : Kernel sys} {acts : List (Act sys P)} (h : Sound k acts) :
    handed acts <+: (k.exec (requests acts)).outputs := by
  have := handed_prefix_reverse acts.reverse (by rwa [List.reverse_reverse])
  rwa [List.reverse_reverse] at this

/-- A peek asked after an output was handed over is answered with the states of the actors in a
world the semantics reaches, up to actors at rest released (`SysState.Leads`), by a run that put
out that output first. The shard may have started from any kernel requests lead to from boot
(`past`). With a request's response for `o`, this is a read asked after a
write's response seeing that write, and every event the run had before it. -/
theorem chain_peek_after (past : List (Kernel.Op σ)) (waiting : Array (Bool × W))
    (batches : List (Config × List (Command σ P W))) {shown before after : List (Act sys P)}
    {ids : List σ.Id} {reply : P ids} {peek : Peek sys ids} {o : σ.Out}
    (h : chain ((Kernel.boot sys).1.exec past).kernel waiting batches
      = before ++ .answer ids reply peek :: after)
    (hshown : shown <+: before) (ho : o ∈ handed shown) :
    ∃ evs more c, (SysState.init sys Kernel.env).Leads Kernel.env
        ((Kernel.boot sys).2.map .output ++ evs ++ more) c
      ∧ o ∈ Event.outputs evs ∧ (∀ i (hi : i ∈ ids), peek.get i hi = c.state i)
      ∧ (∀ x ∈ peek.others, peek.every x.1 = true ∧ x.2 = c.state x.1)
      ∧ ∀ i, peek.every i = true → i ∉ peek.others.map (·.1) → c.state i = (sys.actor i).init := by
  obtain ⟨hpeek, -⟩ := chain_peek h
  generalize peek.every = every at hpeek ⊢
  obtain ⟨tail, rfl⟩ := hshown
  have hsound : Sound ((Kernel.boot sys).1.exec past).kernel shown :=
    Sound.of_append (Sound.of_append (xs := shown ++ tail)
      (h ▸ (chain_sound _ waiting batches).1))
  have hj : requests (shown ++ tail) = requests shown ++ requests tail := List.flatMap_append ..
  have hreach := (Kernel.exec_reachable sys (past ++ requests shown ++ requests tail)).1
  rw [Kernel.exec_append, Kernel.exec_append] at hreach
  refine ⟨(((Kernel.boot sys).1.exec past).events
      ++ (((Kernel.boot sys).1.exec past).kernel.exec (requests shown)).events), _, _,
    by simpa only [List.append_assoc] using hreach, ?_, ?_⟩
  · rw [Event.outputs_append, Kernel.exec_outputs (((Kernel.boot sys).1.exec past).kernel)]
    apply List.mem_append_right
    exact hsound.handed_prefix.subset ho
  subst hpeek
  refine ⟨fun i hi => ?_, fun x hx => ?_, fun i hp hi => ?_⟩
  · rw [Peek.get_of, hj, Kernel.exec_append]
    rfl
  · obtain ⟨hp, hx⟩ := Peek.others_of hx
    refine ⟨hp, ?_⟩
    rw [hx, hj, Kernel.exec_append]
    rfl
  · have := Peek.init_of_not_others hp hi
    rw [hj, Kernel.exec_append] at this
    exact this

end Lanes.Batch
