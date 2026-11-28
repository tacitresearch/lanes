/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Runtime.Sched
public import Lanes.Runtime.KernelSound
public import Lanes.Proof.Equiv

/-!
The free-running scheduler cannot leave the semantics. `Sched.Model` is the scheduler's whole
state as one value: every actor's slot, each worker's run queue and the actor it holds, the
messages a step sent that are not yet in their receivers' mailboxes, and two ghosts, the
messages in flight in the order the semantics sent them and the outputs not yet handed over.
`Sched.Step` is what the shell's threads do to it, each step one transition: an input arrives,
a timer goes off, a worker takes an actor off a run queue or steals one, steps it, pushes one
message it sent, lets it go, or hands an output over; or the process restarts, and the next
one's scheduler starts afresh. The decisions are the functions of `Lanes.Runtime.Sched` that the
shell calls.

Each transition is zero or one event of `SysState.step` under an environment whose links are
reliable (`Reliable`, which `Kernel.env` is) and which allows restarts if the transition is one
(`Step.sound`), so every run of the model is a run of the semantics, and its outputs are that
run's (`Run.reachable`). The ghosts are never read by a decision, so the shell does without
them.

The invariant `Model.Inv` says what makes that true and what makes the scheduler work
(`Step.inv`):

- the mailboxes and the messages not yet pushed hold the messages in flight, link by link in
  the order they were sent (`Model.Coherent`), which is all an ordered link promises: a message
  at the head of a mailbox is the oldest on its link, so it may be delivered;
- what an actor has not pushed, it sent (`Model.OutSrc`);
- an actor is held by at most one worker, and is running exactly when one holds it; an idle
  actor has no mail, and a queued one is on a run queue, so no mail waits for a worker that will
  never come (`Model.Placed`).

A step that stops its actor needs no message to it waiting to be pushed anywhere, since the
semantics drops all its mail at once; the shell ensures it with a lock that such a step takes
alone (`TRUSTED.md`).
-/

@[expose] public section

namespace Lanes.Sched

variable {σ : Signature} {sys : System σ} {env : EnvModel σ}

/-- Every link of `env` is reliable: ordered, and losing and duplicating nothing, as inside one
process. Whether actors crash, start on their own or the process restarts, it may say. -/
def Reliable (env : EnvModel σ) : Prop :=
  ∀ src dst, env.link src dst = Link.reliable

theorem kernel_reliable : Reliable (Kernel.env : EnvModel σ) := fun _ _ => rfl

/-- The scheduler's whole state. Workers are numbered; run queues and holdings are functions of
the number, of which the shell uses the first `workers`. -/
structure Model (sys : System σ) where
  slot : (i : σ.Id) → Slot sys i
  /-- The messages of each actor's last step not yet pushed to their receivers' mailboxes. -/
  out : σ.Id → List (Envelope σ)
  queue : Nat → List σ.Id
  holding : Nat → Option σ.Id
  /-- Ghost: the messages in flight, oldest first. -/
  net : List (Envelope σ)
  /-- Ghost: the outputs put out and not yet handed over. -/
  outbox : List σ.Out
  /-- The moment the last step was told. -/
  clock : Moment

namespace Model

def blank (sys : System σ) : Model sys where
  slot i := Slot.fresh sys i
  out _ := []
  queue _ := []
  holding _ := none
  net := []
  outbox := []
  clock := {}

/-- The system state the scheduler stands for. -/
def abs (m : Model sys) : SysState sys where
  state i := (m.slot i).cell.state
  up i := (m.slot i).cell.up
  net := m.net
  timers i := (m.slot i).cell.timers.map (·.1)
  outbox := m.outbox
  clock := m.clock

def setSlot (m : Model sys) (i : σ.Id) (s : Slot sys i) : Model sys :=
  { m with slot := update m.slot i s }

/-- Put `i` at the back of worker `w`'s run queue, if `b`. -/
def enqueue (m : Model sys) (w : Nat) (i : σ.Id) (b : Bool) : Model sys :=
  if b then { m with queue := update m.queue w (m.queue w ++ [i]) } else m

/-- Push `x` to `i`'s mailbox; if that makes `i` queued, worker `w` puts it on its run queue. -/
def pushTo (m : Model sys) (i : σ.Id) (x : Item σ i) (w : Nat) : Model sys :=
  match (m.slot i).push x with
  | (b, s) => (m.setSlot i s).enqueue w i b

def input (m : Model sys) (x : σ.In) (w : Nat) : Model sys :=
  match sys.accept x with
  | ⟨i, msg⟩ => { m.pushTo i (.msg none msg) w with net := m.net ++ [⟨none, i, msg⟩] }

/-- The messages in flight that the semantics keeps when actor `i` stops: none to `i`, since
every link of `Kernel.env` is reliable. -/
def keep (i : σ.Id) (e : Envelope σ) : Bool :=
  decide (e.dst ≠ i)

theorem keep_eq (i : σ.Id) : keep i = fun e => !decide (e.dst = i) := by
  funext e
  simp [keep]

/-- The messages in flight once the item of a step is taken: a message delivered is no longer. -/
def base (m : Model sys) (i : σ.Id) : Work σ i → List (Envelope σ)
  | .deliver src msg => m.net.erase ⟨src, i, msg⟩
  | _ => m.net

/-- The step of `i` that `j` is, with its item and state taken out of the slot, leaving `s`,
at `now_ms`: the result written back, its messages left to push, and the ghosts updated. -/
def commit (m : Model sys) (i : σ.Id) (s : Slot sys i) (j : Job sys i) (now_ms : Nat) :
    Model sys :=
  { m with
    slot := update m.slot i (s.put now_ms (j.run m.clock)).1
    out := update m.out i (s.put now_ms (j.run m.clock)).2.sends
    net := (if (j.run m.clock).2.any Effect.isStop then (m.base i j.work).filter (keep i)
      else m.base i j.work) ++ (s.put now_ms (j.run m.clock)).2.sends
    outbox := m.outbox ++ (s.put now_ms (j.run m.clock)).2.outputs }

/-- Worker `w` takes `i` off the front of its run queue, leaving `rest`, and holds it if it was
queued. -/
def beginAt (m : Model sys) (w : Nat) (i : σ.Id) (rest : List σ.Id) : Model sys :=
  match (m.slot i).begin with
  | (true, s) => { m.setSlot i s with queue := update m.queue w rest
                                      holding := update m.holding w (some i) }
  | (false, _) => { m with queue := update m.queue w rest }

/-- Worker `w`, holding `i`, pushes the first message `i`'s step sent. -/
def sendOne (m : Model sys) (i : σ.Id) (e : Envelope σ) (rest : List (Envelope σ)) (w : Nat) :
    Model sys :=
  { m with out := update m.out i rest }.pushTo e.dst (.msg (some i) e.msg) w

/-- Push every message `i`'s last step sent, as worker 0. -/
def drain (m : Model sys) (i : σ.Id) : Nat → Model sys
  | 0 => m
  | n + 1 =>
    match m.out i with
    | [] => m
    | e :: rest => (m.sendOne i e rest 0).drain i n

/-- Start `i`, as `SysState.init` does, and push what it sent. -/
def bootOne (m : Model sys) (i : σ.Id) : Model sys :=
  let m' := m.commit i { (m.slot i) with cell := { (m.slot i).cell with up := true } }
    ⟨.start, (m.slot i).cell.state⟩ 0
  m'.drain i (m'.out i).length

def init (sys : System σ) : Model sys :=
  sys.boot.foldl bootOne (blank sys)

end Model

/-- One transition of the scheduler, and the events of the semantics it is: none, one, or for a
step the moment it is told and the step. -/
inductive Step : Model sys → List (Event σ) → Model sys → Prop
  /-- An input arrives; whoever hands it over puts its actor on worker `w`'s run queue if it
  was idle. -/
  | input (m : Model sys) (x : σ.In) (w : Nat) : Step m [.input x] (m.input x w)
  /-- A timer goes off, whenever the shell's clock says, or not at all: what it pushes is
  checked against the actor's pending timers when it is taken. -/
  | ring (m : Model sys) (i : σ.Id) (msg : σ.Msg i) (due : Kernel.Due) (w : Nat) :
    Step m [] (m.pushTo i (.timer msg due) w)
  /-- Worker `w`, holding nothing, takes the first actor off its run queue, and holds it if it
  was queued. -/
  | begin (m : Model sys) (w : Nat) (i : σ.Id) (rest : List σ.Id) (hhold : m.holding w = none)
    (hq : m.queue w = i :: rest) :
    Step m [] (m.beginAt w i rest)
  /-- Worker `w` takes the first actor off worker `v`'s run queue onto the back of its own. -/
  | steal (m : Model sys) (w v : Nat) (i : σ.Id) (rest : List σ.Id) (hq : m.queue v = i :: rest) :
    Step m []
      { m with queue := update (update m.queue v rest) w (update m.queue v rest w ++ [i]) }
  /-- Worker `w`, holding `i` with every message of its last step pushed, steps it on the next
  item of its mailbox, told the moment `t` (`now_ms` is `t`'s time, which arms its timers). If
  the step stops `i`, no message to `i` is waiting to be pushed. -/
  | step (m : Model sys) (w : Nat) (i : σ.Id) (t : Moment) (j : Job sys i) (s : Slot sys i)
    (hhold : m.holding w = some i) (hout : m.out i = []) (htake : (m.slot i).take = (.job j, s))
    (hstop : (j.run t).2.any Effect.isStop = true → ∀ k, ∀ e ∈ m.out k, e.dst ≠ i) :
    Step m [.tick t, j.work.event] (({ m with clock := t } : Model sys).commit i s j t.now_ms)
  /-- The next item is a timer no longer pending: it is dropped. -/
  | stale (m : Model sys) (w : Nat) (i : σ.Id) (s : Slot sys i) (hhold : m.holding w = some i)
    (hout : m.out i = []) (htake : (m.slot i).take = (.stale, s)) :
    Step m [] (m.setSlot i s)
  /-- Worker `w`, holding `i`, pushes the first message `i`'s step sent. -/
  | send (m : Model sys) (w : Nat) (i : σ.Id) (e : Envelope σ) (rest : List (Envelope σ))
    (hhold : m.holding w = some i) (hout : m.out i = e :: rest) :
    Step m [] (m.sendOne i e rest w)
  /-- Worker `w` lets go of `i` once every message it sent is pushed, and puts it back on its
  run queue if mail is waiting. -/
  | release (m : Model sys) (w : Nat) (i : σ.Id) (hhold : m.holding w = some i)
    (hout : m.out i = []) :
    Step m []
      (match (m.slot i).release with
       | (b, s) => ({ m.setSlot i s with holding := update m.holding w none }).enqueue w i b)
  /-- An output put out is handed over, in any order. -/
  | handOver (m : Model sys) (out : σ.Out) (h : out ∈ m.outbox) :
    Step m [.output out] { m with outbox := m.outbox.erase out }
  /-- The process restarts: the next process's scheduler starts afresh, every actor booted again
  and everything else lost. -/
  | restart (m : Model sys) : Step m [.restart] (Model.init sys)

/-- Transitions one after another, and the events they are. -/
inductive Run : Model sys → List (Event σ) → Model sys → Prop
  | refl (m : Model sys) : Run m [] m
  | step {m m' m'' : Model sys} {ev evs : List (Event σ)} :
    Step m ev m' → Run m' evs m'' → Run m (ev ++ evs) m''


/-! What a slot's step does, as the semantics' `settle` does it. -/

namespace Slot

variable {i : σ.Id}

@[simp] theorem Commit.reverse_reverse (c : Commit σ i) : c.reverse.reverse = c := by
  simp [Commit.reverse]

theorem performRev_eq (now_ms : Nat) (eff : Effect σ i) (s : Slot sys i) (c : Commit σ i) :
    performRev now_ms (s, c) eff
      = ((perform now_ms (s, c.reverse) eff).1, (perform now_ms (s, c.reverse) eff).2.reverse) := by
  cases eff <;> simp [performRev, perform, Commit.reverse]

theorem foldl_performRev (now_ms : Nat) (effs : List (Effect σ i)) :
    ∀ (s : Slot sys i) (c : Commit σ i), effs.foldl (performRev now_ms) (s, c)
      = ((effs.foldl (perform now_ms) (s, c.reverse)).1,
          (effs.foldl (perform now_ms) (s, c.reverse)).2.reverse) := by
  induction effs with
  | nil => intro s c; simp
  | cons eff effs ih => intro s c; simp only [List.foldl_cons, performRev_eq, ih, Commit.reverse_reverse]

/-- `put` gathers the step's sends, outputs and timers newest first and turns them round once:
it is the fold of `perform`, which appends each, and costs time linear in the effects. -/
theorem put_eq (now_ms : Nat) (r : sys.State i × List (Effect σ i)) (s : Slot sys i) :
    s.put now_ms r =
      match r.2.foldl (perform now_ms) ({ s with cell := { s.cell with state := r.1 } }, {}) with
      | (s, c) => if r.2.any Effect.isStop then down s c else (s, c) := by
  unfold put
  rw [foldl_performRev, show ({} : Commit σ i).reverse = {} from rfl]
  generalize r.2.foldl (perform now_ms) _ = f
  rcases f with ⟨s', c'⟩
  simp

theorem perform_fold (now_ms : Nat) (effs : List (Effect σ i)) :
    ∀ (s : Slot sys i) (cm : Commit σ i) (c : SysState sys),
      c.timers i = s.cell.timers.map (·.1) →
      ({ c with net := c.net ++ cm.sends, outbox := c.outbox ++ cm.outputs }).performAll i effs
        = { c with net := c.net ++ (effs.foldl (perform now_ms) (s, cm)).2.sends
                   outbox := c.outbox ++ (effs.foldl (perform now_ms) (s, cm)).2.outputs
                   timers := update c.timers i
                     ((effs.foldl (perform now_ms) (s, cm)).1.cell.timers.map (·.1)) }
      ∧ (effs.foldl (perform now_ms) (s, cm)).1.cell.state = s.cell.state
      ∧ (effs.foldl (perform now_ms) (s, cm)).1.cell.up = s.cell.up
      ∧ (effs.foldl (perform now_ms) (s, cm)).1.mail = s.mail
      ∧ (effs.foldl (perform now_ms) (s, cm)).1.status = s.status
      ∧ (∀ e ∈ (effs.foldl (perform now_ms) (s, cm)).2.sends, e ∈ cm.sends ∨ e.src = some i) := by
  induction effs with
  | nil =>
    intro s cm c ht
    refine ⟨?_, rfl, rfl, rfl, rfl, fun e he => .inl he⟩
    apply SysState.ext' <;> simp [← ht]
  | cons eff effs ih =>
    intro s cm c ht
    cases eff with
    | send to msg =>
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ih s { cm with sends := cm.sends ++ [⟨some i, to, msg⟩] } c ht
      refine ⟨?_, h2, h3, h4, h5, fun e he => ?_⟩
      · simp only [SysState.performAll_cons, List.foldl_cons, perform]
        rw [← h1]
        congr 1
        simp [SysState.perform, List.append_assoc]
      · rcases h6 e he with h | h
        · simp only [List.mem_append, List.mem_singleton] at h
          rcases h with h | rfl
          · exact .inl h
          · exact .inr rfl
        · exact .inr h
    | emit out =>
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ih s { cm with outputs := cm.outputs ++ [out] } c ht
      refine ⟨?_, h2, h3, h4, h5, h6⟩
      simp only [SysState.performAll_cons, List.foldl_cons, perform]
      rw [← h1]
      congr 1
      simp [SysState.perform, List.append_assoc]
    | after delay_ms msg =>
      let due : Kernel.Due := ⟨now_ms + delay_ms, s.nextToken⟩
      let s' : Slot sys i := { s with nextToken := s.nextToken + 1,
                                      cell := { s.cell with timers := arm s.cell.timers msg due } }
      let c' : SysState sys :=
        { c with timers := update c.timers i ((arm s.cell.timers msg due).map (·.1)) }
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
        ih s' { cm with armed := cm.armed ++ [(msg, due)] } c' (by simp [c', s'])
      refine ⟨?_, h2, h3, h4, h5, h6⟩
      simp only [SysState.performAll_cons, List.foldl_cons, perform]
      refine Eq.trans ?_ (h1.trans ?_)
      · congr 1
        apply SysState.ext' <;> simp only [c', SysState.perform, arm, Kernel.map_fst_arm]
        rw [ht]
      · apply SysState.ext' <;> simp only [c', update_update] <;> rfl
    | cancel msg =>
      let s' : Slot sys i :=
        { s with cell := { s.cell with timers := s.cell.timers.eraseP (·.1 = msg) } }
      let c' : SysState sys :=
        { c with timers := update c.timers i ((s.cell.timers.eraseP (·.1 = msg)).map (·.1)) }
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ih s' cm c' (by simp [c', s'])
      refine ⟨?_, h2, h3, h4, h5, h6⟩
      simp only [SysState.performAll_cons, List.foldl_cons, perform]
      refine Eq.trans ?_ (h1.trans ?_)
      · congr 1
        apply SysState.ext' <;> simp only [c', SysState.perform, map_fst_eraseP]
        rw [ht]
      · apply SysState.ext' <;> simp only [c', update_update] <;> rfl
    | stop =>
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ih s cm c ht
      refine ⟨?_, h2, h3, h4, h5, h6⟩
      simp only [SysState.performAll_cons, List.foldl_cons, perform]
      rw [← h1]
      rfl

theorem put_settle (now_ms : Nat) (r : sys.State i × List (Effect σ i)) (s : Slot sys i)
    (c : SysState sys) (ht : c.timers i = s.cell.timers.map (·.1)) (hup : c.up i = s.cell.up)
    (henv : Reliable env) :
    c.settle env i r =
      { c with
        state := update c.state i (s.put now_ms r).1.cell.state
        up := update c.up i (s.put now_ms r).1.cell.up
        timers := update c.timers i ((s.put now_ms r).1.cell.timers.map (·.1))
        net := (if r.2.any Effect.isStop then c.net.filter (Model.keep i) else c.net)
          ++ (s.put now_ms r).2.sends
        outbox := c.outbox ++ (s.put now_ms r).2.outputs }
    ∧ (if r.2.any Effect.isStop then (s.put now_ms r).1.cell.up = false
        else (s.put now_ms r).1.cell.up = s.cell.up)
    ∧ (s.put now_ms r).1.status = s.status
    ∧ (s.put now_ms r).1.mail = (if r.2.any Effect.isStop then {} else s.mail)
    ∧ ∀ e ∈ (s.put now_ms r).2.sends, e.src = some i
        ∧ (r.2.any Effect.isStop = true → e.dst ≠ i) := by
  let s0 : Slot sys i := { s with cell := { s.cell with state := r.1 } }
  let c0 : SysState sys := { c with state := update c.state i r.1 }
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := perform_fold now_ms r.2 s0 {} c0 (by simpa [c0, s0] using ht)
  simp only [List.append_nil] at h1
  have hc0 : ({ c0 with net := c0.net, outbox := c0.outbox } : SysState sys) = c0 := rfl
  rw [hc0] at h1
  unfold SysState.settle
  rw [put_eq]
  rcases hf : r.2.foldl (perform now_ms) (s0, {}) with ⟨s', cm⟩
  rw [hf] at h1 h2 h3 h4 h5 h6
  simp only at h1 h2 h3 h4 h5 h6
  have h6' : ∀ e ∈ cm.sends, e.src = some i := fun e he => (h6 e he).resolve_left (by simp)
  change c0.performAll i r.2 = _ at h1
  by_cases hstop : r.2.any Effect.isStop = true
  · simp only [hstop, ite_true, down]
    refine ⟨?_, trivial, h5, trivial, fun e he => ?_⟩
    · rw [h1]
      apply SysState.ext' <;> simp [SysState.down, c0, s0, h2, show ∀ a b, env.link a b = Link.reliable from henv, Link.reliable,
        Model.keep_eq, List.filter_append, update_update]
    · simp only [List.mem_filter, decide_eq_true_eq] at he
      exact ⟨h6' e he.1, fun _ => he.2⟩
  · simp only [hstop, Bool.false_eq_true, ite_false]
    refine ⟨?_, by simpa [s0] using h3, h5, h4, fun e he => ⟨h6' e he, fun h => absurd h (by simp)⟩⟩
    rw [h1]
    apply SysState.ext' <;> simp [c0, s0, h2, h3, ← hup]

@[simp] theorem push_mail (x : Item σ i) (s : Slot sys i) :
    (s.push x).2.mail.toList = s.mail.toList ++ [x] := by
  unfold push; split <;> simp

@[simp] theorem push_cell (x : Item σ i) (s : Slot sys i) : (s.push x).2.cell = s.cell := by
  unfold push; split <;> rfl

theorem push_status (x : Item σ i) (s : Slot sys i) :
    (s.push x).2.status = (if s.status = .idle then .queued else s.status) := by
  unfold push; split <;> simp_all

@[simp] theorem begin_cell (s : Slot sys i) : s.begin.2.cell = s.cell := by
  unfold begin; split <;> rfl
@[simp] theorem begin_mail (s : Slot sys i) : s.begin.2.mail = s.mail := by
  unfold begin; split <;> rfl
@[simp] theorem release_cell (s : Slot sys i) : s.release.2.cell = s.cell := by
  unfold release; split <;> rfl
@[simp] theorem release_mail (s : Slot sys i) : s.release.2.mail = s.mail := by
  unfold release; split <;> rfl

theorem push_fst (x : Item σ i) (s : Slot sys i) : (s.push x).1 = decide (s.status = .idle) := by
  unfold push; split <;> simp_all

/-- What `take` leaves when it gives a step: the state taken out, the status as it was, and the
mailbox and the actor as the step's kind says. -/
theorem take_eq_job {s s' : Slot sys i} {j : Job sys i} (h : s.take = (.job j, s')) :
    j.state = s.cell.state ∧ s'.status = s.status ∧
    ((∃ src msg rest, j.work = .deliver src msg ∧ s.mail.pop? = some (.msg src msg, rest)
        ∧ s.cell.up = true ∧ s'.mail = rest ∧ s'.cell.up = true ∧ s'.cell.timers = s.cell.timers)
     ∨ (∃ src msg rest, j.work = .start ∧ s.mail.pop? = some (.msg src msg, rest)
        ∧ s.cell.up = false ∧ s'.mail = s.mail ∧ s'.cell.up = true
        ∧ s'.cell.timers = s.cell.timers)
     ∨ (∃ msg due rest, j.work = .timeout msg ∧ s.mail.pop? = some (.timer msg due, rest)
        ∧ s.cell.up = true ∧ (msg, due) ∈ s.cell.timers ∧ s'.mail = rest ∧ s'.cell.up = true
        ∧ s'.cell.timers = s.cell.timers.eraseP (·.1 = msg))) := by
  unfold take at h
  split at h
  · cases h
  · next src msg rest hpop =>
    by_cases hup : s.cell.up = true
    · simp only [hup, ite_true, Prod.mk.injEq, Taken.job.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, rfl, .inl ⟨src, msg, rest, rfl, hpop, hup, rfl, rfl, rfl⟩⟩
    · simp only [hup, Bool.false_eq_true, ite_false, Prod.mk.injEq, Taken.job.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, rfl, .inr (.inl ⟨src, msg, rest, rfl, hpop, by simpa using hup, rfl, rfl, rfl⟩)⟩
  · next msg due rest hpop =>
    split at h
    · next hok =>
      simp only [Prod.mk.injEq, Taken.job.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Bool.and_eq_true, List.contains_iff_mem] at hok
      exact ⟨rfl, rfl, .inr (.inr ⟨msg, due, rest, rfl, hpop, hok.1, hok.2, rfl, by simp [hok.1], rfl⟩)⟩
    · cases h

theorem take_eq_stale {s s' : Slot sys i} (h : s.take = (.stale, s')) :
    ∃ msg due, s.mail.toList = .timer msg due :: s'.mail.toList ∧ s'.cell = s.cell
      ∧ s'.status = s.status := by
  unfold take at h
  split at h
  · cases h
  · split at h <;> cases h
  · next msg due rest hpop =>
    split at h
    · cases h
    · simp only [Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact ⟨msg, due, Fifo.toList_of_pop? hpop, rfl, rfl⟩

end Slot

/-! The messages in flight are in the mailboxes and the messages not yet pushed, link by link in
order. -/

/-- The messages from `src` among the items of a mailbox of `dst`. -/
def mailEnvs (dst : σ.Id) (src : Option σ.Id) (items : List (Item σ dst)) : List (Envelope σ) :=
  items.filterMap fun
    | .msg s m => if s = src then some ⟨s, dst, m⟩ else none
    | .timer _ _ => none

namespace Model

/-- The messages a sender's step sent and not yet pushed: none from outside. -/
def pend (out : σ.Id → List (Envelope σ)) : Option σ.Id → List (Envelope σ)
  | none => []
  | some j => out j

/-- On every link, the messages in flight are those in the receiver's mailbox, then those the
sender has not pushed yet, in order. -/
def Coherent (m : Model sys) : Prop :=
  ∀ src dst, m.net.filter (onLink src dst)
    = mailEnvs dst src (m.slot dst).mail.toList ++ (pend m.out src).filter (onLink src dst)

/-- What each actor has not yet pushed, it sent. -/
def OutSrc (m : Model sys) : Prop :=
  ∀ j, ∀ e ∈ m.out j, e.src = some j

end Model

@[simp] theorem mailEnvs_nil (dst : σ.Id) (src : Option σ.Id) : mailEnvs dst src [] = [] := rfl

theorem mailEnvs_append (dst : σ.Id) (src : Option σ.Id) (a b : List (Item σ dst)) :
    mailEnvs dst src (a ++ b) = mailEnvs dst src a ++ mailEnvs dst src b := by
  simp [mailEnvs, List.filterMap_append]

@[simp] theorem mailEnvs_timer (dst : σ.Id) (src : Option σ.Id) (msg : σ.Msg dst) (due : Kernel.Due)
    (l : List (Item σ dst)) : mailEnvs dst src (.timer msg due :: l) = mailEnvs dst src l := by
  simp [mailEnvs]

theorem mailEnvs_msg (dst : σ.Id) (src s : Option σ.Id) (msg : σ.Msg dst) (l : List (Item σ dst)) :
    mailEnvs dst src (.msg s msg :: l)
      = (if s = src then [⟨s, dst, msg⟩] else []) ++ mailEnvs dst src l := by
  by_cases h : s = src <;> simp [mailEnvs, h]

theorem mem_mailEnvs {dst : σ.Id} {src : Option σ.Id} {l : List (Item σ dst)} {e : Envelope σ}
    (h : e ∈ mailEnvs dst src l) : e.src = src ∧ e.dst = dst := by
  simp only [mailEnvs, List.mem_filterMap] at h
  obtain ⟨x, -, hx⟩ := h
  cases x with
  | msg s m =>
    simp only at hx
    split at hx
    · cases hx; simp_all
    · cases hx
  | timer _ _ => cases hx

theorem filter_onLink_eq_nil {src : Option σ.Id} {dst : σ.Id} {l : List (Envelope σ)}
    (h : ∀ e ∈ l, e.src ≠ src ∨ e.dst ≠ dst) : l.filter (onLink src dst) = [] := by
  rw [List.filter_eq_nil_iff]
  intro e he
  rcases h e he with h | h <;> simp [onLink, h]


namespace Model

variable {m : Model sys}

@[simp] theorem setSlot_slot (m : Model sys) (i : σ.Id) (s : Slot sys i) :
    (m.setSlot i s).slot = update m.slot i s := rfl

@[simp] theorem enqueue_slot (m : Model sys) (w : Nat) (i : σ.Id) (b : Bool) :
    (m.enqueue w i b).slot = m.slot := by unfold enqueue; split <;> rfl
@[simp] theorem enqueue_out (m : Model sys) (w : Nat) (i : σ.Id) (b : Bool) :
    (m.enqueue w i b).out = m.out := by unfold enqueue; split <;> rfl
@[simp] theorem enqueue_net (m : Model sys) (w : Nat) (i : σ.Id) (b : Bool) :
    (m.enqueue w i b).net = m.net := by unfold enqueue; split <;> rfl
@[simp] theorem enqueue_outbox (m : Model sys) (w : Nat) (i : σ.Id) (b : Bool) :
    (m.enqueue w i b).outbox = m.outbox := by unfold enqueue; split <;> rfl
@[simp] theorem enqueue_clock (m : Model sys) (w : Nat) (i : σ.Id) (b : Bool) :
    (m.enqueue w i b).clock = m.clock := by unfold enqueue; split <;> rfl
@[simp] theorem pushTo_clock (m : Model sys) (i : σ.Id) (x : Item σ i) (w : Nat) :
    (m.pushTo i x w).clock = m.clock := by simp [pushTo]; rfl
@[simp] theorem abs_clock (m : Model sys) : m.abs.clock = m.clock := rfl
@[simp] theorem commit_clock (m : Model sys) (i : σ.Id) (s : Slot sys i) (j : Job sys i) (n : Nat) :
    (m.commit i s j n).clock = m.clock := rfl
@[simp] theorem enqueue_holding (m : Model sys) (w : Nat) (i : σ.Id) (b : Bool) :
    (m.enqueue w i b).holding = m.holding := by unfold enqueue; split <;> rfl
theorem enqueue_queue (m : Model sys) (w : Nat) (i : σ.Id) (b : Bool) :
    (m.enqueue w i b).queue = if b then update m.queue w (m.queue w ++ [i]) else m.queue := by
  unfold enqueue; split <;> rfl

@[simp] theorem pushTo_slot (m : Model sys) (i : σ.Id) (x : Item σ i) (w : Nat) :
    (m.pushTo i x w).slot = update m.slot i ((m.slot i).push x).2 := by
  simp [pushTo]
@[simp] theorem pushTo_out (m : Model sys) (i : σ.Id) (x : Item σ i) (w : Nat) :
    (m.pushTo i x w).out = m.out := by simp [pushTo]; rfl
@[simp] theorem pushTo_net (m : Model sys) (i : σ.Id) (x : Item σ i) (w : Nat) :
    (m.pushTo i x w).net = m.net := by simp [pushTo]; rfl
@[simp] theorem pushTo_outbox (m : Model sys) (i : σ.Id) (x : Item σ i) (w : Nat) :
    (m.pushTo i x w).outbox = m.outbox := by simp [pushTo]; rfl
@[simp] theorem pushTo_holding (m : Model sys) (i : σ.Id) (x : Item σ i) (w : Nat) :
    (m.pushTo i x w).holding = m.holding := by simp [pushTo]; rfl
theorem pushTo_queue (m : Model sys) (i : σ.Id) (x : Item σ i) (w : Nat) :
    (m.pushTo i x w).queue = if (m.slot i).status = .idle
      then update m.queue w (m.queue w ++ [i]) else m.queue := by
  simp only [pushTo, enqueue_queue, Slot.push_fst]
  by_cases h : (m.slot i).status = .idle <;> simp [h, setSlot]

@[simp] theorem setSlot_out (m : Model sys) (i : σ.Id) (s : Slot sys i) :
    (m.setSlot i s).out = m.out := rfl
@[simp] theorem setSlot_net (m : Model sys) (i : σ.Id) (s : Slot sys i) :
    (m.setSlot i s).net = m.net := rfl
@[simp] theorem setSlot_outbox (m : Model sys) (i : σ.Id) (s : Slot sys i) :
    (m.setSlot i s).outbox = m.outbox := rfl
@[simp] theorem setSlot_clock (m : Model sys) (i : σ.Id) (s : Slot sys i) :
    (m.setSlot i s).clock = m.clock := rfl
@[simp] theorem setSlot_holding (m : Model sys) (i : σ.Id) (s : Slot sys i) :
    (m.setSlot i s).holding = m.holding := rfl
@[simp] theorem setSlot_queue (m : Model sys) (i : σ.Id) (s : Slot sys i) :
    (m.setSlot i s).queue = m.queue := rfl

theorem slot_update_apply {i k : σ.Id} {s : Slot sys i} {f : (j : σ.Id) → Slot sys j}
    (P : (j : σ.Id) → Slot sys j → Prop) (hi : P i s) (hk : k ≠ i → P k (f k)) :
    P k (update f i s k) := by
  by_cases h : k = i
  · subst h; simpa using hi
  · simpa [h] using hk h

/-- Only the mailboxes' messages, the messages not pushed and the ghost of the messages in
flight matter to coherence. -/
theorem Coherent.of_mail {m' : Model sys} (h : m.Coherent) (hnet : m'.net = m.net)
    (hout : m'.out = m.out)
    (hmail : ∀ k src, mailEnvs k src (m'.slot k).mail.toList = mailEnvs k src (m.slot k).mail.toList) :
    m'.Coherent := by
  intro src dst
  rw [hnet, hmail, hout]
  exact h src dst

theorem Coherent.pushTimer (h : m.Coherent) (i : σ.Id) (msg : σ.Msg i) (due : Kernel.Due)
    (w : Nat) : (m.pushTo i (.timer msg due) w).Coherent := by
  refine h.of_mail (by simp) (by simp) fun k src => ?_
  by_cases hk : k = i
  · subst hk; simp [mailEnvs]
  · simp [hk]

theorem Coherent.setSlot (h : m.Coherent) {i : σ.Id} {s : Slot sys i}
    (hs : s.mail.toList = (m.slot i).mail.toList) : (m.setSlot i s).Coherent := by
  refine h.of_mail rfl rfl fun k src => ?_
  by_cases hk : k = i
  · subst hk; simp [hs]
  · simp [hk]

theorem Coherent.input (h : m.Coherent) (x : σ.In) (w : Nat) : (m.input x w).Coherent := by
  unfold Model.input
  rcases hx : sys.accept x with ⟨i, msg⟩
  intro src dst
  simp only [pushTo_slot, List.filter_append, h src dst]
  by_cases hd : dst = i
  · subst hd
    simp only [update_self, Slot.push_mail, mailEnvs_append]
    cases src with
    | none => simp [pend, mailEnvs, onLink]
    | some k => simp [pend, mailEnvs, onLink]
  · cases src <;> simp [hd, onLink, Ne.symm hd, pend]

theorem Coherent.sendOne (h : m.Coherent) (hsrc : m.OutSrc) {i : σ.Id} {e : Envelope σ}
    {rest : List (Envelope σ)} (hout : m.out i = e :: rest) (w : Nat) :
    (m.sendOne i e rest w).Coherent := by
  have he : e.src = some i := hsrc i e (by simp [hout])
  intro src dst
  unfold Model.sendOne
  simp only [pushTo_slot, pushTo_net, h src dst]
  have hpend : ∀ s, pend (({ m with out := update m.out i rest } : Model sys).pushTo e.dst
      (.msg (some i) e.msg) w).out s = if s = some i then rest else pend m.out s := by
    intro s
    rw [pushTo_out]
    cases s with
    | none => simp [pend]
    | some k =>
      by_cases hk : k = i
      · subst hk; simp [pend]
      · simp [pend, hk]
  rw [hpend]
  by_cases hd : dst = e.dst
  · subst hd
    simp only [update_self, Slot.push_mail, mailEnvs_append]
    by_cases hs : src = some i
    · subst hs
      obtain ⟨es, ed, em⟩ := e
      simp only at he
      subst he
      simp [pend, hout, mailEnvs, onLink]
    · have : some i ≠ src := fun h => hs h.symm
      simp [mailEnvs, this, hs]
  · simp only [ne_eq, hd, not_false_eq_true, update_of_ne]
    by_cases hs : src = some i
    · subst hs
      simp [pend, hout, onLink, Ne.symm hd]
    · simp [hs]

end Model


namespace Model

variable {m : Model sys}

theorem filter_keep_onLink (i : σ.Id) (src : Option σ.Id) (dst : σ.Id) (l : List (Envelope σ)) :
    (l.filter (keep i)).filter (onLink src dst)
      = if dst = i then [] else l.filter (onLink src dst) := by
  rw [List.filter_filter]
  split
  · next h =>
    subst h
    rw [List.filter_eq_nil_iff]
    intro e _
    simp_all [onLink, keep_eq]
  · next h =>
    congr 1
    funext e
    by_cases hon : onLink src dst e = true
    · have hd : e.dst = dst := by simp [onLink] at hon; exact hon.2
      simp [hon, keep, hd, h]
    · simp [hon]

/-- Taking the next item out keeps the mailboxes coherent with the messages in flight once the
message delivered, if any, is no longer. -/
theorem Coherent.take (h : m.Coherent) {i : σ.Id} {j : Job sys i} {s : Slot sys i}
    (htake : (m.slot i).take = (.job j, s)) :
    ({ m.setSlot i s with net := m.base i j.work } : Model sys).Coherent := by
  obtain ⟨-, -, hcase⟩ := Slot.take_eq_job htake
  rcases hcase with ⟨src₀, msg, rest, hw, hpop, -, hmail, -, -⟩
      | ⟨src₀, msg, rest, hw, hpop, -, hmail, -, -⟩ | ⟨msg, due, rest, hw, hpop, -, -, hmail, -, -⟩
  · have hlist := Fifo.toList_of_pop? hpop
    intro src dst
    simp only [hw, base, setSlot_slot]
    by_cases hq : onLink src dst ⟨src₀, i, msg⟩ = true
    · have hs : src₀ = src ∧ i = dst := by simpa [onLink] using hq
      obtain ⟨rfl, rfl⟩ := hs
      rw [filter_erase_of_pos _ _ hq, h src₀ i, hlist, mailEnvs_msg]
      simp [hmail]
    · have hq' : onLink src dst ⟨src₀, i, msg⟩ = false := by simpa using hq
      rw [filter_erase_of_neg _ _ hq', h src dst]
      by_cases hd : dst = i
      · subst hd
        have : ¬ src₀ = src := fun hs => hq (by simp [onLink, hs])
        simp [hlist, mailEnvs_msg, this, hmail]
      · simp [hd]
  · refine h.of_mail (by simp [hw, base]) rfl fun k src => ?_
    by_cases hk : k = i
    · subst hk; simp [hmail]
    · simp [hk]
  · refine h.of_mail (by simp [hw, base]) rfl fun k src => ?_
    by_cases hk : k = i
    · subst hk; simp [hmail, Fifo.toList_of_pop? hpop]
    · simp [hk]

theorem Coherent.stale (h : m.Coherent) {i : σ.Id} {s : Slot sys i}
    (htake : (m.slot i).take = (.stale, s)) : (m.setSlot i s).Coherent := by
  obtain ⟨msg, due, hmail, -, -⟩ := Slot.take_eq_stale htake
  refine h.of_mail rfl rfl fun k src => ?_
  by_cases hk : k = i
  · subst hk; simp [hmail]
  · simp [hk]

/-- A step written back keeps the mailboxes coherent: its messages are those not yet pushed,
and if it stopped the actor, nothing in flight is for it any more. -/
theorem coherent_commit {i : σ.Id} {j : Job sys i} {s : Slot sys i}
    (h1 : ({ m.setSlot i s with net := m.base i j.work } : Model sys).Coherent)
    (now_ms : Nat) (hout : m.out i = [])
    (hstop : (j.run m.clock).2.any Effect.isStop = true → ∀ k, ∀ e ∈ m.out k, e.dst ≠ i) :
    (m.commit i s j now_ms).Coherent := by
  obtain ⟨-, -, -, hmail', hsends⟩ :=
    Slot.put_settle now_ms (j.run m.clock) s (m.setSlot i s).abs (by simp [abs]) (by simp [abs]) kernel_reliable
  have hpend : ∀ src, pend (m.commit i s j now_ms).out src
      = if src = some i then (s.put now_ms (j.run m.clock)).2.sends else pend m.out src := by
    intro src
    cases src with
    | none => simp [pend]
    | some k =>
      by_cases hk : k = i
      · subst hk; simp [pend, Model.commit]
      · simp [pend, Model.commit, hk]
  have hnil : ∀ src dst, src ≠ some i →
      (s.put now_ms (j.run m.clock)).2.sends.filter (onLink src dst) = [] := fun src dst hs =>
    filter_onLink_eq_nil fun e he => .inl ((hsends e he).1 ▸ fun h' => hs h'.symm)
  intro src dst
  have h1' := h1 src dst
  simp only [setSlot_slot, setSlot_out] at h1'
  rw [hpend]
  simp only [Model.commit, List.filter_append]
  by_cases hstop' : (j.run m.clock).2.any Effect.isStop = true
  · simp only [hstop', ite_true, filter_keep_onLink] at hmail' ⊢
    by_cases hd : dst = i
    · subst hd
      have hsnil : (s.put now_ms (j.run m.clock)).2.sends.filter (onLink src dst) = [] :=
        filter_onLink_eq_nil fun e he => .inr ((hsends e he).2 hstop')
      simp only [ite_true, List.nil_append, hsnil, update_self, hmail', Fifo.toList_empty,
        mailEnvs_nil]
      split
      · exact hsnil.symm
      · cases src with
        | none => rfl
        | some k =>
          exact (filter_onLink_eq_nil fun e he => .inr (hstop hstop' k e he)).symm
    · simp only [hd, ite_false, ne_eq, not_false_eq_true, update_of_ne, h1']
      split
      · next hs => subst hs; simp [pend, hout]
      · next hs => simp [hnil src dst hs]
  · simp only [hstop', Bool.false_eq_true, ite_false] at hmail' ⊢
    rw [h1']
    have hm : mailEnvs dst src (update m.slot i (s.put now_ms (j.run m.clock)).1 dst).mail.toList
        = mailEnvs dst src (update m.slot i s dst).mail.toList := by
      by_cases hd : dst = i
      · subst hd; simp [hmail']
      · simp [hd]
    rw [hm]
    split
    · next hs => subst hs; simp [pend, hout]
    · next hs => simp [hnil src dst hs]

end Model


namespace Model

variable {m : Model sys}

/-- Where the actors are: running exactly when a worker holds them, held by one worker at most,
idle only without mail, and on a run queue when queued. -/
structure Placed (m : Model sys) : Prop where
  held : ∀ i, (m.slot i).status = .running ↔ ∃ w, m.holding w = some i
  unique : ∀ w v i, m.holding w = some i → m.holding v = some i → w = v
  idle : ∀ i, (m.slot i).status = .idle → (m.slot i).mail.toList = []
  queued : ∀ i, (m.slot i).status = .queued → ∃ w, i ∈ m.queue w

/-- What every state of the scheduler's model satisfies. -/
structure Inv (m : Model sys) : Prop where
  coherent : m.Coherent
  outSrc : m.OutSrc
  placed : m.Placed

theorem mem_pushTo_queue {k : σ.Id} {v : Nat} (i : σ.Id) (x : Item σ i) (w : Nat)
    (h : k ∈ m.queue v) : k ∈ (m.pushTo i x w).queue v := by
  rw [pushTo_queue]
  split
  · by_cases hv : v = w
    · subst hv; simp [h]
    · simp [hv, h]
  · exact h

theorem Placed.pushTo (h : m.Placed) (i : σ.Id) (x : Item σ i) (w : Nat) :
    (m.pushTo i x w).Placed := by
  have hstatus : ∀ k, ((m.pushTo i x w).slot k).status
      = if k = i ∧ (m.slot i).status = .idle then .queued else (m.slot k).status := by
    intro k
    by_cases hk : k = i
    · subst hk; simp [Slot.push_status]
    · simp [hk]
  refine ⟨fun k => ?_, fun w v k => by simpa using h.unique w v k, fun k => ?_, fun k => ?_⟩
  · rw [hstatus, pushTo_holding]
    split
    · next hk =>
      obtain ⟨rfl, hidle⟩ := hk
      simp only [reduceCtorEq, false_iff, not_exists]
      intro v hv
      have := (h.held k).mpr ⟨v, hv⟩
      simp_all
    · exact h.held k
  · rw [hstatus]
    split
    · simp
    · next hk =>
      intro hidle
      by_cases hki : k = i
      · subst hki; exact absurd ⟨rfl, hidle⟩ hk
      · simpa [hki] using h.idle k hidle
  · rw [hstatus]
    split
    · next hk =>
      obtain ⟨rfl, hidle⟩ := hk
      intro _
      refine ⟨w, ?_⟩
      simp [pushTo_queue, hidle]
    · intro hq
      obtain ⟨v, hv⟩ := h.queued k hq
      exact ⟨v, mem_pushTo_queue i x w hv⟩

theorem Placed.of_status {m' : Model sys} (h : m.Placed) (hholding : m'.holding = m.holding)
    (hqueue : m'.queue = m.queue) (hstatus : ∀ k, (m'.slot k).status = (m.slot k).status)
    (hmail : ∀ k, (m.slot k).status = .idle → (m'.slot k).mail.toList = (m.slot k).mail.toList) :
    m'.Placed :=
  ⟨fun k => by rw [hstatus, hholding]; exact h.held k,
   fun w v k => by rw [hholding]; exact h.unique w v k,
   fun k hk => by rw [hstatus] at hk; rw [hmail k hk]; exact h.idle k hk,
   fun k hk => by rw [hstatus] at hk; rw [hqueue]; exact h.queued k hk⟩

theorem running_of_holding (h : m.Placed) {w : Nat} {i : σ.Id} (hhold : m.holding w = some i) :
    (m.slot i).status = .running :=
  (h.held i).mpr ⟨w, hhold⟩

end Model


namespace Model

variable {m : Model sys}

@[simp] theorem abs_pushTo (m : Model sys) (i : σ.Id) (x : Item σ i) (w : Nat) :
    (m.pushTo i x w).abs = m.abs := by
  refine SysState.ext' ?_ ?_ ?_ ?_ ?_
  · funext k; by_cases hk : k = i
    · subst hk; simp [abs]
    · simp [abs, hk]
  · funext k; by_cases hk : k = i
    · subst hk; simp [abs]
    · simp [abs, hk]
  · simp [abs]
  · funext k; by_cases hk : k = i
    · subst hk; simp [abs]
    · simp [abs, hk]
  · simp [abs]

theorem abs_input (m : Model sys) (x : σ.In) (w : Nat) :
    (m.input x w).abs
      = { m.abs with net := m.abs.net ++ [⟨none, (sys.accept x).1, (sys.accept x).2⟩] } := by
  unfold Model.input
  rcases hx : sys.accept x with ⟨i, msg⟩
  have hp := abs_pushTo m i (.msg none msg) w
  dsimp only
  refine SysState.ext' ?_ ?_ ?_ ?_ ?_
  · have := congrArg SysState.state hp; exact this
  · have := congrArg SysState.up hp; exact this
  · simp [abs]
  · have := congrArg SysState.timers hp; exact this
  · simp [abs]

theorem abs_setSlot {i : σ.Id} {s : Slot sys i} (h : s.cell = (m.slot i).cell) :
    (m.setSlot i s).abs = m.abs := by
  refine SysState.ext' ?_ ?_ ?_ ?_ ?_
  · funext k; by_cases hk : k = i
    · subst hk; simp [abs, h]
    · simp [abs, hk]
  · funext k; by_cases hk : k = i
    · subst hk; simp [abs, h]
    · simp [abs, hk]
  · rfl
  · funext k; by_cases hk : k = i
    · subst hk; simp [abs, h]
    · simp [abs, hk]
  · rfl

@[simp] theorem abs_enqueue (m : Model sys) (w : Nat) (i : σ.Id) (b : Bool) :
    (m.enqueue w i b).abs = m.abs := by
  unfold enqueue; split <;> rfl

theorem abs_commit (m : Model sys) (i : σ.Id) (s : Slot sys i) (j : Job sys i) (now_ms : Nat) :
    (m.commit i s j now_ms).abs =
      { m.abs with
        state := update m.abs.state i (s.put now_ms (j.run m.clock)).1.cell.state
        up := update m.abs.up i (s.put now_ms (j.run m.clock)).1.cell.up
        timers := update m.abs.timers i ((s.put now_ms (j.run m.clock)).1.cell.timers.map (·.1))
        net := (if (j.run m.clock).2.any Effect.isStop then (m.base i j.work).filter (keep i)
          else m.base i j.work) ++ (s.put now_ms (j.run m.clock)).2.sends
        outbox := m.abs.outbox ++ (s.put now_ms (j.run m.clock)).2.outputs } := by
  refine SysState.ext' ?_ ?_ ?_ ?_ ?_
  · exact apply_update (fun _ (c : Slot sys _) => c.cell.state) m.slot i _
  · exact apply_update (fun _ (c : Slot sys _) => c.cell.up) m.slot i _
  · rfl
  · exact apply_update (fun _ (c : Slot sys _) => c.cell.timers.map (·.1)) m.slot i _
  · rfl

/-- The head of a mailbox is the oldest message on its link, so the semantics may deliver it. -/
theorem deliverable_head (h : m.Coherent) {i : σ.Id} {src : Option σ.Id} {msg : σ.Msg i}
    {rest : Fifo (Item σ i)} (hpop : (m.slot i).mail.pop? = some (.msg src msg, rest)) :
    m.net.filter (onLink src i) = ⟨src, i, msg⟩ :: (mailEnvs i src rest.toList
      ++ (pend m.out src).filter (onLink src i)) := by
  rw [h src i, Fifo.toList_of_pop? hpop, mailEnvs_msg]
  simp

/-- One step of a worker is the semantics' event for it: a delivery, a start or a timer. -/
theorem step_event (henv : Reliable env) (h : m.Coherent) {i : σ.Id} {j : Job sys i}
    {s : Slot sys i} (now_ms : Nat) (htake : (m.slot i).take = (.job j, s)) :
    m.abs.step env j.work.event = some (m.commit i s j now_ms).abs := by
  obtain ⟨hstate, -, hcase⟩ := Slot.take_eq_job htake
  rcases hcase with ⟨src, msg, rest, hw, hpop, hup, -, hup', htimers⟩
      | ⟨src, msg, rest, hw, hpop, hup, -, hup', htimers⟩
      | ⟨msg, due, rest, hw, hpop, hup, hmem, -, hup', htimers⟩
  · have hhead := deliverable_head h hpop
    rw [hw]
    apply SysState.step_deliver.mpr
    refine ⟨by simpa [abs] using hup, ?_, ?_⟩
    · have hlink : (⟨src, i, msg⟩ : Envelope σ).sameLink = onLink src i := by
        funext x
        simp only [Envelope.sameLink, onLink]
        congr 1 <;> exact decide_eq_decide.mpr eq_comm
      simp [SysState.deliverable, show ∀ a b, env.link a b = Link.reliable from henv, Link.reliable, abs, hlink, ← List.head?_filter,
        hhead]
    · have hrun : (sys.actor i).stepAt { toMoment := m.abs.clock, src := .ofSrc src }
          (m.abs.state i) msg = (j.run m.clock) := by
        simp [Job.run, hw, hstate, abs]
      rw [abs_commit, SysState.handle]
      obtain ⟨hset, -⟩ := Slot.put_settle now_ms (j.run m.clock) s { m.abs with net := m.abs.net.erase ⟨src, i, msg⟩ }
        (by simp [abs, htimers]) (by simp [abs, hup, hup']) henv
      simp only at hset ⊢
      rw [hrun, hset]
      simp [base, hw, abs]
  · rw [hw]
    apply SysState.step_start.mpr
    refine ⟨by simpa [abs] using hup, .inl ?_, ?_⟩
    · have hhead := deliverable_head h hpop
      have hmem : (⟨src, i, msg⟩ : Envelope σ) ∈ m.net := by
        have : (⟨src, i, msg⟩ : Envelope σ) ∈ m.net.filter (onLink src i) := by simp [hhead]
        exact (List.mem_filter.mp this).1
      simp only [SysState.hasMail, abs, List.any_eq_true, decide_eq_true_eq]
      exact ⟨_, hmem, rfl⟩
    · have hrun : (sys.actor i).recoverAt m.abs.clock (m.abs.state i) = (j.run m.clock) := by
        simp [Job.run, hw, hstate, abs]
      rw [abs_commit, SysState.startActor]
      obtain ⟨hset, -⟩ := Slot.put_settle now_ms (j.run m.clock) s { m.abs with up := update m.abs.up i true }
        (by simp [abs, htimers]) (by simp [abs, hup']) henv
      simp only at hset ⊢
      rw [hrun, hset]
      apply SysState.ext' <;> simp [base, hw, abs, update_update]
  · rw [hw]
    apply SysState.step_timeout.mpr
    refine ⟨by simpa [abs] using hup, ?_, ?_⟩
    · simp only [abs, List.mem_map]
      exact ⟨(msg, due), hmem, rfl⟩
    · have hrun : (sys.actor i).stepAt { toMoment := m.abs.clock, src := .timer }
          (m.abs.state i) msg = (j.run m.clock) := by
        simp [Job.run, hw, hstate, abs]
      rw [abs_commit, SysState.handle]
      obtain ⟨hset, -⟩ := Slot.put_settle now_ms (j.run m.clock) s
        { m.abs with timers := update m.abs.timers i ((m.abs.timers i).erase msg) }
        (by simp [abs, htimers, map_fst_eraseP]) (by simp [abs, hup, hup']) henv
      simp only at hset ⊢
      rw [hrun, hset]
      apply SysState.ext' <;> simp [base, hw, abs, update_update]

end Model

namespace Model

variable {m : Model sys}

theorem Placed.congr {m' : Model sys} (h : m.Placed) (hslot : m'.slot = m.slot)
    (hholding : m'.holding = m.holding) (hqueue : m'.queue = m.queue) : m'.Placed :=
  h.of_status hholding hqueue (by simp [hslot]) (by simp [hslot])

theorem Placed.begin (h : m.Placed) {w : Nat} {i : σ.Id} {rest : List σ.Id}
    (hhold : m.holding w = none) (hq : m.queue w = i :: rest) :
    (m.beginAt w i rest).Placed := by
  have hrest : ∀ k, k ≠ i → ∀ v, k ∈ m.queue v → k ∈ update m.queue w rest v := by
    intro k hk v hv
    by_cases hvw : v = w
    · subst hvw; simp only [update_self]; rw [hq] at hv; simpa [hk] using hv
    · simpa [hvw] using hv
  by_cases hqd : (m.slot i).status = .queued
  · simp only [beginAt, Slot.begin, hqd, ite_true]
    have hnot : ∀ v, m.holding v ≠ some i := fun v hv => by
      have := (h.held i).mpr ⟨v, hv⟩; simp_all
    have hstatus : ∀ k, (update m.slot i { (m.slot i) with status := .running } k).status
        = if k = i then .running else (m.slot k).status := by
      intro k; by_cases hk : k = i
      · subst hk; simp
      · simp [hk]
    refine ⟨fun k => ?_, fun v u k hv hu => ?_, fun k hk => ?_, fun k hk => ?_⟩
    · simp only [setSlot_slot, hstatus]
      by_cases hk : k = i
      · subst hk; simp only [ite_true, true_iff]; exact ⟨w, by simp⟩
      · simp only [hk, ite_false]
        rw [h.held k]
        constructor
        · rintro ⟨v, hv⟩
          refine ⟨v, ?_⟩
          by_cases hvw : v = w
          · subst hvw; simp_all
          · simpa [hvw] using hv
        · rintro ⟨v, hv⟩
          by_cases hvw : v = w
          · subst hvw; simp at hv; exact absurd hv.symm hk
          · exact ⟨v, by simpa [hvw] using hv⟩
    · by_cases hvw : v = w <;> by_cases huw : u = w
      · rw [hvw, huw]
      · subst hvw; simp at hv; subst hv
        exact absurd (by simpa [huw] using hu) (hnot u)
      · subst huw; simp at hu; subst hu
        exact absurd (by simpa [hvw] using hv) (hnot v)
      · exact h.unique v u k (by simpa [hvw] using hv) (by simpa [huw] using hu)
    · simp only [setSlot_slot, hstatus] at hk ⊢
      by_cases hki : k = i
      · subst hki; simp at hk
      · simp only [hki, ite_false] at hk; simpa [hki] using h.idle k hk
    · simp only [setSlot_slot, hstatus] at hk
      by_cases hki : k = i
      · subst hki; simp at hk
      · simp only [hki, ite_false] at hk
        obtain ⟨v, hv⟩ := h.queued k hk
        exact ⟨v, hrest k hki v hv⟩
  · simp only [beginAt, Slot.begin, hqd, ite_false]
    refine ⟨fun k => h.held k, fun v u k => h.unique v u k, fun k hk => h.idle k hk,
      fun k hk => ?_⟩
    by_cases hki : k = i
    · subst hki; exact absurd hk hqd
    · obtain ⟨v, hv⟩ := h.queued k hk
      exact ⟨v, hrest k hki v hv⟩

end Model


namespace Model

variable {m : Model sys}

theorem Placed.steal (h : m.Placed) {w v : Nat} {i : σ.Id} {rest : List σ.Id}
    (hq : m.queue v = i :: rest) :
    ({ m with queue := update (update m.queue v rest) w (update m.queue v rest w ++ [i]) }
      : Model sys).Placed := by
  refine ⟨h.held, h.unique, h.idle, fun k hk => ?_⟩
  obtain ⟨u, hu⟩ := h.queued k hk
  by_cases hki : k = i
  · subst hki; exact ⟨w, by simp⟩
  · refine ⟨u, ?_⟩
    have hmid : k ∈ update m.queue v rest u := by
      by_cases huv : u = v
      · subst huv; rw [hq] at hu; simpa [hki] using hu
      · simpa [huv] using hu
    by_cases huw : u = w
    · subst huw; simp [hmid]
    · simpa [huw] using hmid

theorem Placed.release (h : m.Placed) {w : Nat} {i : σ.Id} (hhold : m.holding w = some i) :
    (match (m.slot i).release with
     | (b, s) => ({ m.setSlot i s with holding := update m.holding w none }).enqueue w i b).Placed := by
  rcases hr : (m.slot i).release with ⟨b, s⟩
  have hs : s.status = (if (m.slot i).mail.isEmpty then .idle else .queued)
      ∧ s.mail = (m.slot i).mail ∧ b = !(m.slot i).mail.isEmpty := by
    unfold Slot.release at hr
    split at hr <;> cases hr <;> simp_all
  obtain ⟨hst, hmail, hb⟩ := hs
  simp only
  have hstatus : ∀ k, (update m.slot i s k).status = if k = i then s.status else (m.slot k).status := by
    intro k; by_cases hk : k = i
    · subst hk; simp
    · simp [hk]
  refine ⟨fun k => ?_, fun v u k hv hu => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · simp only [enqueue_slot, enqueue_holding, setSlot_slot, hstatus]
    by_cases hki : k = i
    · subst hki
      simp only [ite_true, hst]
      have hfalse : ¬ (if (m.slot k).mail.isEmpty then Status.idle else .queued) = .running := by
        split <;> simp
      simp only [hfalse, false_iff, not_exists]
      intro u hu
      by_cases huw : u = w
      · subst huw; simp at hu
      · exact huw (h.unique u w k (by simpa [huw] using hu) hhold)
    · simp only [hki, ite_false]
      rw [h.held k]
      constructor
      · rintro ⟨u, hu⟩
        refine ⟨u, ?_⟩
        by_cases huw : u = w
        · subst huw; rw [hhold] at hu; cases hu; exact absurd rfl hki
        · simpa [huw] using hu
      · rintro ⟨u, hu⟩
        by_cases huw : u = w
        · subst huw; simp at hu
        · exact ⟨u, by simpa [huw] using hu⟩
  · simp only [enqueue_holding] at hv hu
    have hv' : m.holding v = some k := by
      by_cases hvw : v = w
      · subst hvw; simp at hv
      · simpa [hvw] using hv
    have hu' : m.holding u = some k := by
      by_cases huw : u = w
      · subst huw; simp at hu
      · simpa [huw] using hu
    exact h.unique v u k hv' hu'
  · simp only [enqueue_slot, setSlot_slot, hstatus] at hk ⊢
    by_cases hki : k = i
    · subst hki
      simp only [ite_true, hst] at hk
      simp only [update_self, hmail]
      split at hk
      · next he => exact (Fifo.isEmpty_iff _).mp he
      · cases hk
    · simp only [hki, ite_false] at hk
      simpa [hki] using h.idle k hk
  · simp only [enqueue_slot, setSlot_slot, hstatus] at hk
    rw [enqueue_queue]
    by_cases hki : k = i
    · subst hki
      simp only [ite_true, hst] at hk
      split at hk
      · cases hk
      · next he =>
        have : b = true := by simp [hb, he]
        exact ⟨w, by simp [this]⟩
    · simp only [hki, ite_false] at hk
      obtain ⟨u, hu⟩ := h.queued k hk
      refine ⟨u, ?_⟩
      split
      · by_cases huw : u = w
        · subst huw; simp [hu]
        · simpa [huw] using hu
      · exact hu

end Model

/-! The start: every actor of `sys.boot` started in order, what each sent pushed at once. -/

namespace Model


theorem abs_blank (sys : System σ) : (blank sys).abs = SysState.blank sys := rfl

theorem abs_drain (m : Model sys) (i : σ.Id) (n : Nat) : (m.drain i n).abs = m.abs := by
  induction n generalizing m with
  | zero => rfl
  | succ n ih =>
    unfold drain
    split
    · rfl
    · rw [ih]; simp only [sendOne, abs_pushTo]; rfl

/-- What draining keeps: the invariant, outside the messages not pushed, which it pushes. -/
theorem drain_inv (m : Model sys) (i : σ.Id) (n : Nat) (hc : m.Coherent) (hs : m.OutSrc)
    (hp : m.Placed) :
    (m.drain i n).Coherent ∧ (m.drain i n).OutSrc ∧ (m.drain i n).Placed
      ∧ (∀ k, k ≠ i → (m.drain i n).out k = m.out k)
      ∧ ((m.out i).length ≤ n → (m.drain i n).out i = []) := by
  induction n generalizing m with
  | zero =>
    refine ⟨hc, hs, hp, fun _ _ => rfl, fun h => ?_⟩
    exact List.eq_nil_of_length_eq_zero (Nat.le_zero.mp h)
  | succ n ih =>
    unfold drain
    split
    · next hout => exact ⟨hc, hs, hp, fun _ _ => rfl, fun _ => hout⟩
    · next e rest hout =>
      have hc' := hc.sendOne hs hout 0
      have hs' : (m.sendOne i e rest 0).OutSrc := by
        intro k e' he'
        simp only [sendOne, pushTo_out] at he'
        by_cases hk : k = i
        · subst hk; exact hs k e' (by simp [hout, by simpa using he'])
        · exact hs k e' (by simpa [hk] using he')
      have hp' := (hp.congr (m' := { m with out := update m.out i rest }) rfl rfl rfl).pushTo
        e.dst (.msg (some i) e.msg) 0
      obtain ⟨h1, h2, h3, h4, h5⟩ := ih _ hc' hs' hp'
      refine ⟨h1, h2, h3, fun k hk => ?_, fun hlen => h5 ?_⟩
      · rw [h4 k hk]; simp [sendOne, hk]
      · simp only [sendOne, pushTo_out, update_self]
        rw [hout] at hlen
        simpa using hlen

theorem abs_bootOne (henv : Reliable env) (m : Model sys) (i : σ.Id) :
    (m.bootOne i).abs = m.abs.startActor env i := by
  unfold bootOne
  simp only [abs_drain]
  rw [abs_commit, SysState.startActor]
  obtain ⟨hset, -⟩ := Slot.put_settle 0 ((⟨.start, (m.slot i).cell.state⟩ : Job sys i).run m.clock)
    { (m.slot i) with cell := { (m.slot i).cell with up := true } }
    { m.abs with up := update m.abs.up i true } (by simp [abs]) (by simp [abs]) henv
  have hrun : (sys.actor i).recoverAt m.abs.clock (m.abs.state i)
      = (⟨.start, (m.slot i).cell.state⟩ : Job sys i).run m.clock := rfl
  rw [hrun, hset]
  apply SysState.ext' <;> simp [base, abs, update_update]

theorem bootOne_inv (m : Model sys) (i : σ.Id) (hc : m.Coherent)
    (hp : m.Placed) (hout : ∀ k, m.out k = []) :
    (m.bootOne i).Coherent ∧ (m.bootOne i).OutSrc ∧ (m.bootOne i).Placed
      ∧ ∀ k, (m.bootOne i).out k = [] := by
  let s : Slot sys i := { (m.slot i) with cell := { (m.slot i).cell with up := true } }
  let j : Job sys i := ⟨.start, (m.slot i).cell.state⟩
  obtain ⟨-, -, hst, hmail, hsends⟩ :=
    Slot.put_settle 0 (j.run m.clock) s (m.setSlot i s).abs (by simp [abs, s]) (by simp [abs, s])
      kernel_reliable
  have hc1 : (m.commit i s j 0).Coherent := by
    refine coherent_commit ?_ 0 (hout i) (fun _ k e he => by simp [hout k] at he)
    exact (hc.setSlot (s := s) rfl).of_mail (by simp [base, j]) rfl fun _ _ => rfl
  have hs1 : (m.commit i s j 0).OutSrc := by
    intro k e he
    by_cases hk : k = i
    · subst hk; exact (hsends e (by simpa [commit] using he)).1
    · simp [commit, hk, hout k] at he
  have hp1 : (m.commit i s j 0).Placed := by
    refine hp.of_status rfl rfl (fun k => ?_) (fun k hk => ?_)
    · by_cases hk : k = i
      · subst hk; simp [commit, hst, s]
      · simp [commit, hk]
    · by_cases hki : k = i
      · subst hki
        have hempty := hp.idle k hk
        simp only [commit, update_self, hmail]
        split <;> simp [hempty, s]
      · simp [commit, hki]
  obtain ⟨h1, h2, h3, h4, h5⟩ := drain_inv _ i ((m.commit i s j 0).out i).length hc1 hs1 hp1
  refine ⟨h1, h2, h3, fun k => ?_⟩
  change ((m.commit i s j 0).drain i ((m.commit i s j 0).out i).length).out k = []
  by_cases hk : k = i
  · subst hk; exact h5 (Nat.le_refl _)
  · rw [h4 k hk]; simp [commit, hk, hout k]

theorem init_spec (sys : System σ) (henv : Reliable env) :
    (init sys).abs = SysState.init sys env ∧ (init sys).Inv := by
  suffices h : ∀ (l : List σ.Id) (m : Model sys), m.Coherent → m.OutSrc → m.Placed →
      (∀ k, m.out k = []) →
      (l.foldl bootOne m).abs = l.foldl (fun c i => c.startActor env i) m.abs
        ∧ (l.foldl bootOne m).Inv by
    obtain ⟨h1, h2⟩ := h sys.boot (blank sys)
      (fun src dst => by cases src <;> simp [blank, pend, Slot.fresh])
      (fun _ _ he => by simp [blank] at he)
      ⟨fun k => by simp [blank, Slot.fresh], fun _ _ _ h => by simp [blank] at h,
        fun k _ => by simp [blank, Slot.fresh], fun k h => by simp [blank, Slot.fresh] at h⟩
      (fun _ => rfl)
    exact ⟨h1, h2⟩
  intro l
  induction l with
  | nil => intro m hc hs hp _; exact ⟨rfl, hc, hs, hp⟩
  | cons i l ih =>
    intro m hc hs hp hout
    obtain ⟨hc', hs', hp', hout'⟩ := bootOne_inv m i hc hp hout
    obtain ⟨h1, h2⟩ := ih (m.bootOne i) hc' hs' hp' hout'
    refine ⟨?_, h2⟩
    simp only [List.foldl_cons]
    rw [h1, abs_bootOne henv]

end Model

/-- Every transition of the scheduler is no event of the semantics, one, or for a step the
moment it is told and the step, from the state it stands for to the state it leads to. -/
theorem Step.sound (henv : Reliable env) {m m' : Model sys} {ev : List (Event σ)}
    (hr : .restart ∈ ev → env.mayRestart = true)
    (hinv : m.Inv) (h : Step m ev m') : m.abs.run env ev = some m'.abs := by
  cases h with
  | input x w =>
    simp only [SysState.run, SysState.step, Option.bind_some, Model.abs_input]
  | ring i msg due w => simp [SysState.run]
  | begin w i rest hhold hq =>
    simp only [SysState.run, Option.some.injEq, Model.beginAt]
    rcases hb : (m.slot i).begin with ⟨b, s⟩
    have hcell : s.cell = (m.slot i).cell := by simpa [hb] using Slot.begin_cell (m.slot i)
    cases b
    · rfl
    · exact (Model.abs_setSlot hcell).symm
  | steal w v i rest hq => rfl
  | step w i t j s hhold hout htake hstop =>
    have hc : ({ m with clock := t } : Model sys).Coherent := hinv.coherent
    have hstep := Model.step_event henv hc t.now_ms (m := { m with clock := t }) htake
    simp only [SysState.run, SysState.step, Option.bind_some]
    exact (congrArg (·.bind fun c => c.run env []) hstep).trans rfl
  | stale w i s hhold hout htake =>
    obtain ⟨-, -, -, hcell, -⟩ := Slot.take_eq_stale htake
    simp only [SysState.run, Option.some.injEq]
    exact (Model.abs_setSlot hcell).symm
  | send w i e rest hhold hout =>
    simp only [SysState.run, Option.some.injEq, Model.sendOne, Model.abs_pushTo]
    rfl
  | release w i hhold hout =>
    simp only [SysState.run, Option.some.injEq]
    rcases hr : (m.slot i).release with ⟨b, s⟩
    have hcell : s.cell = (m.slot i).cell := by simpa [hr] using Slot.release_cell (m.slot i)
    simp only [Model.abs_enqueue]
    exact (Model.abs_setSlot hcell).symm
  | handOver out hmem =>
    simp [SysState.run, SysState.step, Model.abs, hmem]
  | restart =>
    simp [SysState.run, SysState.step, hr (by simp), (Model.init_spec sys henv).1]


/-- Every transition keeps the invariant. -/
theorem Step.inv {m m' : Model sys} {ev : List (Event σ)} (hinv : m.Inv)
    (h : Step m ev m') : m'.Inv := by
  obtain ⟨hcoh, hsrc, hpl⟩ := hinv
  cases h with
  | input x w =>
    refine ⟨hcoh.input x w, ?_, ?_⟩
    · unfold Model.input; split; intro j e he; exact hsrc j e (by simpa using he)
    · unfold Model.input; split
      exact (hpl.pushTo _ _ w).congr rfl rfl rfl
  | ring i msg due w =>
    exact ⟨hcoh.pushTimer i msg due w, fun j e he => hsrc j e (by simpa using he),
      hpl.pushTo i _ w⟩
  | begin w i rest hhold hq =>
    refine ⟨?_, ?_, hpl.begin hhold hq⟩
    · unfold Model.beginAt
      rcases hb : (m.slot i).begin with ⟨b, s⟩
      cases b
      · exact hcoh.of_mail rfl rfl fun _ _ => rfl
      · have hmail : s.mail = (m.slot i).mail := by simpa [hb] using Slot.begin_mail (m.slot i)
        exact (hcoh.setSlot (by rw [hmail])).of_mail rfl rfl fun _ _ => rfl
    · unfold Model.beginAt
      rcases (m.slot i).begin with ⟨b, s⟩
      cases b <;> exact hsrc
  | steal w v i rest hq =>
    exact ⟨hcoh.of_mail rfl rfl fun _ _ => rfl, hsrc, hpl.steal hq⟩
  | step w i t j s hhold hout htake hstop =>
    obtain ⟨-, hst, -⟩ := Slot.take_eq_job htake
    obtain ⟨-, -, hst', -, hsends⟩ :=
      Slot.put_settle t.now_ms (j.run t) s (m.setSlot i s).abs (by simp [Model.abs])
        (by simp [Model.abs]) kernel_reliable
    have hrun := Model.running_of_holding hpl hhold
    have hc : ({ m with clock := t } : Model sys).Coherent := hcoh
    refine ⟨Model.coherent_commit (m := { m with clock := t }) (hc.take htake) t.now_ms hout hstop,
      ?_, ?_⟩
    · intro k e he
      by_cases hk : k = i
      · subst hk; exact (hsends e (by simpa [Model.commit] using he)).1
      · exact hsrc k e (by simpa [Model.commit, hk] using he)
    · refine hpl.of_status rfl rfl (fun k => ?_) (fun k hk => ?_)
      · by_cases hk : k = i
        · subst hk; simp [Model.commit, hst', hst]
        · simp [Model.commit, hk]
      · have hki : k ≠ i := fun hki => by subst hki; simp_all
        simp [Model.commit, hki]
  | stale w i s hhold hout htake =>
    obtain ⟨-, -, -, -, hst⟩ := Slot.take_eq_stale htake
    have hrun := Model.running_of_holding hpl hhold
    refine ⟨hcoh.stale htake, hsrc, hpl.of_status rfl rfl (fun k => ?_) (fun k hk => ?_)⟩
    · by_cases hk : k = i
      · subst hk; simp [hst]
      · simp [hk]
    · have hki : k ≠ i := fun hki => by subst hki; simp_all
      simp [hki]
  | send w i e rest hhold hout =>
    refine ⟨hcoh.sendOne hsrc hout w, fun k e' he' => ?_, ?_⟩
    · simp only [Model.sendOne, Model.pushTo_out] at he'
      by_cases hk : k = i
      · subst hk; exact hsrc k e' (by simp [hout, by simpa using he'])
      · exact hsrc k e' (by simpa [hk] using he')
    · exact (hpl.congr (m' := { m with out := update m.out i rest }) rfl rfl rfl).pushTo _ _ w
  | release w i hhold hout =>
    refine ⟨?_, ?_, hpl.release hhold⟩
    · rcases hr : (m.slot i).release with ⟨b, s⟩
      have hmail : s.mail = (m.slot i).mail := by simpa [hr] using Slot.release_mail (m.slot i)
      exact (hcoh.setSlot (by rw [hmail])).of_mail (by simp) (by simp) fun _ _ => by simp
    · rcases (m.slot i).release with ⟨b, s⟩
      exact fun j e he => hsrc j e (by simpa using he)
  | handOver out hmem =>
    exact ⟨hcoh.of_mail rfl rfl fun _ _ => rfl, hsrc, hpl.congr rfl rfl rfl⟩
  | restart => exact (Model.init_spec sys (env := Kernel.env) kernel_reliable).2


theorem Run.sound (henv : Reliable env) {m m' : Model sys} {evs : List (Event σ)}
    (hr : .restart ∈ evs → env.mayRestart = true) (hinv : m.Inv) (h : Run m evs m') :
    m.abs.run env evs = some m'.abs ∧ m'.Inv := by
  induction h with
  | refl => exact ⟨rfl, hinv⟩
  | @step m₁ m₂ m₃ ev evs hstep _ ih =>
    obtain ⟨hrun, hinv'⟩ := ih (fun h => hr (List.mem_append_right _ h)) (Step.inv hinv hstep)
    refine ⟨?_, hinv'⟩
    rw [SysState.run_append, Step.sound henv (fun h => hr (List.mem_append_left _ h)) hinv hstep]
    exact hrun

/--
Every run of the scheduler from its start is a run of the semantics under every environment
whose links are reliable (`Kernel.env` among them) and which allows process restarts if the run
has one: the events its transitions are, in order, lead from `SysState.init` to the state the
scheduler stands for, which the semantics therefore reaches. The outputs it handed over are that
run's outputs (`Event.outputs`), and the invariant holds all along.
-/
theorem Run.reachable (henv : Reliable env) {m : Model sys} {evs : List (Event σ)}
    (hr : .restart ∈ evs → env.mayRestart = true) (h : Run (Model.init sys) evs m) :
    (SysState.init sys env).run env evs = some m.abs
      ∧ sys.Reachable env m.abs ∧ m.Inv := by
  obtain ⟨habs, hinv⟩ := Model.init_spec sys henv
  obtain ⟨hrun, hinv'⟩ := Run.sound henv hr hinv h
  rw [habs] at hrun
  exact ⟨hrun, System.Reachable.init.run hrun, hinv'⟩

/-! The step function runs outside the slot's lock: between `take` and `put` only pushes reach
the slot, and they commute with both. -/

namespace Slot

variable {i : σ.Id}

/-- Two slots that differ at most in how their mailboxes' queues are laid out. -/
def Same (a b : Slot sys i) : Prop :=
  a.cell = b.cell ∧ a.status = b.status ∧ a.nextToken = b.nextToken
    ∧ a.mail.toList = b.mail.toList

theorem push_of_ne_idle {s : Slot sys i} (x : Item σ i) (hst : s.status ≠ .idle) :
    (s.push x).2 = { s with mail := s.mail.push x } := by
  simp [push, hst]

/-- A push to the actor while a worker steps it does not change what the worker took. -/
theorem take_push {s : Slot sys i} (x : Item σ i) (hst : s.status ≠ .idle)
    (hne : s.mail.toList ≠ []) :
    ((s.push x).2.take).1 = (s.take).1 ∧ Same ((s.push x).2.take).2 ((s.take).2.push x).2 := by
  rw [push_of_ne_idle x hst]
  cases hpop : s.mail.pop? with
  | none => exact absurd (Fifo.pop?_eq_none.mp hpop) hne
  | some p =>
    obtain ⟨a, rest⟩ := p
    have hl := Fifo.toList_of_pop? hpop
    cases hpop' : (s.mail.push x).pop? with
    | none =>
      have := Fifo.pop?_eq_none.mp hpop'
      simp [hl] at this
    | some p' =>
      obtain ⟨a', rest'⟩ := p'
      have hl' := Fifo.toList_of_pop? hpop'
      rw [Fifo.toList_push, hl] at hl'
      simp only [List.cons_append, List.cons.injEq] at hl'
      obtain ⟨rfl, hrest⟩ := hl'
      cases a with
      | msg src m =>
        by_cases hup : s.cell.up = true
        · simp only [take, hpop, hpop', hup, ite_true]
          exact ⟨by simp, by simp [Same, push, hst, hrest]⟩
        · simp only [take, hpop, hpop', hup, Bool.false_eq_true, ite_false]
          exact ⟨by simp, by simp [Same, push, hst]⟩
      | timer m due =>
        by_cases hok : (s.cell.up && s.cell.timers.contains (m, due)) = true
        · simp only [take, hpop, hpop', hok, ite_true]
          exact ⟨by simp, by simp [Same, push, hst, hrest]⟩
        · simp only [take, hpop, hpop', hok, Bool.false_eq_true, ite_false]
          exact ⟨by simp, by simp [Same, push, hst, hrest]⟩

theorem perform_fold_mail (now_ms : Nat) (effs : List (Effect σ i)) :
    ∀ (s : Slot sys i) (c : Commit σ i) (q : Fifo (Item σ i)),
      effs.foldl (perform now_ms) ({ s with mail := q }, c)
        = ({ (effs.foldl (perform now_ms) (s, c)).1 with mail := q },
            (effs.foldl (perform now_ms) (s, c)).2) := by
  induction effs with
  | nil => intro s c q; rfl
  | cons eff effs ih =>
    intro s c q
    cases eff <;> simp only [List.foldl_cons, perform] <;> rw [← ih] <;> rfl

/-- A push to the actor while a worker steps it is as if it came before the step: kept, or
dropped with the actor's mail if the step stops it. -/
theorem put_push (now_ms : Nat) (r : sys.State i × List (Effect σ i)) {s : Slot sys i}
    (x : Item σ i) (hst : s.status ≠ .idle) :
    ((s.push x).2.put now_ms r).1
      = if r.2.any Effect.isStop then (s.put now_ms r).1 else ((s.put now_ms r).1.push x).2 := by
  rw [push_of_ne_idle x hst, put_eq, put_eq]
  let s0 : Slot sys i := { s with cell := { s.cell with state := r.1 } }
  have h := perform_fold_mail now_ms r.2 s0 {} (s.mail.push x)
  let t0 := update (SysState.blank sys).timers i (s0.cell.timers.map (·.1))
  let c0 : SysState sys := { SysState.blank sys with timers := t0 }
  obtain ⟨-, -, -, hmail, hstatus, -⟩ :=
    perform_fold now_ms r.2 s0 {} c0 (by simp [c0, t0])
  rw [show ({ ({ s with mail := s.mail.push x } : Slot sys i) with
      cell := { s.cell with state := r.1 } } : Slot sys i) = { s0 with mail := s.mail.push x }
      from rfl, h]
  rcases hf : r.2.foldl (perform now_ms) (s0, {}) with ⟨s1, c⟩
  rw [hf] at hmail hstatus
  simp only at hmail hstatus ⊢
  by_cases hstop : r.2.any Effect.isStop = true
  · simp [hstop, down]
  · simp only [hstop, Bool.false_eq_true, ite_false]
    have hst1 : s1.status ≠ .idle := by rw [hstatus]; exact hst
    rw [push_of_ne_idle x hst1, hmail]

end Slot

/-! The ledger's bounds. They are not in the model: an input refused is no event, and the only
thing the runtime does past the mail's capacity, by default, is the model's restart. These say
that the ledger decides as the shell's documentation says. -/

namespace Ledger

variable {W I : Type}

/-- An input is taken only while fewer than `capacity` inputs wait, the mail between actors is
below `highWater` and the ledger is open; taking it leaves the mail as it was. -/
theorem offer_taken {capacity highWater : Nat} {l : Ledger W I}
    (h : (l.offer capacity highWater).1 = .taken) :
    l.closed = false ∧ l.inputs < capacity ∧ l.mail < highWater
      ∧ (l.offer capacity highWater).2.inputs = l.inputs + 1
      ∧ (l.offer capacity highWater).2.mail = l.mail := by
  unfold offer at h ⊢
  by_cases hc : l.closed = true
  · simp [hc] at h
  · by_cases hroom : l.inputs < capacity ∧ l.mail < highWater
    · refine ⟨by simpa using hc, hroom.1, hroom.2, ?_, ?_⟩
      · simp [hc, hroom]
      · have hm := hroom.2
        simp only [mail] at hm
        simp only [hc, hroom.1, hm, mail, decide_true, Bool.and_self, ite_true, Bool.false_eq_true,
          ite_false]
        omega
    · have hno : (decide (l.inputs < capacity) && decide (l.mail < highWater)) = false := by
        simpa using hroom
      simp [hc, hno] at h

/-- An input refused leaves no trace: the ledger is as it was. -/
theorem offer_refused {capacity highWater : Nat} {l : Ledger W I}
    (h : (l.offer capacity highWater).1 ≠ .taken) : (l.offer capacity highWater).2 = l := by
  unfold offer at h ⊢
  by_cases hc : l.closed = true
  · simp [hc]
  · by_cases hroom : (decide (l.inputs < capacity) && decide (l.mail < highWater)) = true
    · simp [hc, hroom] at h
    · simp [hc, hroom]

/-- At or past the high-water mark, no input is taken. -/
theorem offer_of_mail {capacity highWater : Nat} {l : Ledger W I} (h : highWater ≤ l.mail) :
    (l.offer capacity highWater).1 ≠ .taken := fun ht => by
  have := (offer_taken ht).2.2.1
  omega

/-- A step's sends are reported exactly when they leave the mail past the capacity. -/
theorem sent_over (n freed capacity : Nat) (l : Ledger W I) :
    (l.sent n freed capacity).1.2 = if capacity < (l.sent n freed capacity).2.mail then
      some (l.sent n freed capacity).2.mail else none := rfl

/-- The senders that waited are woken when steps bring the mail from at or past the high-water
mark to below it. -/
theorem done_wakes {highWater gone before after : Nat} {l : Ledger W I}
    (hwas : highWater ≤ l.mail) (hnow : (l.items - gone) - l.inputs < highWater) :
    (l.done highWater gone before after).1.1 = l.waiting := by
  unfold done
  simp only [mail] at hwas ⊢
  have : (l.items - gone) - l.inputs < highWater ∧ highWater ≤ l.items - l.inputs := ⟨hnow, hwas⟩
  simp [this]

/-- Counting a turn's new timers before the rest of it gives the ledger `done` gives: the shell
splits the turn so that whoever takes those timers next finds them counted. -/
theorem done_armed (highWater gone before after : Nat) (l : Ledger W I) :
    (l.armed (after - before)).done highWater gone (before - after) 0
      = l.done highWater gone before after := by
  have h : l.timers + (after - before) + 0 - (before - after) = l.timers + after - before := by
    omega
  simp only [done, armed, mail, h]
  rfl

end Ledger

end Lanes.Sched
