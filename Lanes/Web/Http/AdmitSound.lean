/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Core.Step
public import Lanes.Proof.List
public import Lanes.Web.Http.Admit
public import Lanes.Web.Http.FrontSound

/-!
# The gate before the runtime is the gate in the system

`Http.serve` makes the gate's decisions before the runtime (`Lanes.Web.Http.Admit`). This file
proves that nothing is lost by it: the gate keeps its three theorems, and a run of the front
with the runtime is a run of `served sys`, the system with the gate as an actor, with the same
requests arriving and the same answers handed over.

**The front alone.** The front is `Gate.step` folded over the messages it sees, with the
deadlines it arms (`Front`). It answers no request more often than it arrived
(`Front.run_answered_le`), its waiting list stays within `maxPending` and free of repeats
(`Front.run_bounded`), and every request that waits is answered, if every deadline that stays
armed is eventually passed to it (`Front.pending_answered`). The last is what the server's
ticker is trusted to do.

**The front with the runtime.** `Front.World` is what the server runs, as a transition system:
the front's state and its answers not yet handed over, beside the runtime's state, a state of
`admitted sys` under the kernel's environment (`EnvModel.reliable`). Its events are a request
arriving, a deadline passing, the front taking an output of the runtime, an answer handed over,
and the runtime's own events. `Front.World.refines` proves that every run of it is a run of
`served sys bridge config` under `Front.servedEnv`, with the same inputs and outputs in the
same order: the gate's waiting list and deadlines are the front's, the application's actors
have the same states, timers and messages, and the answers on their way to the gate are the
outputs the front has not yet taken. So every theorem about the runs of `served sys` holds of
the server (`Front.World.answered_le_arrived`).

`Front.servedEnv` is the kernel's environment but for one thing: the gate takes the system's
answers in any order, as the front takes the runtime's outputs. The entries are the runtime's
inputs: the requests the gate admitted, in the order it admitted them.
-/

@[expose] public section

namespace Lanes.Http

variable {σ : Signature}

/-! ## The front alone -/

namespace Gate

def Act.answers (id : ReqId) : Gate.Act σ → Bool
  | .respond i _ => i == id
  | _ => false

end Gate

def GateMsg.arrives (id : ReqId) : GateMsg σ → Bool
  | .arrive i _ => i == id
  | _ => false

/-- The front's state: the gate's waiting list, and the requests whose deadline is armed. -/
structure Front where
  pending : List ReqId := []
  armed : List ReqId := []

namespace Front

/-- What an act of the gate does to the deadlines. -/
def arm (armed : List ReqId) : Gate.Act σ → List ReqId
  | .arm id => if id ∈ armed then armed else armed ++ [id]
  | .disarm id => armed.erase id
  | _ => armed

/-- The front on `msg`: a deadline that passes is no longer armed, and the gate decides. -/
def step (bridge : Bridge σ) (config : GateConfig) (f : Front) (msg : GateMsg σ) :
    Front × List (Gate.Act σ) :=
  let armed := match msg with
    | .expire id => f.armed.erase id
    | _ => f.armed
  let r := Gate.step bridge config Gate.acts f.pending msg
  ({ pending := r.1, armed := r.2.foldl arm armed }, r.2)

/-- The front on messages in order: its state after them, and all it did. -/
def run (bridge : Bridge σ) (config : GateConfig) (f : Front) : List (GateMsg σ) →
    Front × List (Gate.Act σ)
  | [] => (f, [])
  | msg :: msgs =>
    let r := f.step bridge config msg
    let rs := run bridge config r.1 msgs
    (rs.1, r.2 ++ rs.2)

variable {bridge : Bridge σ} {config : GateConfig}

/-- One step answers `id` no more often than it handles an arrival of it, counting the times
`id` waits before and after. -/
theorem step_count (id : ReqId) (pending : List ReqId) (msg : GateMsg σ) :
    (Gate.step bridge config Gate.acts pending msg).1.count id
        + (Gate.step bridge config Gate.acts pending msg).2.countP (·.answers id)
      ≤ pending.count id + (msg.arrives id).toNat := by
  cases msg with
  | arrive i request =>
    simp only [Gate.step]
    split
    · simp
    · split
      · by_cases hid : i = id <;> simp [Gate.acts, Gate.Act.answers, GateMsg.arrives, hid]
      · split
        · by_cases hid : i = id <;> simp [Gate.acts, Gate.Act.answers, GateMsg.arrives, hid]
        · by_cases hid : i = id <;> simp [Gate.acts, Gate.Act.answers, GateMsg.arrives, hid]
  | answer out =>
    simp only [Gate.step]
    split
    · split
      · next i _ _ hi =>
        by_cases hid : i = id
        · subst hid
          have := List.count_pos_iff.mpr hi
          simp [Gate.acts, Gate.Act.answers, GateMsg.arrives, List.count_erase_self]
          omega
        · simp [Gate.acts, Gate.Act.answers, GateMsg.arrives, List.count_erase, hid]
      · simp
    · simp
  | expire i =>
    simp only [Gate.step]
    split
    · next hi =>
      by_cases hid : i = id
      · subst hid
        have := List.count_pos_iff.mpr hi
        simp [Gate.acts, Gate.Act.answers, GateMsg.arrives, List.count_erase_self]
        omega
      · simp [Gate.acts, Gate.Act.answers, GateMsg.arrives, List.count_erase, hid]
    · simp

theorem run_count (id : ReqId) (f : Front) (msgs : List (GateMsg σ)) :
    (f.run bridge config msgs).1.pending.count id
        + (f.run bridge config msgs).2.countP (·.answers id)
      ≤ f.pending.count id + msgs.countP (·.arrives id) := by
  induction msgs generalizing f with
  | nil => simp [run]
  | cons msg msgs ih =>
    have h1 := step_count (bridge := bridge) (config := config) id f.pending msg
    have h2 := ih (f.step bridge config msg).1
    simp only [run, List.countP_append, List.countP_cons] at h2 ⊢
    simp only [step] at h1 h2 ⊢
    cases h : msg.arrives id <;> simp [h] at h1 ⊢ <;> omega

/-- The front answers no request more often than it arrived. With the server's ids, which are
used once each, no request is answered twice. -/
theorem run_answered_le (id : ReqId) (msgs : List (GateMsg σ)) :
    (({} : Front).run bridge config msgs).2.countP (·.answers id)
      ≤ msgs.countP (·.arrives id) := by
  have := run_count (bridge := bridge) (config := config) id {} msgs
  simp at this
  omega

/-- The front's waiting list stays within `maxPending` and free of repeats. -/
theorem run_bounded (msgs : List (GateMsg σ)) {f : Front}
    (h : f.pending.length ≤ config.maxPending ∧ f.pending.Nodup) :
    (f.run bridge config msgs).1.pending.length ≤ config.maxPending
      ∧ (f.run bridge config msgs).1.pending.Nodup := by
  induction msgs generalizing f with
  | nil => exact h
  | cons msg msgs ih => exact ih (Gate.step_bounded bridge config Gate.acts msg h)

/-! Every request that waits is answered. -/

/-- What the front keeps: every waiting request has its deadline armed, and none waits twice. -/
def Inv (f : Front) : Prop :=
  f.pending.Nodup ∧ ∀ id ∈ f.pending, id ∈ f.armed

theorem mem_foldl_arm {armed : List ReqId} {id : ReqId} (h : id ∈ armed) :
    ∀ acts : List (Gate.Act σ), (∀ a ∈ acts, a ≠ .disarm id) → id ∈ acts.foldl arm armed := by
  intro acts
  induction acts generalizing armed with
  | nil => intro _; exact h
  | cons a acts ih =>
    intro hacts
    refine ih ?_ fun b hb => hacts b (List.mem_cons_of_mem _ hb)
    cases a with
    | arm i => simp only [arm]; split <;> simp [h]
    | disarm i =>
      have hne : i ≠ id := fun e => hacts _ List.mem_cons_self (by rw [e])
      exact (List.mem_erase_of_ne (Ne.symm hne)).mpr h
    | _ => exact h

theorem inv_step (msg : GateMsg σ) {f : Front} (h : f.Inv) : (f.step bridge config msg).1.Inv := by
  obtain ⟨hnodup, harmed⟩ := h
  cases msg with
  | arrive i request =>
    simp only [step, Gate.step]
    split
    · exact ⟨hnodup, harmed⟩
    · next hnew =>
      split
      · exact ⟨hnodup, fun id hid => mem_foldl_arm (harmed id hid) _ (by simp [Gate.acts])⟩
      · split
        · exact ⟨hnodup, fun id hid => mem_foldl_arm (harmed id hid) _ (by simp [Gate.acts])⟩
        · refine ⟨List.nodup_cons.mpr ⟨hnew, hnodup⟩, fun id hid => ?_⟩
          simp only [Gate.acts, List.foldl_cons, List.foldl_nil, arm]
          rcases List.mem_cons.mp hid with rfl | hid
          · split <;> simp_all
          · have := harmed id hid
            split <;> simp [this]
  | answer out =>
    simp only [step, Gate.step]
    split
    · split
      · next i _ _ _ =>
        refine ⟨hnodup.erase i, fun id hid => ?_⟩
        have hne : id ≠ i := fun e => by subst e; exact (List.Nodup.not_mem_erase hnodup) hid
        simp only [Gate.acts, List.foldl_cons, List.foldl_nil, arm]
        exact (List.mem_erase_of_ne hne).mpr (harmed id (List.mem_of_mem_erase hid))
      · exact ⟨hnodup, fun id hid => harmed id hid⟩
    · exact ⟨hnodup, fun id hid => harmed id hid⟩
  | expire i =>
    simp only [step, Gate.step]
    split
    · refine ⟨hnodup.erase i, fun id hid => ?_⟩
      have hne : id ≠ i := fun e => by subst e; exact (List.Nodup.not_mem_erase hnodup) hid
      simp only [Gate.acts, List.foldl_cons, List.foldl_nil, arm]
      exact (List.mem_erase_of_ne hne).mpr (harmed id (List.mem_of_mem_erase hid))
    · next hi =>
      refine ⟨hnodup, fun id hid => ?_⟩
      have hne : id ≠ i := fun e => by subst e; exact hi hid
      exact (List.mem_erase_of_ne hne).mpr (harmed id hid)

/-- A request waiting stays waiting through a step that does not answer it. -/
theorem stays (msg : GateMsg σ) {f : Front} {id : ReqId} (hid : id ∈ f.pending)
    (hno : ∀ r, Gate.Act.respond id r ∉ (f.step bridge config msg).2) :
    id ∈ (f.step bridge config msg).1.pending := by
  cases msg with
  | arrive i request =>
    simp only [step, Gate.step] at hno ⊢
    split
    · exact hid
    · split
      · exact hid
      · split
        · exact hid
        · exact List.mem_cons_of_mem _ hid
  | answer out =>
    simp only [step, Gate.step] at hno ⊢
    split
    · next i r heq =>
      rw [heq] at hno
      split
      · next hi =>
        simp only [hi, ↓reduceIte] at hno
        have hne : id ≠ i := fun e => by subst e; exact hno r (by simp [Gate.acts])
        exact (List.mem_erase_of_ne hne).mpr hid
      · exact hid
    · exact hid
  | expire i =>
    simp only [step, Gate.step] at hno ⊢
    split
    · next hi =>
      simp only [hi, ↓reduceIte] at hno
      have hne : id ≠ i := fun e => by subst e; exact hno timedOut (by simp [Gate.acts])
      exact (List.mem_erase_of_ne hne).mpr hid
    · exact hid

/-- A deadline passing for a request that waits answers it `504`. -/
theorem expire_answers {f : Front} {id : ReqId} (hid : id ∈ f.pending) :
    Gate.Act.respond id timedOut ∈ (f.step bridge config (.expire id)).2 := by
  simp [step, Gate.step, hid, Gate.acts]

/-- Every request that waits in the front is answered: in an endless sequence of messages from
a state where the front keeps `Inv`, if every deadline that stays armed is eventually passed to
the front, a later step answers the request. The server's ticker is trusted to pass every
deadline on once it is due. -/
theorem pending_answered (msgs : Nat → GateMsg σ) (fs : Nat → Front)
    (hstep : ∀ n, fs (n + 1) = ((fs n).step bridge config (msgs n)).1) (hinit : (fs 0).Inv)
    (hfair : ∀ n id, (∀ m, n ≤ m → id ∈ (fs m).armed) → ∃ m, n ≤ m ∧ msgs m = .expire id)
    {n : Nat} {id : ReqId} (hid : id ∈ (fs n).pending) :
    ∃ m, n ≤ m ∧ ∃ r, Gate.Act.respond id r ∈ ((fs m).step bridge config (msgs m)).2 := by
  have hinv : ∀ m, (fs m).Inv := by
    intro m
    induction m with
    | zero => exact hinit
    | succ m ih => rw [hstep]; exact inv_step _ ih
  apply Classical.byContradiction
  intro hnot
  have hno : ∀ m, n ≤ m → ∀ r, Gate.Act.respond id r ∉ ((fs m).step bridge config (msgs m)).2 :=
    fun m hm r hr => hnot ⟨m, hm, r, hr⟩
  have hwait : ∀ m, n ≤ m → id ∈ (fs m).pending := by
    intro m hm
    induction m with
    | zero => rwa [Nat.le_zero.mp hm] at hid
    | succ m ih =>
      rcases Nat.lt_or_ge m n with hlt | hge
      · rwa [show n = m + 1 by omega] at hid
      · rw [hstep]; exact stays _ (ih hge) (hno m hge)
  obtain ⟨m, hm, hexp⟩ := hfair n id fun m hm => (hinv m).2 id (hwait m hm)
  exact hno m hm timedOut (hexp ▸ expire_answers (hwait m hm))

end Front

/-! ## The front with the runtime -/

namespace Front

variable {sys : System σ} {bridge : Bridge σ} {config : GateConfig}

/-- What the server runs: the front, the answers it has given and not yet written, and the
runtime. -/
structure World (sys : System σ) (bridge : Bridge σ) where
  front : Front := {}
  answers : List (ReqId × Response) := []
  runtime : SysState (admitted sys bridge)

/-- What can happen to the server: a request arrives, a deadline passes, the front takes an
output of the runtime, an answer is written, or the runtime does something of its own. -/
inductive World.Event (σ : Signature) where
  | arrive (id : ReqId) (request : Request)
  | expire (id : ReqId)
  | take (out : σ.Out)
  | answer (answer : ReqId × Response)
  | runtime (ev : Lanes.Event (admittedSig σ))

namespace World

/-- Do one act of the gate. What it passes on is `entry`, the arrival it decided on, which
enters the runtime as an entry. -/
def act (entry : Option (ReqId × Request)) (w : World sys bridge) : Gate.Act σ → World sys bridge
  | .respond id response => { w with answers := w.answers ++ [(id, response)] }
  | .forward _ =>
    match entry with
    | some e =>
      { w with runtime := { w.runtime with net := w.runtime.net ++
          [⟨none, ((admitted sys bridge).accept e).1, ((admitted sys bridge).accept e).2⟩] } }
    | none => w
  | a => { w with front := { w.front with armed := arm w.front.armed a } }

/-- The gate decides on `msg` and the front does what it decided. -/
def decide (bridge : Bridge σ) (config : GateConfig) (w : World sys bridge) (msg : GateMsg σ)
    (entry : Option (ReqId × Request)) : World sys bridge :=
  let r := Gate.step bridge config Gate.acts w.front.pending msg
  r.2.foldl (act entry) { w with front := { w.front with pending := r.1 } }

/-- One event, or `none` if it is not enabled. The runtime runs under the kernel's environment. -/
def step (config : GateConfig) (w : World sys bridge) : World.Event σ → Option (World sys bridge)
  | .arrive id request => some (w.decide bridge config (.arrive id request) (some (id, request)))
  | .expire id =>
    if id ∈ w.front.armed then
      some ({ w with front := { w.front with armed := w.front.armed.erase id } }.decide bridge
        config (.expire id) none)
    else none
  | .take out =>
    if out ∈ w.runtime.outbox then
      some ({ w with runtime := { w.runtime with outbox := w.runtime.outbox.erase out } }.decide bridge
        config (.answer out) none)
    else none
  | .answer a => if a ∈ w.answers then some { w with answers := w.answers.erase a } else none
  | .runtime ev =>
    match ev with
    | .input _ | .output _ => none
    | ev => (w.runtime.step .reliable ev).map fun s => { w with runtime := s }

def run (config : GateConfig) (w : World sys bridge) :
    List (World.Event σ) → Option (World sys bridge)
  | [] => some w
  | ev :: evs => (w.step config ev).bind fun w' => w'.run config evs

def init (sys : System σ) (bridge : Bridge σ) : World sys bridge :=
  { runtime := SysState.init (admitted sys bridge) .reliable }

/-- What the outside sees of an event: a request arriving and an answer written. -/
def Event.visible : World.Event σ → Option (Visible (ReqId × Request) (ReqId × Response))
  | .arrive id request => some (.input (id, request))
  | .answer a => some (.output a)
  | _ => none

end World

/-- The kernel's environment, but the gate takes the system's answers in any order, as the
front takes the runtime's outputs. -/
def servedEnv : EnvModel (servedSig σ) where
  link _ dst := match dst with
    | .inl () => Link.unordered
    | .inr _ => Link.reliable

/-! The relation between the two. -/

/-- A sender in the runtime as a sender in `served sys`: the outside is the gate. The sink sends
nothing; it is the outside, so that the map is one to one. -/
def swap : Option (Unit ⊕ σ.Id) → Option (Unit ⊕ σ.Id)
  | none => some (.inl ())
  | some (.inl ()) => none
  | some (.inr i) => some (.inr i)

/-- A message in the runtime as one in `served sys`. One to the sink is nothing. -/
def conv : Envelope (admittedSig σ) → Option (Envelope (servedSig σ))
  | ⟨src, .inr j, m⟩ => some ⟨swap src, .inr j, m⟩
  | ⟨_, .inl (), _⟩ => none

def toSys (e : Envelope (servedSig σ)) : Bool := e.dst.isRight

def toGate : Envelope (servedSig σ) → Option (GateMsg σ)
  | ⟨_, .inl (), m⟩ => some m
  | ⟨_, .inr _, _⟩ => none

def responds (bridge : Bridge σ) (out : σ.Out) : Bool := (bridge.encode out).isSome

/-- The server is `served sys` in state `c`: the gate's waiting list and deadlines are the
front's, its answers not yet handed over are the front's, the application's actors are as in
the runtime, and the messages on their way to the gate are the runtime's outputs that are answers
and that the front has not yet taken. -/
structure Rel (w : World sys bridge) (c : SysState (served sys bridge config)) : Prop where
  pending : c.state (.inl ()) = w.front.pending
  state : ∀ j, c.state (.inr j) = w.runtime.state (.inr j)
  gateUp : c.up (.inl ()) = true
  up : ∀ j, c.up (.inr j) = w.runtime.up (.inr j)
  gateTimers : c.timers (.inl ()) = w.front.armed.map .expire
  timers : ∀ j, c.timers (.inr j) = w.runtime.timers (.inr j)
  outbox : c.outbox = w.answers
  sysNet : c.net.filter toSys = w.runtime.net.filterMap conv
  gateNet : (c.net.filterMap toGate).Perm ((w.runtime.outbox.filter (responds bridge)).map .answer)
  clock : c.clock = w.runtime.clock

/-! What an actor of the application does, in each. -/

def newE {j : σ.Id} : Effect σ j → List (Effect (admittedSig σ) (.inr j))
  | .send to m => [.send (.inr to) m]
  | .emit out => [.emit out]
  | .after d m => [.after d m]
  | .cancel m => [.cancel m]
  | .stop => [.stop]

def oldE (bridge : Bridge σ) {j : σ.Id} : Effect σ j → List (Effect (servedSig σ) (.inr j))
  | .send to m => [.send (.inr to) m]
  | .emit out => if responds bridge out then [.send (.inl ()) (.answer out)] else []
  | .after d m => [.after d m]
  | .cancel m => [.cancel m]
  | .stop => [.stop]

theorem admitted_step (j : σ.Id) (t : Moment) (src : Sender (Unit ⊕ σ.Id)) (s : sys.State j)
    (m : σ.Msg j) :
    ((admitted sys bridge).actor (.inr j)).stepAt ⟨t, src⟩ s m
      = (((sys.actor j).stepAt ⟨t, Sender.right src⟩ s m).1,
          ((sys.actor j).stepAt ⟨t, Sender.right src⟩ s m).2.flatMap newE) := by
  simp only [Actor.mapEff, Actor.mapSrc, List.flatMap_assoc, Prod.mk.injEq, true_and]
  congr 1
  funext eff
  cases eff <;> simp [Wiring.right, Effect.filterMapOut, admitOutput, newE]

theorem admitted_recover (j : σ.Id) (t : Moment) (s : sys.State j) :
    ((admitted sys bridge).actor (.inr j)).recoverAt t s
      = (((sys.actor j).recoverAt t s).1, ((sys.actor j).recoverAt t s).2.flatMap newE) := by
  simp only [Actor.mapEff, Actor.mapSrc, List.flatMap_assoc, Prod.mk.injEq, true_and]
  congr 1
  funext eff
  cases eff <;> simp [Wiring.right, Effect.filterMapOut, admitOutput, newE]

theorem served_step (j : σ.Id) (t : Moment) (src : Sender (Unit ⊕ σ.Id)) (s : sys.State j)
    (m : σ.Msg j) :
    ((served sys bridge config).actor (.inr j)).stepAt ⟨t, src⟩ s m
      = (((sys.actor j).stepAt ⟨t, Sender.right src⟩ s m).1,
          ((sys.actor j).stepAt ⟨t, Sender.right src⟩ s m).2.flatMap (oldE bridge)) := by
  simp only [Actor.mapEff, Actor.mapSrc, List.flatMap_assoc, Prod.mk.injEq, true_and]
  congr 1
  funext eff
  cases eff with
  | emit out =>
    simp only [oldE, responds, List.flatMap_cons, List.flatMap_nil, Wiring.right, frontWiring]
    by_cases h : (bridge.encode out).isSome = true <;> simp [h, Effect.filterMapOut, frontedOutput]
  | _ => simp [Wiring.right, Effect.filterMapOut, oldE]

theorem served_recover (j : σ.Id) (t : Moment) (s : sys.State j) :
    ((served sys bridge config).actor (.inr j)).recoverAt t s
      = (((sys.actor j).recoverAt t s).1,
          ((sys.actor j).recoverAt t s).2.flatMap (oldE bridge)) := by
  simp only [Actor.mapEff, Actor.mapSrc, List.flatMap_assoc, Prod.mk.injEq, true_and]
  congr 1
  funext eff
  cases eff with
  | emit out =>
    simp only [oldE, responds, List.flatMap_cons, List.flatMap_nil, Wiring.right, frontWiring]
    by_cases h : (bridge.encode out).isSome = true <;> simp [h, Effect.filterMapOut, frontedOutput]
  | _ => simp [Wiring.right, Effect.filterMapOut, oldE]

/-- What the gate does, as an effect of the gate in `served sys`. -/
def oldG (sys : System σ) (config : GateConfig) : Gate.Act σ → List (Effect (servedSig σ) (.inl ()))
  | .respond id response => [.emit (id, response)]
  | .forward x => [.send (.inr (sys.accept x).1) (sys.accept x).2]
  | .arm id => [.after config.requestTimeout_ms (.expire id)]
  | .disarm id => [.cancel (.expire id)]

def Gate.Act.perform {E : Type} (does : Gate.Effects σ E) : Gate.Act σ → E
  | .respond id response => does.respond id response
  | .forward x => does.forward x
  | .arm id => does.arm id
  | .disarm id => does.disarm id

/-- The gate's decisions do not depend on what its acts are. -/
theorem gate_step_acts {E : Type} (does : Gate.Effects σ E) (pending : List ReqId)
    (msg : GateMsg σ) :
    Gate.step bridge config does pending msg
      = ((Gate.step bridge config Gate.acts pending msg).1,
          (Gate.step bridge config Gate.acts pending msg).2.map (Gate.Act.perform does)) := by
  cases msg with
  | arrive id request =>
    simp only [Gate.step]
    split
    · rfl
    · split
      · rfl
      · split <;> rfl
  | answer out =>
    simp only [Gate.step]
    split
    · split <;> rfl
    · rfl
  | expire id =>
    simp only [Gate.step]
    split <;> rfl

theorem served_gate_step (ctx : Ctx (Unit ⊕ σ.Id)) (pending : List ReqId) (msg : GateMsg σ) :
    ((served sys bridge config).actor (.inl ())).stepAt ctx pending msg
      = ((Gate.step bridge config Gate.acts pending msg).1,
          (Gate.step bridge config Gate.acts pending msg).2.flatMap (oldG sys config)) := by
  simp only [Actor.mapEff, Actor.mapSrc, gateActor]
  rw [gate_step_acts]
  simp only [List.flatMap_assoc, List.flatMap_map, Prod.mk.injEq, true_and]
  congr 1
  funext a
  cases a <;> simp [Gate.Act.perform, Wiring.left, frontWiring, Effect.filterMapOut,
    frontedOutput, oldG]

/-! What keeps the relation. -/

theorem swap_inj {a b : Option (Unit ⊕ σ.Id)} (h : swap a = swap b) : a = b := by
  rcases a with _ | (_ | _) <;> rcases b with _ | (_ | _) <;> simp_all [swap]

theorem conv_some {e : Envelope (admittedSig σ)} {x : Envelope (servedSig σ)}
    (h : conv e = some x) : x.dst = e.dst ∧ x.src = swap e.src := by
  obtain ⟨src, dst, m⟩ := e
  rcases dst with ⟨⟩ | j
  · simp [conv] at h
  · simp only [conv, Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl⟩

theorem conv_inj {a b : Envelope (admittedSig σ)} {x : Envelope (servedSig σ)}
    (ha : conv a = some x) (hb : conv b = some x) : a = b := by
  obtain ⟨sa, da, ma⟩ := a
  obtain ⟨sb, db, mb⟩ := b
  rcases da with ⟨⟩ | ja
  · simp [conv] at ha
  rcases db with ⟨⟩ | jb
  · simp [conv] at hb
  simp only [conv, Option.some.injEq] at ha hb
  subst ha
  simp only [Envelope.mk.injEq, Sum.inr.injEq] at hb
  obtain ⟨hs, rfl, hm⟩ := hb
  rw [swap_inj hs.symm, eq_of_heq hm]

theorem toSys_conv {e : Envelope (admittedSig σ)} {x : Envelope (servedSig σ)}
    (h : conv e = some x) : toSys x = true := by
  obtain ⟨src, dst, m⟩ := e
  rcases dst with ⟨⟩ | j
  · simp [conv] at h
  · simp only [conv, Option.some.injEq] at h
    subst h
    rfl

theorem toGate_of_toSys {e : Envelope (servedSig σ)} (h : toSys e = true) : toGate e = none := by
  obtain ⟨src, dst, m⟩ := e
  rcases dst with ⟨⟩ | j
  · simp [toSys] at h
  · rfl

/-- What the gate holds is answers only. -/
theorem toGate_answer {w : World sys bridge} {c : SysState (served sys bridge config)}
    (h : Rel w c) {e : Envelope (servedSig σ)} (he : e ∈ c.net) {m : GateMsg σ}
    (hm : toGate e = some m) : ∃ out, m = .answer out := by
  have : m ∈ (w.runtime.outbox.filter (responds bridge)).map .answer :=
    h.gateNet.mem_iff.mp (List.mem_filterMap.mpr ⟨e, he, hm⟩)
  obtain ⟨out, -, rfl⟩ := List.mem_map.mp this
  exact ⟨out, rfl⟩

/-- A message to an actor of the application, put in flight in both. -/
theorem rel_send {w : World sys bridge} {c : SysState (served sys bridge config)} (h : Rel w c)
    {e : Envelope (admittedSig σ)} {x : Envelope (servedSig σ)} (hx : conv e = some x) :
    Rel { w with runtime := { w.runtime with net := w.runtime.net ++ [e] } }
      { c with net := c.net ++ [x] } where
  pending := h.pending
  state := h.state
  gateUp := h.gateUp
  up := h.up
  gateTimers := h.gateTimers
  timers := h.timers
  outbox := h.outbox
  sysNet := by simp [List.filter_append, h.sysNet, toSys_conv hx, hx]
  gateNet := by
    simpa [List.filterMap_append, toGate_of_toSys (toSys_conv hx)] using h.gateNet
  clock := h.clock

/-- An output of an actor of the application: in the runtime's outbox, and an answer on its way
to the gate in `served sys` if it is a response. -/
theorem rel_emit {w : World sys bridge} {c : SysState (served sys bridge config)} (h : Rel w c)
    (j : σ.Id) (out : σ.Out) :
    Rel { w with runtime := { w.runtime with outbox := w.runtime.outbox ++ [out] } }
      (if responds bridge out then
        { c with net := c.net ++ [⟨some (.inr j), .inl (), .answer out⟩] } else c) := by
  split
  · next hr =>
    exact { h with
      sysNet := by simp [List.filter_append, h.sysNet, toSys]
      gateNet := by
        simpa [List.filterMap_append, List.filter_append, hr, toGate] using
          h.gateNet.append_right [GateMsg.answer out] }
  · next hr =>
    exact { h with gateNet := by simpa [List.filter_append, hr] using h.gateNet }

theorem rel_timers {w : World sys bridge} {c : SysState (served sys bridge config)} (h : Rel w c)
    (j : σ.Id) (v : List (σ.Msg j)) :
    Rel { w with runtime := { w.runtime with timers := update w.runtime.timers (.inr j) v } }
      { c with timers := update c.timers (.inr j) v } :=
  { h with
    gateTimers := by simp [h.gateTimers]
    timers := fun j' => by
      by_cases hj : j' = j
      · subst hj; simp
      · have : (Sum.inr j' : Unit ⊕ σ.Id) ≠ .inr j := fun e => hj (Sum.inr.inj e)
        simp [this, h.timers j'] }

theorem rel_state {w : World sys bridge} {c : SysState (served sys bridge config)} (h : Rel w c)
    (j : σ.Id) (s : sys.State j) :
    Rel { w with runtime := { w.runtime with state := update w.runtime.state (.inr j) s } }
      { c with state := update c.state (.inr j) s } :=
  { h with
    pending := by simp [h.pending]
    state := fun j' => by
      by_cases hj : j' = j
      · subst hj; simp
      · have : (Sum.inr j' : Unit ⊕ σ.Id) ≠ .inr j := fun e => hj (Sum.inr.inj e)
        simp [this, h.state j'] }

theorem rel_up {w : World sys bridge} {c : SysState (served sys bridge config)} (h : Rel w c)
    (j : σ.Id) (b : Bool) :
    Rel { w with runtime := { w.runtime with up := update w.runtime.up (.inr j) b } }
      { c with up := update c.up (.inr j) b } :=
  { h with
    gateUp := by simp [h.gateUp]
    up := fun j' => by
      by_cases hj : j' = j
      · subst hj; simp
      · have : (Sum.inr j' : Unit ⊕ σ.Id) ≠ .inr j := fun e => hj (Sum.inr.inj e)
        simp [this, h.up j'] }

theorem rel_perform {w : World sys bridge} {c : SysState (served sys bridge config)} (h : Rel w c)
    (j : σ.Id) (eff : Effect σ j) :
    Rel { w with runtime := w.runtime.performAll (.inr j) (newE eff) }
      (c.performAll (.inr j) (oldE bridge eff)) := by
  cases eff with
  | send to m =>
    exact rel_send h (e := ⟨some (.inr j), .inr to, m⟩) (x := ⟨some (.inr j), .inr to, m⟩) rfl
  | emit out =>
    have := rel_emit h j out
    by_cases hr : responds bridge out = true
    · simp only [hr, ↓reduceIte] at this
      simpa [newE, oldE, hr, SysState.performAll, SysState.perform] using this
    · simp only [hr, Bool.false_eq_true, ↓reduceIte] at this
      simpa [newE, oldE, hr, SysState.performAll, SysState.perform] using this
  | after d m =>
    have hm : (m ∈ c.timers (.inr j)) = (m ∈ w.runtime.timers (.inr j)) := by rw [h.timers j]
    simp only [newE, oldE, SysState.performAll_cons, SysState.performAll_nil, SysState.perform]
    rw [h.timers j]
    exact rel_timers h j _
  | cancel m =>
    simp only [newE, oldE, SysState.performAll_cons, SysState.performAll_nil, SysState.perform]
    rw [h.timers j]
    exact rel_timers h j _
  | stop => exact h

theorem rel_performAll {w : World sys bridge} {c : SysState (served sys bridge config)}
    (h : Rel w c) (j : σ.Id) (effs : List (Effect σ j)) :
    Rel { w with runtime := w.runtime.performAll (.inr j) (effs.flatMap newE) }
      (c.performAll (.inr j) (effs.flatMap (oldE bridge))) := by
  induction effs generalizing w c with
  | nil => exact h
  | cons eff effs ih =>
    simp only [List.flatMap_cons, SysState.performAll, List.foldl_append] at ih ⊢
    exact ih (rel_perform h j eff)

theorem filter_swap {α : Type} (p q : α → Bool) (l : List α) :
    (l.filter p).filter q = (l.filter q).filter p := by
  simp only [List.filter_filter, Bool.and_comm]

theorem rel_down {w : World sys bridge} {c : SysState (served sys bridge config)} (h : Rel w c)
    (j : σ.Id) :
    Rel { w with runtime := w.runtime.down .reliable (.inr j) } (c.down servedEnv (.inr j)) := by
  have hq : ∀ e : Envelope (servedSig σ),
      (decide (e.dst ≠ .inr j) || (servedEnv.link e.src e.dst).lossy) = decide (e.dst ≠ .inr j) := by
    intro e
    rcases e with ⟨src, dst, m⟩
    rcases dst with ⟨⟩ | j' <;> simp [servedEnv, Link.unordered, Link.reliable]
  have hq' : ∀ e : Envelope (admittedSig σ),
      (decide (e.dst ≠ .inr j) || ((EnvModel.reliable).link e.src e.dst).lossy)
        = decide (e.dst ≠ .inr j) := by
    intro e; simp [EnvModel.reliable, Link.reliable]
  have h1 := rel_up (rel_timers h j []) j false
  refine { h1 with sysNet := ?_, gateNet := ?_ }
  · simp only [SysState.down]
    rw [List.filter_congr (fun e _ => hq e), List.filter_congr (fun e _ => hq' e),
      filter_swap, h.sysNet, List.filter_filterMap, List.filterMap_filter]
    congr 1
    funext e
    cases hc : conv e with
    | none => simp
    | some x =>
      obtain ⟨hd, -⟩ := conv_some hc
      by_cases hj : e.dst = Sum.inr j <;> simp [Option.filter, hd, hj]
  · simp only [SysState.down]
    rw [List.filter_congr (fun e _ => hq e), filterMap_filter_of_none]
    · exact h.gateNet
    · intro e he
      rcases e with ⟨src, dst, m⟩
      rcases dst with ⟨⟩ | j'
      · simp at he
      · rfl

theorem rel_settle {w : World sys bridge} {c : SysState (served sys bridge config)} (h : Rel w c)
    (j : σ.Id) (s : sys.State j) (effs : List (Effect σ j)) :
    Rel { w with runtime := w.runtime.settle .reliable (.inr j) (s, effs.flatMap newE) }
      (c.settle servedEnv (.inr j) (s, effs.flatMap (oldE bridge))) := by
  have hnew : (effs.flatMap (newE (j := j))).any Effect.isStop = effs.any Effect.isStop :=
    Effect.any_isStop_flatMap (fun eff => by cases eff <;> rfl) effs
  have hold : (effs.flatMap (oldE bridge (j := j))).any Effect.isStop = effs.any Effect.isStop :=
    Effect.any_isStop_flatMap (fun eff => by
      cases eff with
      | emit out => simp only [oldE]; split <;> rfl
      | _ => rfl) effs
  have h1 := rel_performAll (rel_state h j s) j effs
  simp only [SysState.settle, hnew, hold]
  split
  · exact rel_down h1 j
  · exact h1

theorem rel_handle {w : World sys bridge} {c : SysState (served sys bridge config)} (h : Rel w c)
    (j : σ.Id) (m : σ.Msg j) {src src' : Sender (Unit ⊕ σ.Id)}
    (hsrc : Sender.right src' = Sender.right src) :
    Rel { w with runtime := w.runtime.handle .reliable (.inr j) m src }
      (c.handle servedEnv (.inr j) m src') := by
  simp only [SysState.handle]
  rw [admitted_step, served_step, h.state j, h.clock, hsrc]
  exact rel_settle h j _ _

theorem rel_start {w : World sys bridge} {c : SysState (served sys bridge config)} (h : Rel w c)
    (j : σ.Id) :
    Rel { w with runtime := w.runtime.startActor .reliable (.inr j) }
      (c.startActor servedEnv (.inr j)) := by
  simp only [SysState.startActor]
  rw [admitted_recover, served_recover, h.state j,
    show (sys.actor j).recoverAt c.clock = (sys.actor j).recoverAt w.runtime.clock by rw [h.clock]]
  exact rel_settle (rel_up h j true) j _ _

/-! The gate's side. -/

theorem admitted_accept {id : ReqId} {request : Request} {x : σ.In}
    (h : bridge.decode id request = .ok x) :
    (admitted sys bridge).accept (id, request) = ⟨.inr (sys.accept x).1, (sys.accept x).2⟩ := by
  simp [admitInput, h]

theorem rel_act {w : World sys bridge} {c : SysState (served sys bridge config)} (h : Rel w c)
    (entry : Option (ReqId × Request)) (a : Gate.Act σ)
    (hfwd : ∀ x, a = .forward x → ∃ e, entry = some e ∧ bridge.decode e.1 e.2 = .ok x) :
    Rel (w.act entry a) (c.performAll (.inl ()) (oldG sys config a)) := by
  cases a with
  | respond id response =>
    exact { h with
      outbox := by simp [oldG, SysState.performAll, SysState.perform, h.outbox, World.act] }
  | forward x =>
    obtain ⟨⟨id, request⟩, rfl, hdec⟩ := hfwd x rfl
    have hdec : bridge.decode id request = .ok x := hdec
    have he : (⟨none, ((admitted sys bridge).accept (id, request)).1,
        ((admitted sys bridge).accept (id, request)).2⟩ : Envelope (admittedSig σ))
          = ⟨none, .inr (sys.accept x).1, (sys.accept x).2⟩ := by
      rw [admitted_accept hdec]
    have hw : w.act (some (id, request)) (.forward x) = { w with runtime := { w.runtime with
        net := w.runtime.net ++ [⟨none, .inr (sys.accept x).1, (sys.accept x).2⟩] } } := by
      rw [← he]; rfl
    rw [hw]
    simp only [oldG, SysState.performAll_cons, SysState.performAll_nil, SysState.perform]
    exact rel_send h rfl
  | arm id =>
    have hmem : ((GateMsg.expire id : GateMsg σ) ∈ w.front.armed.map GateMsg.expire)
        = (id ∈ w.front.armed) := by
      simp
    refine { h with gateTimers := ?_, timers := fun j => ?_ }
    · simp only [oldG, SysState.performAll_cons, SysState.performAll_nil, SysState.perform,
        update_self, h.gateTimers, hmem, World.act, arm]
      split <;> simp
    · simp [oldG, SysState.performAll, SysState.perform, h.timers j, World.act]
  | disarm id =>
    refine { h with gateTimers := ?_, timers := fun j => ?_ }
    · simp only [oldG, SysState.performAll_cons, SysState.performAll_nil, SysState.perform,
        update_self, h.gateTimers, World.act, arm]
      exact (map_erase fun x _ hx => GateMsg.expire.inj hx).symm
    · simp [oldG, SysState.performAll, SysState.perform, h.timers j, World.act]

theorem rel_acts {w : World sys bridge} {c : SysState (served sys bridge config)} (h : Rel w c)
    (entry : Option (ReqId × Request)) (acts : List (Gate.Act σ))
    (hfwd : ∀ x, Gate.Act.forward x ∈ acts → ∃ e, entry = some e ∧ bridge.decode e.1 e.2 = .ok x) :
    Rel (acts.foldl (World.act entry) w)
      (c.performAll (.inl ()) (acts.flatMap (oldG sys config))) := by
  induction acts generalizing w c with
  | nil => exact h
  | cons a acts ih =>
    simp only [List.foldl_cons, List.flatMap_cons, SysState.performAll, List.foldl_append] at ih ⊢
    exact ih (rel_act h entry a fun x hx => hfwd x (hx ▸ List.mem_cons_self))
      fun x hx => hfwd x (List.mem_cons_of_mem _ hx)

/-- The gate passes on only what `decode` made of an arrival. -/
theorem forward_mem {pending : List ReqId} {msg : GateMsg σ} {x : σ.In}
    (h : Gate.Act.forward x ∈ (Gate.step bridge config Gate.acts pending msg).2) :
    ∃ id request, msg = .arrive id request ∧ bridge.decode id request = .ok x := by
  cases msg with
  | arrive id request =>
    refine ⟨id, request, rfl, ?_⟩
    simp only [Gate.step] at h
    split at h
    · simp at h
    · split at h
      · simp [Gate.acts] at h
      · split at h
        · simp [Gate.acts] at h
        · next y hy => simp only [Gate.acts, List.mem_cons, Gate.Act.forward.injEq] at h; simp_all
  | answer out =>
    simp only [Gate.step] at h
    split at h
    · split at h <;> simp [Gate.acts] at h
    · simp at h
  | expire id =>
    simp only [Gate.step] at h
    split at h <;> simp [Gate.acts] at h

theorem rel_decide {w : World sys bridge} {c : SysState (served sys bridge config)} (h : Rel w c)
    (msg : GateMsg σ) (entry : Option (ReqId × Request))
    (hentry : ∀ id request, msg = .arrive id request → entry = some (id, request))
    (src : Sender (Unit ⊕ σ.Id)) :
    Rel (w.decide bridge config msg entry) (c.handle servedEnv (.inl ()) msg src) := by
  simp only [SysState.handle]
  rw [served_gate_step, h.pending]
  have hstop : ((Gate.step bridge config Gate.acts w.front.pending msg).2.flatMap
      (oldG sys config)).any Effect.isStop = false := by
    simp only [List.any_flatMap]
    simp only [List.any_eq_false]
    intro a _
    cases a <;> simp [oldG, Effect.isStop]
  simp only [SysState.settle, hstop, Bool.false_eq_true, ↓reduceIte]
  refine rel_acts ?_ entry _ fun x hx => ?_
  · exact { h with
      pending := by simp
      state := fun j => by simp [h.state j] }
  · obtain ⟨id, request, rfl, hdec⟩ := forward_mem hx
    exact ⟨(id, request), hentry id request rfl, hdec⟩

/-! The runtime's sink does nothing the gate sees. -/

theorem rel_runtime {w : World sys bridge} {c : SysState (served sys bridge config)} (h : Rel w c)
    (s : SysState (admitted sys bridge)) (hstate : ∀ j, s.state (.inr j) = w.runtime.state (.inr j))
    (hup : ∀ j, s.up (.inr j) = w.runtime.up (.inr j))
    (htimers : ∀ j, s.timers (.inr j) = w.runtime.timers (.inr j))
    (hnet : s.net.filterMap conv = w.runtime.net.filterMap conv) (houtbox : s.outbox = w.runtime.outbox)
    (hclock : s.clock = w.runtime.clock) :
    Rel { w with runtime := s } c :=
  { h with
    clock := h.clock.trans hclock.symm
    state := fun j => (h.state j).trans (hstate j).symm
    up := fun j => (h.up j).trans (hup j).symm
    timers := fun j => (h.timers j).trans (htimers j).symm
    sysNet := h.sysNet.trans hnet.symm
    gateNet := by rw [houtbox]; exact h.gateNet }

theorem sink_settle (s : SysState (admitted sys bridge)) (env : EnvModel (admittedSig σ)) (u : Unit) :
    s.settle env (.inl ()) (u, []) = { s with state := update s.state (.inl ()) u } := by
  simp [SysState.settle, SysState.performAll]

theorem rel_sink_state {w : World sys bridge} {c : SysState (served sys bridge config)}
    (h : Rel w c) (u : Unit) :
    Rel { w with runtime := { w.runtime with state := update w.runtime.state (.inl ()) u } } c :=
  rel_runtime h _ (fun _ => by simp [update]) (fun _ => rfl) (fun _ => rfl) rfl rfl rfl

theorem conv_sameLink {e : Envelope (admittedSig σ)} {x : Envelope (servedSig σ)}
    (hx : conv e = some x) (a : Envelope (admittedSig σ)) :
    ((conv a).any x.sameLink) = e.sameLink a := by
  obtain ⟨hxd, hxs⟩ := conv_some hx
  cases ha : conv a with
  | none =>
    obtain ⟨src, dst, m⟩ := a
    rcases dst with ⟨⟩ | j
    · obtain ⟨es, ed, em⟩ := e
      rcases ed with ⟨⟩ | je
      · simp [conv] at hx
      · simp [Envelope.sameLink]
    · simp [conv] at ha
  | some y =>
    obtain ⟨hyd, hys⟩ := conv_some ha
    simp only [Option.any_some, Envelope.sameLink, hxd, hxs, hyd, hys]
    congr 1
    simp only [decide_eq_decide]
    exact ⟨fun h => swap_inj h, fun h => h ▸ rfl⟩

/-! Each event of the server is a run of `served sys`. -/

theorem hasMail_eq {w : World sys bridge} {c : SysState (served sys bridge config)} (h : Rel w c)
    (j : σ.Id) : c.hasMail (.inr j) = w.runtime.hasMail (.inr j) := by
  have hc : c.hasMail (.inr j) = (c.net.filter toSys).any fun e => decide (e.dst = .inr j) := by
    simp only [SysState.hasMail, List.any_filter]
    congr 1
    funext e
    rcases e with ⟨src, dst, m⟩
    rcases dst with ⟨⟩ | j' <;> simp [toSys]
  rw [hc, h.sysNet, List.any_filterMap, SysState.hasMail]
  congr 1
  funext e
  cases hx : conv e with
  | none =>
    rcases e with ⟨src, dst, m⟩
    rcases dst with ⟨⟩ | j'
    · simp
    · simp [conv] at hx
  | some x =>
    obtain ⟨hd, -⟩ := conv_some hx
    simp [hd]

theorem deliverable_eq {w : World sys bridge} {c : SysState (served sys bridge config)}
    (h : Rel w c) {e : Envelope (admittedSig σ)} {x : Envelope (servedSig σ)} (hx : conv e = some x)
    (hd : w.runtime.deliverable .reliable e = true) : c.deliverable servedEnv x = true := by
  obtain ⟨hxd, -⟩ := conv_some hx
  have hlink : servedEnv.link x.src x.dst = Link.reliable := by
    rw [hxd]
    obtain ⟨src, dst, m⟩ := e
    rcases dst with ⟨⟩ | j
    · simp [conv] at hx
    · rfl
  simp only [SysState.deliverable, EnvModel.reliable, Link.reliable, ↓reduceIte] at hd
  simp only [SysState.deliverable, hlink, Link.reliable, ↓reduceIte]
  have hfind : c.net.find? x.sameLink = (c.net.filter toSys).find? x.sameLink := by
    rw [List.find?_filter]
    congr 1
    funext a
    by_cases hs : x.sameLink a = true
    · have : toSys a = true := by
        simp only [Envelope.sameLink, Bool.and_eq_true, decide_eq_true_eq] at hs
        rw [toSys, ← hs.2, hxd]
        obtain ⟨src, dst, m⟩ := e
        rcases dst with ⟨⟩ | j
        · simp [conv] at hx
        · rfl
      simp [hs, this]
    · simp [hs]
  rw [hfind, h.sysNet, List.find?_filterMap]
  have : (fun a => (conv a).any x.sameLink) = e.sameLink := funext (conv_sameLink hx)
  rw [this]
  simp only [beq_iff_eq] at hd
  rw [hd]
  simp [hx]

/-- What the gate holds is answers, so an arrival is not among them. -/
theorem arrival_not_mem {w : World sys bridge} {c : SysState (served sys bridge config)}
    (h : Rel w c) (id : ReqId) (request : Request) :
    (⟨none, .inl (), .arrive id request⟩ : Envelope (servedSig σ)) ∉ c.net := by
  intro he
  obtain ⟨out, hout⟩ := toGate_answer h he rfl
  cases hout

theorem sim_arrive {w : World sys bridge} {c : SysState (served sys bridge config)} (h : Rel w c)
    (id : ReqId) (request : Request) :
    c.run servedEnv [.input (id, request), .deliver ⟨none, .inl (), .arrive id request⟩]
      = some (c.handle servedEnv (.inl ()) (.arrive id request)) := by
  have hin : c.step servedEnv (.input (id, request))
      = some { c with net := c.net ++ [⟨none, .inl (), .arrive id request⟩] } :=
    SysState.step_input.mpr rfl
  have hdel : ({ c with net := c.net ++ [⟨none, .inl (), .arrive id request⟩] } :
      SysState (served sys bridge config)).step servedEnv (.deliver ⟨none, .inl (), .arrive id request⟩)
        = some (c.handle servedEnv (.inl ()) (.arrive id request)) := by
    refine SysState.step_deliver.mpr ⟨h.gateUp, ?_, ?_⟩
    · simp [SysState.deliverable, servedEnv, Link.unordered]
    · rw [List.erase_append_right _ (arrival_not_mem h id request)]
      simp
      rfl
  rw [SysState.run, hin, Option.bind_some, SysState.run, hdel]
  rfl

theorem sink_handle (s : SysState (admitted sys bridge)) (env : EnvModel (admittedSig σ)) (m : Unit)
    (src : Sender (Unit ⊕ σ.Id)) :
    s.handle env (.inl ()) m src = { s with state := update s.state (.inl ()) () } :=
  sink_settle s env ()

theorem sink_start (s : SysState (admitted sys bridge)) (env : EnvModel (admittedSig σ)) :
    s.startActor env (.inl ())
      = { s with up := update s.up (.inl ()) true, state := update s.state (.inl ()) () } :=
  sink_settle { s with up := update s.up (.inl ()) true } env ()

theorem sim_runtime {w w' : World sys bridge} {c : SysState (served sys bridge config)}
    (h : Rel w c) {ev : Lanes.Event (admittedSig σ)} (hstep : w.step config (.runtime ev) = some w') :
    ∃ (evs : List (Lanes.Event (servedSig σ))) (c' : SysState (served sys bridge config)),
      c.run servedEnv evs = some c' ∧ Rel w' c'
        ∧ evs.filterMap Lanes.Event.visible = (World.Event.visible (.runtime ev)).toList := by
  cases ev with
  | input x => simp [World.step] at hstep
  | output o => simp [World.step] at hstep
  | deliver e =>
    simp only [World.step, Option.map_eq_some_iff] at hstep
    obtain ⟨s, hs, rfl⟩ := hstep
    obtain ⟨hup, hd, rfl⟩ := SysState.step_deliver.mp hs
    obtain ⟨src, dst, m⟩ := e
    rcases dst with ⟨⟩ | j
    · refine ⟨[], c, rfl, ?_, rfl⟩
      rw [sink_handle]
      have h1 : Rel { w with runtime := { w.runtime with net := w.runtime.net.erase ⟨src, .inl (), m⟩ } } c :=
        rel_runtime h _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (filterMap_erase_of_none rfl _) rfl
          rfl
      exact rel_sink_state h1 ()
    · let x : Envelope (servedSig σ) := ⟨swap src, .inr j, m⟩
      have hx : conv ⟨src, .inr j, m⟩ = some x := rfl
      have h1 : Rel { w with runtime := { w.runtime with net := w.runtime.net.erase ⟨src, .inr j, m⟩ } }
          { c with net := c.net.erase x } :=
        { h with
          sysNet := by
            rw [filter_erase_of_pos _ _ (toSys_conv hx), h.sysNet,
              filterMap_erase (fun y => ⟨fun hy => conv_inj hy hx, fun hy => hy ▸ hx⟩)]
          gateNet := by rw [filterMap_erase_of_none rfl]; exact h.gateNet }
      refine ⟨[.deliver x], _, ?_,
        rel_handle h1 j m (src' := .ofSrc (swap src)) (by rcases src with _ | (_ | _) <;> rfl), rfl⟩
      rw [SysState.run, SysState.step_deliver.mpr
        ⟨by rw [h.up]; exact hup, deliverable_eq h hx hd, rfl⟩]
      rfl
  | duplicate e =>
    simp only [World.step, Option.map_eq_some_iff] at hstep
    obtain ⟨s, hs, -⟩ := hstep
    obtain ⟨-, hdup, -⟩ := SysState.step_duplicate.mp hs
    simp [EnvModel.reliable, Link.reliable] at hdup
  | drop e =>
    simp only [World.step, Option.map_eq_some_iff] at hstep
    obtain ⟨s, hs, -⟩ := hstep
    obtain ⟨hlossy, -⟩ := SysState.step_drop.mp hs
    simp [EnvModel.reliable, Link.reliable] at hlossy
  | crash i =>
    simp only [World.step, Option.map_eq_some_iff] at hstep
    obtain ⟨s, hs, -⟩ := hstep
    obtain ⟨-, hcrash, -⟩ := SysState.step_crash.mp hs
    simp [EnvModel.reliable] at hcrash
  | restart =>
    simp only [World.step, Option.map_eq_some_iff] at hstep
    obtain ⟨s, hs, -⟩ := hstep
    obtain ⟨hmay, -⟩ := SysState.step_restart.mp hs
    simp [EnvModel.reliable] at hmay
  | tick m =>
    simp only [World.step, Option.map_eq_some_iff] at hstep
    obtain ⟨s, hs, rfl⟩ := hstep
    obtain rfl := SysState.step_tick.mp hs
    exact ⟨[.tick m], { c with clock := m }, by simp [SysState.run, SysState.step_tick],
      { h with clock := rfl }, rfl⟩
  | timeout i m =>
    simp only [World.step, Option.map_eq_some_iff] at hstep
    obtain ⟨s, hs, rfl⟩ := hstep
    obtain ⟨hup, hm, rfl⟩ := SysState.step_timeout.mp hs
    rcases i with ⟨⟩ | j
    · refine ⟨[], c, rfl, ?_, rfl⟩
      rw [sink_handle]
      have h1 : Rel { w with runtime := { w.runtime with
          timers := update w.runtime.timers (.inl ()) ((w.runtime.timers (.inl ())).erase m) } } c :=
        rel_runtime h _ (fun _ => rfl) (fun _ => rfl) (fun _ => by simp [update]) rfl rfl rfl
      exact rel_sink_state h1 ()
    · let c₁ : SysState (served sys bridge config) :=
        { c with timers := update c.timers (.inr j) ((c.timers (.inr j)).erase m) }
      refine ⟨[.timeout (.inr j) m], c₁.handle servedEnv (.inr j) m .timer, ?_, ?_, rfl⟩
      · rw [SysState.run, SysState.step_timeout.mpr
          ⟨by rw [h.up]; exact hup, by rw [h.timers]; exact hm, rfl⟩]
        rfl
      · have hv : (c.timers (.inr j)).erase m = (w.runtime.timers (.inr j)).erase m := by
          rw [h.timers j]
        simp only [c₁]
        rw [hv]
        exact rel_handle (rel_timers h j _) j m (src' := .timer) rfl
  | start i =>
    simp only [World.step, Option.map_eq_some_iff] at hstep
    obtain ⟨s, hs, rfl⟩ := hstep
    obtain ⟨hdown, hmail, rfl⟩ := SysState.step_start.mp hs
    rcases i with ⟨⟩ | j
    · refine ⟨[], c, rfl, ?_, rfl⟩
      rw [sink_start]
      exact rel_runtime h _ (fun _ => by simp [update]) (fun _ => by simp [update]) (fun _ => rfl)
        rfl rfl rfl
    · have hmail' : c.hasMail (.inr j) = true := by
        rw [hasMail_eq h]
        simpa [EnvModel.reliable] using hmail
      refine ⟨[.start (.inr j)], _, ?_, rel_start h j, rfl⟩
      simp [SysState.run, SysState.step_start.mpr ⟨by rw [h.up]; exact hdown, .inl hmail', rfl⟩]

theorem sim_step {w w' : World sys bridge} {c : SysState (served sys bridge config)}
    (h : Rel w c) {ev : World.Event σ} (hstep : w.step config ev = some w') :
    ∃ (evs : List (Lanes.Event (servedSig σ))) (c' : SysState (served sys bridge config)),
      c.run servedEnv evs = some c' ∧ Rel w' c'
        ∧ evs.filterMap Lanes.Event.visible = (World.Event.visible ev).toList := by
  cases ev with
  | arrive id request =>
    simp only [World.step, Option.some.injEq] at hstep
    subst hstep
    refine ⟨_, _, sim_arrive h id request, rel_decide h _ _ (fun _ _ e => by cases e; rfl) .outside, ?_⟩
    simp [Lanes.Event.visible, World.Event.visible]
  | expire id =>
    simp only [World.step] at hstep
    split at hstep
    · next hid =>
      simp only [Option.some.injEq] at hstep
      subst hstep
      have hmem : GateMsg.expire id ∈ c.timers (.inl ()) := by
        rw [h.gateTimers]; exact List.mem_map_of_mem hid
      have h1 : Rel { w with front := { w.front with armed := w.front.armed.erase id } }
          { c with timers := update c.timers (.inl ()) ((c.timers (.inl ())).erase (.expire id)) } :=
        { h with
          gateTimers := by
            simp only [update_self, h.gateTimers]
            exact (map_erase fun x _ hx => GateMsg.expire.inj hx).symm
          timers := fun j => by simp [h.timers j] }
      refine ⟨[.timeout (.inl ()) (.expire id)], _, ?_,
        rel_decide h1 (.expire id) none (fun _ _ e => by cases e) .timer,
        by simp [Lanes.Event.visible, World.Event.visible]⟩
      simp [SysState.run, SysState.step_timeout.mpr ⟨h.gateUp, hmem, rfl⟩]
    · simp at hstep
  | take out =>
    simp only [World.step] at hstep
    split at hstep
    · next hout =>
      simp only [Option.some.injEq] at hstep
      subst hstep
      by_cases hr : responds bridge out = true
      · have hin : GateMsg.answer out ∈ c.net.filterMap toGate :=
          h.gateNet.mem_iff.mpr (List.mem_map_of_mem (List.mem_filter.mpr ⟨hout, hr⟩))
        obtain ⟨e, he, hte⟩ := List.mem_filterMap.mp hin
        obtain ⟨src, dst, m⟩ := e
        rcases dst with ⟨⟩ | j
        · simp only [toGate, Option.some.injEq] at hte
          subst hte
          have h1 : Rel { w with runtime := { w.runtime with outbox := w.runtime.outbox.erase out } }
              { c with net := c.net.erase ⟨src, .inl (), .answer out⟩ } :=
            { h with
              sysNet := by rw [filter_erase_of_neg _ _ (by rfl), h.sysNet]
              gateNet := by
                dsimp only
                refine (filterMap_erase_perm (f := toGate) he rfl).symm.trans ?_
                refine (h.gateNet.erase _).trans ?_
                rw [filter_erase_of_pos _ _ hr, map_erase fun x _ hx => GateMsg.answer.inj hx] }
          refine ⟨[.deliver ⟨src, .inl (), .answer out⟩], _, ?_,
            rel_decide h1 (.answer out) none (fun _ _ e => by cases e) (.ofSrc src),
            by simp [Lanes.Event.visible, World.Event.visible]⟩
          have hdel := SysState.step_deliver (env := servedEnv) (c := c)
            (c' := ({ c with net := c.net.erase ⟨src, .inl (), .answer out⟩ } :
              SysState (served sys bridge config)).handle servedEnv (.inl ()) (.answer out)
                (.ofSrc src))
            (e := ⟨src, .inl (), .answer out⟩)
          simp only [SysState.run, hdel.mpr ⟨h.gateUp, by
            simp [SysState.deliverable, servedEnv, Link.unordered, he], rfl⟩, Option.bind_some]
        · simp [toGate] at hte
      · have hnone : bridge.encode out = none := by
          simpa [responds] using hr
        refine ⟨[], c, rfl, ?_, by simp [World.Event.visible]⟩
        have h1 : Rel { w with runtime := { w.runtime with outbox := w.runtime.outbox.erase out } } c :=
          { h with
            gateNet := by
              dsimp only
              rw [filter_erase_of_neg _ _ (by simpa using hr)]
              exact h.gateNet }
        have hw : ({ w with runtime := { w.runtime with outbox := w.runtime.outbox.erase out } } :
            World sys bridge).decide bridge config (.answer out) none
              = { w with runtime := { w.runtime with outbox := w.runtime.outbox.erase out } } := by
          simp only [World.decide, Gate.step, hnone, List.foldl_nil]
        rw [hw]
        exact h1
    · simp at hstep
  | answer a =>
    simp only [World.step] at hstep
    split at hstep
    · next ha =>
      simp only [Option.some.injEq] at hstep
      subst hstep
      refine ⟨[.output a], { c with outbox := c.outbox.erase a }, ?_,
        { h with outbox := by simp [h.outbox] }, by simp [Lanes.Event.visible, World.Event.visible]⟩
      simp [SysState.run, SysState.step_output.mpr ⟨by rw [h.outbox]; exact ha, rfl⟩]
    · simp at hstep
  | runtime ev => exact sim_runtime h hstep

/-! From the start. -/

theorem rel_boot {w : World sys bridge} {c : SysState (served sys bridge config)} (h : Rel w c)
    (boot : List σ.Id) :
    Rel { w with runtime := (boot.map Sum.inr).foldl (fun s i => s.startActor .reliable i) w.runtime }
      ((boot.map Sum.inr).foldl (fun c i => c.startActor servedEnv i) c) := by
  induction boot generalizing w c with
  | nil => exact h
  | cons j boot ih => exact ih (rel_start h j)

theorem rel_init : Rel (World.init sys bridge)
    (SysState.init (served sys bridge config) servedEnv) := by
  have h0 : Rel ({ runtime := SysState.blank (admitted sys bridge) } : World sys bridge)
      ((SysState.blank (served sys bridge config)).startActor servedEnv (.inl ())) :=
    { pending := by simp [SysState.startActor, SysState.settle, SysState.blank, Actor.mapEff, Actor.mapSrc,
        gateActor,
        SysState.performAll]
      state := fun _ => by simp [SysState.startActor, SysState.settle, SysState.blank, Actor.mapEff, Actor.mapSrc,
        gateActor,
        SysState.performAll]
      gateUp := by simp [SysState.startActor, SysState.settle, SysState.blank, Actor.mapEff, Actor.mapSrc,
        gateActor,
        SysState.performAll]
      up := fun _ => by simp [SysState.startActor, SysState.settle, SysState.blank, Actor.mapEff, Actor.mapSrc,
        gateActor,
        SysState.performAll]
      gateTimers := by simp [SysState.startActor, SysState.settle, SysState.blank, Actor.mapEff, Actor.mapSrc,
        gateActor,
        SysState.performAll]
      timers := fun _ => by simp [SysState.startActor, SysState.settle, SysState.blank, Actor.mapEff, Actor.mapSrc,
        gateActor,
        SysState.performAll]
      outbox := by simp [SysState.startActor, SysState.settle, SysState.blank, Actor.mapEff, Actor.mapSrc,
        gateActor,
        SysState.performAll]
      sysNet := by simp [SysState.startActor, SysState.settle, SysState.blank, Actor.mapEff, Actor.mapSrc,
        gateActor,
        SysState.performAll]
      gateNet := by simp [SysState.startActor, SysState.settle, SysState.blank, Actor.mapEff, Actor.mapSrc,
        gateActor,
        SysState.performAll]
      clock := by simp [SysState.startActor, SysState.settle, SysState.blank, Actor.mapEff, Actor.mapSrc,
        gateActor,
        SysState.performAll] }
  have := rel_boot h0 sys.boot
  have hsink : (sink.boot.map (Sum.inl (β := σ.Id))) = [] := rfl
  simpa [World.init, SysState.init, List.foldl_cons, hsink] using this

/-- A run of the server from its start is a run of `served sys` from its start, under
`servedEnv`, with the same requests arriving and the same answers handed over, in the same
order, and the two in the relation `Rel` at its end. -/
theorem World.refines {events : List (World.Event σ)} {w : World sys bridge}
    (hrun : (World.init sys bridge).run config events = some w) :
    ∃ (events' : List (Lanes.Event (servedSig σ))) (c : SysState (served sys bridge config)),
      (SysState.init (served sys bridge config) servedEnv).run servedEnv events' = some c
        ∧ Rel w c
        ∧ events'.filterMap Lanes.Event.visible = events.filterMap World.Event.visible := by
  suffices ∀ (events : List (World.Event σ)) (w₀ w : World sys bridge)
      (c₀ : SysState (served sys bridge config)), Rel w₀ c₀ → w₀.run config events = some w →
      ∃ events' c, c₀.run servedEnv events' = some c ∧ Rel w c
        ∧ events'.filterMap Lanes.Event.visible = events.filterMap World.Event.visible from
    this events _ w _ rel_init hrun
  intro events
  induction events with
  | nil =>
    intro w₀ w c₀ h hrun
    simp only [World.run, Option.some.injEq] at hrun
    subst hrun
    exact ⟨[], c₀, rfl, h, rfl⟩
  | cons ev events ih =>
    intro w₀ w c₀ h hrun
    simp only [World.run] at hrun
    cases hstep : w₀.step config ev with
    | none => simp [hstep] at hrun
    | some w₁ =>
      rw [hstep, Option.bind_some] at hrun
      obtain ⟨evs₁, c₁, hrun₁, h₁, hvis₁⟩ := sim_step h hstep
      obtain ⟨evs₂, c₂, hrun₂, h₂, hvis₂⟩ := ih w₁ w c₁ h₁ hrun
      refine ⟨evs₁ ++ evs₂, c₂, ?_, h₂, ?_⟩
      · rw [SysState.run_append, hrun₁, Option.bind_some, hrun₂]
      · rw [List.filterMap_append, hvis₁, hvis₂, List.filterMap_cons]
        cases World.Event.visible ev <;> rfl

namespace World

def arrived (events : List (World.Event σ)) : List ReqId :=
  events.filterMap fun
    | .arrive id _ => some id
    | _ => none

def answered (events : List (World.Event σ)) : List ReqId :=
  events.filterMap fun
    | .answer (id, _) => some id
    | _ => none

end World

/-- The server answers no request more often than it arrived: the gate's theorem
`served_answered_le_arrived`, of the gate before the runtime. -/
theorem World.answered_le_arrived {events : List (World.Event σ)} {w : World sys bridge}
    (hrun : (World.init sys bridge).run config events = some w) (id : ReqId) :
    (World.answered events).count id ≤ (World.arrived events).count id := by
  obtain ⟨events', c, hrun', -, hvis⟩ := World.refines hrun
  have hle := _root_.Lanes.Http.served_answered_le_arrived (env := servedEnv) rfl hrun' id
  let inId : Visible (ReqId × Request) (ReqId × Response) → Option ReqId
    | .input (id, _) => some id
    | _ => none
  let outId : Visible (ReqId × Request) (ReqId × Response) → Option ReqId
    | .output (id, _) => some id
    | _ => none
  have harrived : Served.arrived events' = World.arrived events := by
    have h1 : Served.arrived events' = (events'.filterMap Lanes.Event.visible).filterMap inId := by
      simp only [Served.arrived, List.filterMap_filterMap]
      congr 1
      funext ev
      cases ev with
      | input x => cases x; rfl
      | output o => cases o; rfl
      | _ => rfl
    have h2 : World.arrived events = (events.filterMap World.Event.visible).filterMap inId := by
      simp only [World.arrived, List.filterMap_filterMap]
      congr 1
      funext ev
      cases ev with
      | answer a => cases a; rfl
      | _ => rfl
    rw [h1, h2, hvis]
  have hanswered : Served.answered events' = World.answered events := by
    have h1 : Served.answered events' = (events'.filterMap Lanes.Event.visible).filterMap outId := by
      simp only [Served.answered, List.filterMap_filterMap]
      congr 1
      funext ev
      cases ev with
      | input x => cases x; rfl
      | output o => cases o; rfl
      | _ => rfl
    have h2 : World.answered events = (events.filterMap World.Event.visible).filterMap outId := by
      simp only [World.answered, List.filterMap_filterMap]
      congr 1
      funext ev
      cases ev with
      | answer a => cases a; rfl
      | _ => rfl
    rw [h1, h2, hvis]
  rw [← harrived, ← hanswered]
  exact hle

end Front

end Lanes.Http
