/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Core.Inspect

/-!
# Joining systems

`System.join a b wiring` is the two systems side by side as one `System`, so the semantics, the
checker, the runtime and every theorem apply to it as to any other. Its actors are those of
both. An output of one that the wiring routes to the other becomes a message to the actor the
other's `accept` names for that input; every other output is an output of the join. Each system
is written and proved on its own, against its own signature, and knows nothing of the other.

`System.filterMapIO` changes what a system's inputs and outputs look like from outside and hides
some of its outputs; `System.mapIO` is the same and hides none.
-/

@[expose] public section

namespace Lanes

variable {σ τ : Signature}

abbrev JoinMsg (σ τ : Signature) : σ.Id ⊕ τ.Id → Type
  | .inl i => σ.Msg i
  | .inr j => τ.Msg j

instance : ∀ i, DecidableEq (JoinMsg σ τ i)
  | .inl i => inferInstanceAs (DecidableEq (σ.Msg i))
  | .inr j => inferInstanceAs (DecidableEq (τ.Msg j))

abbrev JoinState (a : System σ) (b : System τ) : σ.Id ⊕ τ.Id → Type
  | .inl i => a.State i
  | .inr j => b.State j

/-- The actors, inputs and outputs of both signatures, each tagged with its side. -/
abbrev joinSig (σ τ : Signature) : Signature where
  Id := σ.Id ⊕ τ.Id
  Msg := JoinMsg σ τ
  In := σ.In ⊕ τ.In
  Out := σ.Out ⊕ τ.Out

/-- Which outputs of each system are inputs of the other. The rest leave the join. -/
structure Wiring (σ τ : Signature) where
  toRight : σ.Out → Option τ.In := fun _ => none
  toLeft : τ.Out → Option σ.In := fun _ => none

namespace Wiring

def left (w : Wiring σ τ) (b : System τ) {i : σ.Id} :
    Effect σ i → Effect (joinSig σ τ) (.inl i)
  | .send to msg => .send (.inl to) msg
  | .emit out =>
    match w.toRight out with
    | some x => .send (.inr (b.accept x).1) (b.accept x).2
    | none => .emit (.inl out)
  | .after delay_ms msg => .after delay_ms msg
  | .cancel msg => .cancel msg
  | .stop => .stop

def right (w : Wiring σ τ) (a : System σ) {j : τ.Id} :
    Effect τ j → Effect (joinSig σ τ) (.inr j)
  | .send to msg => .send (.inr to) msg
  | .emit out =>
    match w.toLeft out with
    | some x => .send (.inl (a.accept x).1) (a.accept x).2
    | none => .emit (.inr out)
  | .after delay_ms msg => .after delay_ms msg
  | .cancel msg => .cancel msg
  | .stop => .stop

end Wiring

/-- The sender as one side of a join sees it: an actor of that side, or, for an actor of the
other side, whose messages the wiring hands over as inputs, the outside. -/
def Sender.left {α β : Type} : Sender (α ⊕ β) → Sender α
  | .actor (.inl i) => .actor i
  | .actor (.inr _) => .outside
  | .outside => .outside
  | .timer => .timer

def Sender.right {α β : Type} : Sender (α ⊕ β) → Sender β
  | .actor (.inr j) => .actor j
  | .actor (.inl _) => .outside
  | .outside => .outside
  | .timer => .timer

/-- `a` and `b` as one system. An output that `w` routes to the other side is delivered as a
message to the actor that side's `accept` names; what a join preserves is proved in
`Lanes/Proof/JoinSound.lean`. Each side's actors are told their senders as that side sees them
(`Sender.left`, `Sender.right`). -/
abbrev System.join (a : System σ) (b : System τ) (w : Wiring σ τ := {}) :
    System (joinSig σ τ) where
  State := JoinState a b
  actor
    | .inl i => ((a.actor i).mapSrc Sender.left).mapEff fun eff => [w.left b eff]
    | .inr j => ((b.actor j).mapSrc Sender.right).mapEff fun eff => [w.right a eff]
  accept
    | .inl x => ⟨.inl (a.accept x).1, (a.accept x).2⟩
    | .inr y => ⟨.inr (b.accept y).1, (b.accept y).2⟩
  boot := a.boot.map .inl ++ b.boot.map .inr

/-- `σ` with other inputs and outputs. -/
abbrev Signature.withIO (σ : Signature) (In Out : Type) [DecidableEq In] [DecidableEq Out] :
    Signature where
  Id := σ.Id
  Msg := σ.Msg
  In := In
  Out := Out

section MapIO

variable {In Out : Type} [DecidableEq In] [DecidableEq Out]

def Effect.filterMapOut (output : σ.Out → Option Out) {i : σ.Id} :
    Effect σ i → List (Effect (σ.withIO In Out) i)
  | .send to msg => [.send to msg]
  | .emit out =>
    match output out with
    | some shown => [.emit shown]
    | none => []
  | .after delay_ms msg => [.after delay_ms msg]
  | .cancel msg => [.cancel msg]
  | .stop => [.stop]

/-- The same system behind other inputs and outputs: `input` says what each new input means and
`output` how each output is shown. An output for which `output` gives `none` is not put out. A
join keeps in its signature the outputs it has wired, though none is ever put out, and this is
how they leave it. -/
abbrev System.filterMapIO (sys : System σ) (input : In → σ.In) (output : σ.Out → Option Out) :
    System (σ.withIO In Out) where
  State := sys.State
  actor i := (sys.actor i).mapEff (Effect.filterMapOut output)
  accept x := sys.accept (input x)
  boot := sys.boot

/-- `filterMapIO` that hides nothing, and so what is proved of `filterMapIO` is proved of it. -/
abbrev System.mapIO (sys : System σ) (input : In → σ.In) (output : σ.Out → Out) :
    System (σ.withIO In Out) :=
  sys.filterMapIO input (some ∘ output)

end MapIO

instance (priority := low) {α β : Type} [Hashable α] [Hashable β] : Hashable (α ⊕ β) where
  hash
    | .inl a => mixHash 1 (hash a)
    | .inr b => mixHash 2 (hash b)

/-! What the checker needs of a join is what it needs of each side. Instance search cannot find
these by itself for a concrete signature, whose fields it has already unfolded, so each is named
and given in one line: `instance : (joinSig σ τ).Inspect := .join`. -/

@[instance_reducible] def Signature.Inspect.join [σ.Inspect] [τ.Inspect] : (joinSig σ τ).Inspect where
  enumId := inferInstanceAs (Enum (σ.Id ⊕ τ.Id))
  reprId := inferInstanceAs (Repr (σ.Id ⊕ τ.Id))
  hashId := inferInstanceAs (Hashable (σ.Id ⊕ τ.Id))
  reprMsg
    | .inl i => inferInstanceAs (Repr (σ.Msg i))
    | .inr j => inferInstanceAs (Repr (τ.Msg j))
  hashMsg
    | .inl i => inferInstanceAs (Hashable (σ.Msg i))
    | .inr j => inferInstanceAs (Hashable (τ.Msg j))
  reprIn := inferInstanceAs (Repr (σ.In ⊕ τ.In))
  hashIn := inferInstanceAs (Hashable (σ.In ⊕ τ.In))
  reprOut := inferInstanceAs (Repr (σ.Out ⊕ τ.Out))
  hashOut := inferInstanceAs (Hashable (σ.Out ⊕ τ.Out))

@[instance_reducible] def System.Inspect.join {a : System σ} {b : System τ} {w : Wiring σ τ} [a.Inspect] [b.Inspect] :
    (a.join b w).Inspect where
  beqState
    | .inl i => inferInstanceAs (BEq (a.State i))
    | .inr j => inferInstanceAs (BEq (b.State j))
  reprState
    | .inl i => inferInstanceAs (Repr (a.State i))
    | .inr j => inferInstanceAs (Repr (b.State j))
  hashState
    | .inl i => inferInstanceAs (Hashable (a.State i))
    | .inr j => inferInstanceAs (Hashable (b.State j))

@[instance_reducible] def Signature.Inspect.withIO {In Out : Type} [DecidableEq In] [DecidableEq Out] [σ.Inspect]
    [Repr In] [Hashable In] [Repr Out] [Hashable Out] : (σ.withIO In Out).Inspect where
  enumId := inferInstanceAs (Enum σ.Id)
  reprId := inferInstanceAs (Repr σ.Id)
  hashId := inferInstanceAs (Hashable σ.Id)
  reprMsg i := inferInstanceAs (Repr (σ.Msg i))
  hashMsg i := inferInstanceAs (Hashable (σ.Msg i))

@[instance_reducible] def System.Inspect.filterMapIO {In Out : Type} [DecidableEq In]
    [DecidableEq Out] {sys : System σ} [sys.Inspect] {input : In → σ.In}
    {output : σ.Out → Option Out} :
    (sys.filterMapIO input output).Inspect where
  beqState i := inferInstanceAs (BEq (sys.State i))
  reprState i := inferInstanceAs (Repr (sys.State i))
  hashState i := inferInstanceAs (Hashable (sys.State i))

@[instance_reducible] def System.Inspect.mapIO {In Out : Type} [DecidableEq In] [DecidableEq Out]
    {sys : System σ} [sys.Inspect] {input : In → σ.In} {output : σ.Out → Out} :
    (sys.mapIO input output).Inspect :=
  .filterMapIO

end Lanes
