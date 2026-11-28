/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Check.System

/-!
# Searching a reduced model

A reduction replaces each state the search reaches by a representative, `canon` of it, so that
states the properties cannot tell apart are stored once. Symmetry is the usual case: actors, or
values in the driver, that can be swapped without changing what can happen, with `canon` putting
them in a fixed order.

`Model.reduce` is the model seen through `canon`, which `Check.search` explores like any other.
`Lanes.Check.ReduceSound` proves that a pass of the reduced model is a pass of the model, when
`canon` is a `Model.Reduction`: every state is related to its representative by an equivalence
that the properties and the constraint respect and that is a simulation of the model. The
reduced search's counts are those of the reduced model.

`Check.systemReduced` is `Check.system` with a reduction of its worlds.
-/

@[expose] public section

namespace Lanes.Check

variable {S L : Type}

/-- The model seen through `canon`: each state it reaches replaced by `canon` of it. -/
def Model.reduce (m : Model S L) (canon : S → S) : Model S L where
  init := m.init.map canon
  next s := (m.next s).map fun (l, t) => (l, canon t)

variable {σ : Signature} {sys : System σ} {D : Type}

/-- `system`, with each world the search reaches replaced by `canon` of it. A pass is a pass of
`system` when `canon` is a `World.Reduction` (`Check.systemReduced_sound`). -/
def systemReduced [σ.Inspect] (sys : System σ) [sys.Inspect] {D : Type} [BEq D] [Hashable D]
    (sc : Scenario σ D) (canon : World sys D → World sys D) (props : List (Property (World sys D)))
    (opts : Options (World sys D) := {}) : Report (World sys D) (Event σ) :=
  (search ((model sys sc).reduce fun n => .of (canon n.world)) (Node.props props)
    (Node.options opts) Event.kind Event.kinds).map (·.world)

end Lanes.Check
