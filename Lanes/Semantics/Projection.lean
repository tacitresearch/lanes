/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Core.Run
public import Lanes.Semantics.Liveness
public import Lanes.Semantics.Seq

/-!
# Fair runs seen through a projection

A leads-to theorem is about the fair runs of one system. When that system is part of a larger
one (one side of a join, a system behind hidden inputs and outputs), the theorem should hold of
it there too. That takes more than a projection of states: the projection of a fair run must be
a run of the part, and a fair one.

A `System.View` says how the states and events of `sys` are seen as those of `sys'`. It
projects (`System.View.Projects`) when every step of `sys` from a reachable state is a finite
run of `sys'` between related states (`System.View.Block`), and the obligations match: what
`sys'` owes in a related state, `sys` owes too (`lift`), a step of `sys` that meets that
obligation meets the obligation of `sys'` in its run, and a step of `sys` that starts its wait
again starts the wait of `sys'` again. Then every fair run of `sys` is seen as a fair run of
`sys'` (`System.View.Projects.fair_run`), and leads-to carries over
(`System.View.Projects.leadsTo`).

The run of `sys'` is made of the finite runs one after another, each followed by one stutter,
so that it is infinite even where `sys` stutters forever (`System.Run.ofBlocks`).

## Main definitions

- `System.Run.ofBlocks`: the run made of finite runs one after the other.
- `SysState.RestartsAlong`: a finite run starts the wait for an obligation again.
- `System.View`, `System.View.Block`, `System.View.Projects`: a projection of runs.
- `System.View.Sees`: a run of `sys` seen as a run of `sys'`.

## Main statements

- `System.View.Projects.fair_run`: every fair run of `sys` is seen as a fair run of `sys'`.
- `System.View.Projects.leadsTo`: what leads to what in `sys'` does so in `sys`.
- `System.View.Sees.shown_after`: what the run of `sys'` shows after a position, the run of
  `sys` shows after the corresponding one.
-/

@[expose] public section

namespace Lanes

variable {σ σ' : Signature}

namespace System.Run

variable {α : Type}

/-- Where the `k`-th of the lists `B` starts when they are put one after the other, each followed
by one more position. -/
def blockStart (B : Nat → List α) : Nat → Nat
  | 0 => 0
  | k + 1 => blockStart B k + (B k).length + 1

/-- The blocks start further on, one after another. -/
theorem blockStart_strictMono (B : Nat → List α) : StrictMono (blockStart B) :=
  StrictMono.of_lt_succ fun k => by simp only [blockStart]; omega

/-- The block that position `p` falls in. -/
def blockOf (B : Nat → List α) (p : Nat) : Nat :=
  segment (blockStart B) p

/-- A position within a block, the position after its last element included, is in that block. -/
theorem blockOf_add (B : Nat → List α) {k j : Nat} (hj : j ≤ (B k).length) :
    blockOf B (blockStart B k + j) = k :=
  segment_range_val (blockStart_strictMono B) (Nat.le_add_right _ _)
    (by simp only [blockStart]; omega)

/-- Every position is in a block. -/
theorem exists_blockStart (B : Nat → List α) (p : Nat) :
    ∃ k j, j ≤ (B k).length ∧ blockStart B k + j = p := by
  have hlo := segment_lower_bound (blockStart_strictMono B) rfl p
  have hhi := segment_upper_bound (blockStart_strictMono B) rfl p
  simp only [blockStart] at hhi
  exact ⟨blockOf B p, p - blockStart B (blockOf B p), by unfold blockOf; omega,
    by unfold blockOf; omega⟩

variable {sys : System σ} {env : EnvModel σ}

/-- The run that takes the finite runs `B` one after the other, from the states `D`, and
stutters after each. -/
def ofBlocks (D : Nat → SysState sys) (B : Nat → List (Event σ))
    (h0 : D 0 = SysState.init sys env) (hrun : ∀ k, (D k).run env (B k) = some (D (k + 1))) :
    sys.Run env where
  state p := ((D (blockOf B p)).run env ((B (blockOf B p)).take
    (p - blockStart B (blockOf B p)))).getD (D (blockOf B p))
  event p := (B (blockOf B p))[p - blockStart B (blockOf B p)]?
  init := by
    have h := blockOf_add B (k := 0) (j := 0) (Nat.zero_le _)
    simp only [blockStart, Nat.zero_add] at h
    simp [h, blockStart, SysState.run, h0]
  exec p := by
    obtain ⟨k, j, hj, rfl⟩ := exists_blockStart B p
    obtain ⟨x, hx, hrest⟩ := SysState.run_take (hrun k) j
    simp only [blockOf_add B hj, Nat.add_sub_cancel_left, hx, Option.getD_some]
    rcases Nat.lt_or_ge j (B k).length with hlt | hge
    · have hj' : j + 1 ≤ (B k).length := hlt
      rw [show blockStart B k + j + 1 = blockStart B k + (j + 1) by omega, blockOf_add B hj',
        Nat.add_sub_cancel_left, List.getElem?_eq_getElem hlt]
      rw [List.drop_eq_getElem_cons hlt, SysState.run] at hrest
      cases hy : x.step env (B k)[j] with
      | none => simp [hy] at hrest
      | some y =>
        have htake : (B k).take (j + 1) = (B k).take j ++ [(B k)[j]] := by simp
        simp only [htake, SysState.run_append, hx, Option.bind_some, SysState.run, hy,
          Option.getD_some]
        exact hy
    · obtain rfl : j = (B k).length := Nat.le_antisymm hj hge
      rw [show blockStart B k + (B k).length + 1 = blockStart B (k + 1) + 0 by
        simp [blockStart], blockOf_add B (Nat.zero_le _), Nat.add_sub_cancel_left]
      rw [List.drop_length, SysState.run, Option.some.injEq] at hrest
      simp [Spec.stutter, SysState.run, hrest]

variable {D : Nat → SysState sys} {B : Nat → List (Event σ)} {h0 : D 0 = SysState.init sys env}
  {hrun : ∀ k, (D k).run env (B k) = some (D (k + 1))}

/-- Within a block, the run is in the states of that block's finite run. -/
theorem ofBlocks_state {k j : Nat} (hj : j ≤ (B k).length) :
    (D k).run env ((B k).take j) = some ((ofBlocks D B h0 hrun).state (blockStart B k + j)) := by
  obtain ⟨x, hx, -⟩ := SysState.run_take (hrun k) j
  simp [ofBlocks, blockOf_add B hj, hx]

/-- Within a block, the run takes that block's events, and stutters after the last. -/
theorem ofBlocks_event {k j : Nat} (hj : j ≤ (B k).length) :
    (ofBlocks D B h0 hrun).event (blockStart B k + j) = (B k)[j]? := by
  simp [ofBlocks, blockOf_add B hj]

/-- The run starts each block in the state the block starts from. -/
theorem ofBlocks_start (k : Nat) : (ofBlocks D B h0 hrun).state (blockStart B k) = D k := by
  have h := ofBlocks_state (h0 := h0) (hrun := hrun) (k := k) (Nat.zero_le _)
  simpa [SysState.run] using h.symm

/-- The events up to the start of a block are the events of the blocks before it, each followed
by a stutter. -/
theorem ofBlocks_take (k : Nat) :
    (ofBlocks D B h0 hrun).event.take (blockStart B (k + 1))
      = (ofBlocks D B h0 hrun).event.take (blockStart B k) ++ ((B k).map some ++ [none]) := by
  have hpart (j : Nat) (hj : j ≤ (B k).length) :
      (ofBlocks D B h0 hrun).event.take (blockStart B k + j)
        = (ofBlocks D B h0 hrun).event.take (blockStart B k) ++ ((B k).take j).map some := by
    induction j with
    | zero => simp
    | succ j ih =>
      have hlt : j < (B k).length := by omega
      rw [← Nat.add_assoc, ωSequence.take_succ', ih (by omega), ofBlocks_event (by omega),
        List.append_assoc, List.take_add_one, List.map_append, List.getElem?_eq_getElem hlt]
      rfl
  rw [show blockStart B (k + 1) = blockStart B k + (B k).length + 1 from rfl, ωSequence.take_succ',
    hpart _ (Nat.le_refl _), ofBlocks_event (Nat.le_refl _), List.getElem?_eq_none (Nat.le_refl _),
    List.take_length, List.append_assoc]

end System.Run

/-- One of the events `evs`, run from `d`, starts the wait for `ob` again. -/
def SysState.RestartsAlong {sys : System σ} (env : EnvModel σ) (d : SysState sys)
    (evs : List (Event σ)) (ob : Obligation σ) : Prop :=
  ∃ j, ∃ hj : j < evs.length, ∃ dj, d.run env (evs.take j) = some dj ∧ ob.Restarted dj evs[j]

/-- How the states, events and obligations of `sys` are seen as those of `sys'`. -/
structure System.View (sys : System σ) (sys' : System σ') (α : Type) where
  /-- The states of `sys'` that a state of `sys` is seen as, between steps. -/
  rel : SysState sys → SysState sys' → Prop
  /-- What each state on the way through a step agrees with: the state before the step or the
  state after it. -/
  near : SysState sys → SysState sys' → Prop
  /-- The obligation of `sys` that stands for an obligation of `sys'`, if there is one. -/
  lift : Obligation σ' → Option (Obligation σ)
  /-- What an event of `sys` shows. -/
  shows : Event σ → Option α
  /-- What an event of `sys'` shows. -/
  shows' : Event σ' → Option α

namespace System.View

variable {sys : System σ} {sys' : System σ'} {α : Type} (v : sys.View sys' α)
  {env : EnvModel σ} {env' : EnvModel σ'}

/-- The run `evs` of `sys'` from `d` to `d'` stands for the step `e` of `sys` from `c` to `c'`,
or for a stutter where `e` is `none`: it shows what the step shows, takes the obligation of
`sys'` whose lift the step takes, starts the wait for it again where the step starts the wait for
its lift again, and passes only through states that agree with `c` or with `c'`. -/
structure Block (env' : EnvModel σ') (c : SysState sys) (e : Option (Event σ))
    (c' : SysState sys) (d : SysState sys') (evs : List (Event σ')) (d' : SysState sys') :
    Prop where
  /-- The run goes from `d` to `d'`. -/
  run : d.run env' evs = some d'
  /-- It ends in a state that `c'` is seen as. -/
  rel : v.rel c' d'
  /-- It shows what the step shows. -/
  shown : evs.filterMap v.shows' = (e.bind v.shows).toList
  /-- It takes the obligation that the step takes the lift of. -/
  taken : ∀ ob' ob, v.lift ob' = some ob → e = some ob.event → ob'.event ∈ evs
  /-- It starts the wait for an obligation again where the step does so for its lift. -/
  restarts : ∀ ob' ob ev, v.lift ob' = some ob → e = some ev → ob.Restarted c ev →
    d.RestartsAlong env' evs ob'
  /-- Each state on the way agrees with `c` or with `c'`. -/
  near : ∀ j dj, d.run env' (evs.take j) = some dj → v.near c dj ∨ v.near c' dj

/-- `v` projects the runs of `sys` under `env` onto runs of `sys'` under `env'`. -/
structure Projects (env : EnvModel σ) (env' : EnvModel σ') : Prop where
  /-- A related state agrees. -/
  near : ∀ c d, v.rel c d → v.near c d
  /-- `sys'` starts with a run that shows nothing and ends where the start of `sys` is seen. -/
  init : ∃ evs d, v.Block env' (SysState.init sys env) none (SysState.init sys env)
    (SysState.init sys' env') evs d
  /-- Every step of `sys` from a reachable state is a run of `sys'`. -/
  step : ∀ c ev c' d, sys.Reachable env c → v.rel c d → c.step env ev = some c' →
    ∃ evs d', v.Block env' c (some ev) c' d evs d'
  /-- What `sys'` owes in a related state, `sys` owes too, as its lift. -/
  due : ∀ c d ob', sys.Reachable env c → v.rel c d → ob'.Due env' d →
    ∃ ob, v.lift ob' = some ob ∧ ob.Due env c

/-- `r'` is `r` seen through `v`: position `n` of `r` is position `f n` of `r'`. -/
structure Sees (r : sys.Run env) (r' : sys'.Run env') (f : Nat → Nat) : Prop where
  /-- Positions keep their order. -/
  mono : StrictMono f
  /-- Each state of `r` is seen as the corresponding state of `r'`. -/
  rel : ∀ n, v.rel (r.state n) (r'.state (f n))
  /-- Every state of `r'` agrees with a state of `r`, at the end of the step it falls in or at
  its start. -/
  near : ∀ p, ∃ n, p < f (n + 1) ∧
    (v.near (r.state n) (r'.state p) ∨ v.near (r.state (n + 1)) (r'.state p))
  /-- What `r'` shows at a position, `r` shows in the step that position falls in. -/
  shown : ∀ p ev' x, r'.event p = some ev' → v.shows' ev' = some x →
    ∃ n, p < f (n + 1) ∧ ∃ ev, r.event n = some ev ∧ v.shows ev = some x
  /-- Up to corresponding positions, the two runs show the same. -/
  deeds : ∀ n, (r'.event.take (f n)).filterMap (·.bind v.shows')
    = (r.event.take n).filterMap (·.bind v.shows)

variable {v}

/-- A stutter of `sys` is the empty run of `sys'`. -/
theorem Projects.stutter (h : v.Projects env env') {c : SysState sys} {d : SysState sys'}
    (hcd : v.rel c d) : v.Block env' c none c d [] d where
  run := rfl
  rel := hcd
  shown := rfl
  taken _ _ _ he := by cases he
  restarts _ _ _ _ he := by cases he
  near j dj hj := by
    simp only [List.take_nil, SysState.run, Option.some.injEq] at hj
    exact .inl (hj ▸ h.near c d hcd)

/-- The run of `sys'` for position `n` of a run of `sys`. -/
theorem Projects.block (h : v.Projects env env') (r : sys.Run env) (n : Nat) (d : SysState sys')
    (hd : v.rel (r.state n) d) :
    ∃ p : List (Event σ') × SysState sys',
      v.Block env' (r.state n) (r.event n) (r.state (n + 1)) d p.1 p.2 := by
  cases hev : r.event n with
  | none =>
    have hs := System.Run.step_none hev
    exact ⟨([], d), by rw [hs]; exact h.stutter hd⟩
  | some ev =>
    obtain ⟨evs, d', hb⟩ := h.step _ ev _ d (r.reachable n) hd (System.Run.step_some hev)
    exact ⟨(evs, d'), hb⟩

/-- The start of the run of `sys'`. -/
theorem Projects.start (h : v.Projects env env') :
    ∃ p : List (Event σ') × SysState sys', v.Block env' (SysState.init sys env) none
      (SysState.init sys env) (SysState.init sys' env') p.1 p.2 :=
  let ⟨evs, d, hb⟩ := h.init
  ⟨(evs, d), hb⟩

/-- The state of `sys'` at the end of the run for position `n` of `r`, and the run. -/
private noncomputable def Projects.stage (h : v.Projects env env') (r : sys.Run env) :
    (n : Nat) → {d : SysState sys' // v.rel (r.state n) d}
  | 0 => ⟨(Classical.choose h.start).2, by rw [r.init]; exact (Classical.choose_spec h.start).rel⟩
  | n + 1 =>
    ⟨(Classical.choose (h.block r n _ (Projects.stage h r n).2)).2,
      (Classical.choose_spec (h.block r n _ (Projects.stage h r n).2)).rel⟩

/-- The run of `sys'` that stands for position `n - 1` of `r`, after the start at `0`. -/
private noncomputable def Projects.blocks (h : v.Projects env env') (r : sys.Run env) :
    Nat → List (Event σ')
  | 0 => (Classical.choose h.start).1
  | n + 1 => (Classical.choose (h.block r n _ (Projects.stage h r n).2)).1

/-- Where the runs of `Projects.blocks` start. -/
private noncomputable def Projects.starts (h : v.Projects env env') (r : sys.Run env) :
    Nat → SysState sys'
  | 0 => SysState.init sys' env'
  | n + 1 => (Projects.stage h r n).1

/-- The run for position `n` stands for the step at `n`. -/
private theorem Projects.blocks_spec (h : v.Projects env env') (r : sys.Run env) (n : Nat) :
    v.Block env' (r.state n) (r.event n) (r.state (n + 1)) (h.starts r (n + 1))
      (h.blocks r (n + 1)) (h.starts r (n + 2)) :=
  Classical.choose_spec (h.block r n _ (Projects.stage h r n).2)

/-- The first run stands for the start. -/
private theorem Projects.blocks_zero (h : v.Projects env env') (r : sys.Run env) :
    v.Block env' (SysState.init sys env) none (SysState.init sys env) (h.starts r 0)
      (h.blocks r 0) (h.starts r 1) :=
  Classical.choose_spec h.start

/-- Each run goes from where it starts to where the next one starts. -/
private theorem Projects.blocks_run (h : v.Projects env env') (r : sys.Run env) (k : Nat) :
    (h.starts r k).run env' (h.blocks r k) = some (h.starts r (k + 1)) := by
  cases k with
  | zero => exact (h.blocks_zero r).run
  | succ n => exact (h.blocks_spec r n).run

/-- The run of `sys'` that `r` is seen as. -/
private noncomputable def Projects.seen (h : v.Projects env env') (r : sys.Run env) :
    sys'.Run env' :=
  System.Run.ofBlocks (h.starts r) (h.blocks r) rfl (h.blocks_run r)

/-- Within a run, the seen run is in that run's states. -/
private theorem Projects.seen_state (h : v.Projects env env') (r : sys.Run env) {k j : Nat}
    (hj : j ≤ (h.blocks r k).length) :
    (h.starts r k).run env' ((h.blocks r k).take j)
      = some ((h.seen r).state (System.Run.blockStart (h.blocks r) k + j)) :=
  System.Run.ofBlocks_state hj

/-- Within a run, the seen run takes that run's events. -/
private theorem Projects.seen_event (h : v.Projects env env') (r : sys.Run env) {k j : Nat}
    (hj : j ≤ (h.blocks r k).length) :
    (h.seen r).event (System.Run.blockStart (h.blocks r) k + j) = (h.blocks r k)[j]? :=
  System.Run.ofBlocks_event hj

/-- What the seen run shows up to the end of a run. -/
private theorem Projects.seen_shows (h : v.Projects env env') (r : sys.Run env) (k : Nat) :
    ((h.seen r).event.take (System.Run.blockStart (h.blocks r) (k + 1))).filterMap
        (·.bind v.shows')
      = ((h.seen r).event.take (System.Run.blockStart (h.blocks r) k)).filterMap (·.bind v.shows')
        ++ (h.blocks r k).filterMap v.shows' := by
  have htake : (h.seen r).event.take (System.Run.blockStart (h.blocks r) (k + 1))
      = (h.seen r).event.take (System.Run.blockStart (h.blocks r) k)
        ++ ((h.blocks r k).map some ++ [none]) := System.Run.ofBlocks_take k
  rw [htake]
  simp [List.filterMap_append, List.filterMap_map, Function.comp_def]

/-- At the end of the run for position `n`, the seen run is in a state that `r.state n` is
seen as. -/
private theorem Projects.seen_rel (h : v.Projects env env') (r : sys.Run env) (n : Nat) :
    v.rel (r.state n) ((h.seen r).state (System.Run.blockStart (h.blocks r) (n + 1))) := by
  have := System.Run.ofBlocks_start (h0 := rfl) (hrun := h.blocks_run r) (n + 1)
  exact this ▸ (Projects.stage h r n).2

/-- A position within a run comes before the next run. -/
private theorem Projects.lt_next (h : v.Projects env env') (r : sys.Run env) {k j : Nat}
    (hj : j ≤ (h.blocks r k).length) :
    System.Run.blockStart (h.blocks r) k + j < System.Run.blockStart (h.blocks r) (k + 1) := by
  show _ < System.Run.blockStart _ k + _ + 1
  omega

/-- Every fair run of `sys` is seen through `v` as a fair run of `sys'`. -/
theorem Projects.fair_run (h : v.Projects env env') {r : sys.Run env} (hfair : r.Fair) :
    ∃ (r' : sys'.Run env') (f : Nat → Nat), r'.Fair ∧ v.Sees r r' f := by
  have hmono : StrictMono fun n => System.Run.blockStart (h.blocks r) (n + 1) :=
    (System.Run.blockStart_strictMono _).comp (StrictMono.add_const 1)
  refine ⟨h.seen r, fun n => System.Run.blockStart (h.blocks r) (n + 1), ?_, hmono,
    h.seen_rel r, fun p => ?_, fun p ev' x hev hx => ?_, fun n => ?_⟩
  · refine System.Run.fair_iff.mpr fun ob' k hdue => ?_
    have hk : k ≤ System.Run.blockStart (h.blocks r) (k + 1) := hmono.le_apply k
    have hle (n : Nat) (hn : k ≤ n) : k ≤ System.Run.blockStart (h.blocks r) (n + 1) :=
      Nat.le_trans hk (hmono.monotone hn)
    obtain ⟨ob, hlift, -⟩ := h.due _ _ ob' (r.reachable k) (h.seen_rel r k) (hdue _ hk).1
    have hdue' (n : Nat) (hn : k ≤ n) : ob.Due env (r.state n) := by
      obtain ⟨ob₂, hlift₂, hdue₂⟩ := h.due _ _ ob' (r.reachable n) (h.seen_rel r n)
        (hdue _ (hle n hn)).1
      exact (Option.some.inj (hlift.symm.trans hlift₂)) ▸ hdue₂
    have hquiet (n : Nat) (hn : k ≤ n) : ¬r.Restarts n ob := by
      rintro ⟨ev, hev, hrestart⟩
      obtain ⟨j, hj, dj, hdj, hrestarted⟩ :=
        (h.blocks_spec r n).restarts ob' ob ev hlift hev hrestart
      refine (hdue _ (Nat.le_trans (hle n hn) (Nat.le_add_right _ j))).2
        ⟨(h.blocks r (n + 1))[j], ?_, ?_⟩
      · rw [h.seen_event r (Nat.le_of_lt hj), List.getElem?_eq_getElem hj]
      · rw [← Option.some.inj ((h.seen_state r (Nat.le_of_lt hj)).symm.trans hdj)] at hrestarted
        exact hrestarted
    obtain ⟨n, hn, hev⟩ := hfair.taken hdue' hquiet
    obtain ⟨j, hj, hjeq⟩ := List.getElem_of_mem ((h.blocks_spec r n).taken ob' ob hlift hev)
    refine ⟨_, Nat.le_trans (hle n hn) (Nat.le_add_right _ j), ?_⟩
    rw [h.seen_event r (Nat.le_of_lt hj), List.getElem?_eq_getElem hj, hjeq]
  · obtain ⟨k, j, hj, rfl⟩ := System.Run.exists_blockStart (h.blocks r) p
    have hp := h.lt_next r hj
    cases k with
    | zero =>
      refine ⟨0, Nat.lt_trans hp (System.Run.blockStart_strictMono _ (Nat.lt_succ_self 1)), ?_⟩
      have := (h.blocks_zero r).near j _ (h.seen_state r hj)
      rw [r.init]
      exact this.elim .inl .inl
    | succ n => exact ⟨n, hp, (h.blocks_spec r n).near j _ (h.seen_state r hj)⟩
  · obtain ⟨k, j, hj, rfl⟩ := System.Run.exists_blockStart (h.blocks r) p
    rw [h.seen_event r hj] at hev
    have hlt : j < (h.blocks r k).length := by
      rcases Nat.lt_or_ge j (h.blocks r k).length with hlt | hge
      · exact hlt
      · rw [List.getElem?_eq_none hge] at hev
        cases hev
    rw [List.getElem?_eq_getElem hlt, Option.some.injEq] at hev
    have hmem : x ∈ (h.blocks r k).filterMap v.shows' :=
      List.mem_filterMap.mpr ⟨_, List.getElem_mem hlt, hev ▸ hx⟩
    have hp := h.lt_next r hj
    cases k with
    | zero =>
      rw [(h.blocks_zero r).shown] at hmem
      cases hmem
    | succ n =>
      rw [(h.blocks_spec r n).shown] at hmem
      cases hrn : r.event n with
      | none => simp [hrn] at hmem
      | some ev =>
        simp only [hrn, Option.bind_some, Option.mem_toList] at hmem
        exact ⟨n, hp, ev, hrn, hmem⟩
  · induction n with
    | zero =>
      rw [h.seen_shows r 0, (h.blocks_zero r).shown]
      simp [System.Run.blockStart]
    | succ n ih =>
      rw [h.seen_shows r (n + 1), ih, (h.blocks_spec r n).shown, ωSequence.take_succ',
        List.filterMap_append]
      cases r.event n with
      | none => simp
      | some ev => cases hs : v.shows ev <;> simp [hs]

/-- What leads to what in `sys'` does so in `sys`: a state of `sys` with `P` is seen as one with
`P'`, and a state of `sys'` with `Q'` agrees only with states of `sys` with `Q`. -/
theorem Projects.leadsTo (h : v.Projects env env') {P Q : SysState sys → Prop}
    {P' Q' : SysState sys' → Prop} (hP : ∀ c d, v.rel c d → P c → P' d)
    (hQ : ∀ c d, v.near c d → Q' d → Q c) (h' : sys'.LeadsTo env' P' Q') :
    sys.LeadsTo env P Q := by
  intro r hfair n hPn
  obtain ⟨r', f, hfair', hsees⟩ := h.fair_run hfair
  obtain ⟨m, hm, hQm⟩ := h' r' hfair' (f n) (hP _ _ (hsees.rel n) hPn)
  obtain ⟨N, hN, hnear⟩ := hsees.near m
  have hn : n ≤ N := Nat.lt_succ_iff.mp (hsees.mono.lt_iff_lt.mp (Nat.lt_of_le_of_lt hm hN))
  rcases hnear with hnear | hnear
  · exact ⟨N, hn, hQ _ _ hnear hQm⟩
  · exact ⟨N + 1, by omega, hQ _ _ hnear hQm⟩

/-- What `r'` shows at a position from `f n` on, `r` shows at a position from `n` on. -/
theorem Sees.shown_after {r : sys.Run env} {r' : sys'.Run env'} {f : Nat → Nat} (hsees : v.Sees r r' f)
    {n p : Nat} (hp : f n ≤ p) {ev' : Event σ'} {x : α} (hev : r'.event p = some ev')
    (hx : v.shows' ev' = some x) :
    ∃ m, n ≤ m ∧ ∃ ev, r.event m = some ev ∧ v.shows ev = some x := by
  obtain ⟨m, hm, ev, hev, hshows⟩ := hsees.shown p ev' x hev hx
  exact ⟨m, Nat.lt_succ_iff.mp (hsees.mono.lt_iff_lt.mp (Nat.lt_of_le_of_lt hp hm)), ev, hev, hshows⟩

end System.View

end Lanes
