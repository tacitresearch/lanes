/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TodoDb

/-!
What the fix rests on, proved of the actor for every state and every message (`keyed := true`):
every request it sends is a `begin`, a read, a `commit` or a `rollback`, or an insert of the to-do
being stored, under the key its user gave it, in the transaction that has just read that key and
found it free (`keyed_requests`). It never asks the store to choose a key, to replace a row or to
delete one (`keyed_no_unkeyed`), and so no output of any run of the system, under any environment,
does (`outputs_noUnkeyed`, through `System.Emits.outputs`).

So a retry after a lost `COMMIT` cannot add a second row: it reads the key first, and if the lost
commit takes effect later, one of the two inserts of the key fails, as the table's primary key
makes it (the premise that the database behaves like the store model). `Check.lean` checks the
whole: no database the store model may be in holds a to-do twice, with lost answers and failures.
-/

namespace TodoDb

open Lanes

variable {cfg : Config}

/-- What an effect asks the store, if it asks it something. -/
def asked : Effect sig .app → Option Request
  | .emit (.store r) => some r
  | _ => none

/-- The requests among some effects. -/
def requests (effects : List (Effect sig .app)) : List Request := effects.filterMap asked

/-- What a request of the fixed actor may be, in state `s` on message `m`: no operation that
adds a row under a key the store chooses, replaces one or deletes one, and an insert only of the
to-do being stored, under its key, on the answer that the key is free. -/
def Keyed (s : State) (m : In) (r : Request) : Prop :=
  match r.op with
  | .append _ | .write .. | .delete _ => False
  | .insert k t => ∃ a, s.current = some a ∧ a.stage = .check ∧ a.key = k ∧ a.title = t
      ∧ r.txn = a.txn ∧ m = .store { id := a.request, answer := .value none }
  | _ => True

/-- Only `begin` is asked. -/
def OnlyBegin (effects : List (Effect sig .app)) : Prop := ∀ r ∈ requests effects, r.op = .begin

theorem attempt_onlyBegin (s : State) (key : Nat) (title : String) (tries : Nat) :
    OnlyBegin (attempt s key title tries).2 := by
  intro r h
  simp [requests, attempt, ask, asked] at h
  subst h
  rfl

theorem next_onlyBegin (s : State) : OnlyBegin (next s).2 := by
  unfold next
  split
  · exact attempt_onlyBegin _ _ _ _
  · intro r h
    simp [requests] at h

theorem finish_onlyBegin (s : State) (key : Nat) (added : Bool) :
    OnlyBegin (finish s (if added then .added key else .gaveUp key)).2 := by
  intro r h
  unfold finish at h
  cases added <;> simpa [requests, asked] using next_onlyBegin _ r (by simpa [requests, asked] using h)

theorem retry_onlyBegin (s : State) (a : Attempt) : OnlyBegin (retry cfg s a).2 := by
  unfold retry
  split
  · exact attempt_onlyBegin _ _ _ _
  · exact finish_onlyBegin s a.key false

theorem keyed_of_onlyBegin {s : State} {m : In} {effects : List (Effect sig .app)}
    (h : OnlyBegin effects) : ∀ r ∈ requests effects, Keyed s m r := by
  intro r hr
  simp [Keyed, h r hr]

theorem ask_requests (s : State) (a : Attempt) (stage : Stage) (op : Store.Op Nat String) :
    requests (ask s a stage op).2 = [{ id := s.nextRequest, txn := a.txn, op }] := by
  simp [requests, ask, asked]

/-- Every request the fixed actor sends is `Keyed`. -/
theorem keyed_requests (hk : cfg.keyed = true) (s : State) (m : In) :
    ∀ r ∈ requests (step cfg s m).2, Keyed s m r := by
  cases m with
  | add key title =>
    simp only [step]
    split
    · intro r hr
      simp [requests, asked] at hr
    · exact keyed_of_onlyBegin (next_onlyBegin _)
  | store reply =>
    simp only [step]
    split
    · rename_i a hcur
      split
      · rename_i hid
        unfold answered
        split
        · exact keyed_of_onlyBegin (retry_onlyBegin _ _)
        · exact keyed_of_onlyBegin (retry_onlyBegin _ _)
        · split
          · simp only [hk, ↓reduceIte]
            intro r hr
            rw [ask_requests] at hr
            simp only [List.mem_singleton] at hr
            subst hr
            simp [Keyed]
          · intro r hr
            simp only [requests, List.filterMap_cons, asked, List.mem_cons] at hr
            rcases hr with rfl | hr
            · simp [Keyed]
            · exact keyed_of_onlyBegin (finish_onlyBegin _ a.key true) r hr
          · intro r hr
            rw [ask_requests] at hr
            simp only [List.mem_singleton] at hr
            subst hr
            refine ⟨a, hcur, by assumption, rfl, rfl, rfl, ?_⟩
            cases reply
            simp_all
          · exact keyed_of_onlyBegin (retry_onlyBegin _ _)
          · intro r hr
            rw [ask_requests] at hr
            simp only [List.mem_singleton] at hr
            subst hr
            simp [Keyed]
          · exact keyed_of_onlyBegin (finish_onlyBegin _ a.key true)
          · exact keyed_of_onlyBegin (retry_onlyBegin _ _)
      · intro r hr
        simp [requests] at hr
    · intro r hr
      simp [requests] at hr

/-- The fixed actor never asks the store to append, to replace or to delete. -/
theorem keyed_no_unkeyed (hk : cfg.keyed = true) (s : State) (m : In) (r : Request)
    (h : r ∈ requests (step cfg s m).2) :
    (∀ v, r.op ≠ .append v) ∧ (∀ k v, r.op ≠ .write k v) ∧ (∀ k, r.op ≠ .delete k) := by
  have := keyed_requests hk s m r h
  refine ⟨fun v hv => ?_, fun k v hv => ?_, fun k hv => ?_⟩ <;> simp [Keyed, hv] at this

/-- An output that adds a row under a key the store chooses, replaces one or deletes one. -/
def NoUnkeyed (out : Out) : Prop :=
  ∀ r, out = .store r → (∀ v, r.op ≠ .append v) ∧ (∀ k v, r.op ≠ .write k v) ∧ (∀ k, r.op ≠ .delete k)

theorem emits_noUnkeyed (hk : cfg.keyed = true) : (system cfg).Emits NoUnkeyed := by
  refine ⟨fun i s msg out h => ?_, fun i s out h => ?_⟩
  · cases i
    intro r hr
    subst hr
    exact keyed_no_unkeyed hk s msg r (List.mem_filterMap.mpr ⟨_, h, rfl⟩)
  · cases i
    simp [system, app] at h

/-- In every run of the fixed system, under every environment, no request it sends appends,
replaces or deletes a row. -/
theorem outputs_noUnkeyed (hk : cfg.keyed = true) {env : EnvModel sig} {events : List (Event sig)}
    {c : SysState (system cfg)} (hrun : (SysState.init (system cfg) env).run env events = some c) :
    ∀ out, Event.output out ∈ events → NoUnkeyed out :=
  (emits_noUnkeyed hk).outputs hrun

end TodoDb
