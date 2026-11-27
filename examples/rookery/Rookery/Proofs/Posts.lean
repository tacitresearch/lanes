import Rookery.Proofs.Board

/-!
# Posts: kept, deleted only by their author, gone once deleted

Of every request and deadline, for every board and configuration:

- a post stays until a request made as its author asks to delete it (`handle_keeps`,
  `postsOf_fire`), and so through any sequence of them (`run_keeps`): an accepted post is never
  lost. Through a crash the board keeps its state (`Rookery.Proofs.Refines`), and through
  `kill -9` the journal gives it back (`Lanes.Journal.recover_kernel`, trusted shell);
- a request made as `n` changes no other account (`handle_get?_ne`): only a post's author can
  delete it;
- a post deleted stays gone: no request or deadline gives an account a post with that id again
  (`Gone.handle`, `Gone.fire`), so no read shows it (`Gone.not_mem_feed`).
-/

set_option linter.unusedSectionVars false

namespace Rookery

open Lanes

variable {N C : Type} [DecidableEq N] [DecidableEq C]

namespace Board

namespace Posts

variable {d : Option PostId} {old new : List Post} {next next' : PostId}

theorem keeps (h : Posts d old next new next') {q : Post} (hq : q ∈ old) :
    q ∈ new ∨ d = some q.id := by
  cases h with
  | same => exact .inl hq
  | @removed id hd =>
    by_cases hid : q.id = id
    · exact .inr (hid ▸ hd)
    · exact .inl (List.mem_filter.mpr ⟨hq, by simpa using hid⟩)
  | added body => exact .inl (List.mem_cons_of_mem _ hq)

theorem next_le (h : Posts d old next new next') : next ≤ next' := by
  cases h
  · exact Nat.le_refl _
  · exact Nat.le_refl _
  · exact Nat.le_succ _

/-- A request that moves `next` puts a new post first with the id `next` had. -/
theorem added_of_next (h : Posts d old next new next') (hnext : next' ≠ next) :
    next' = next + 1 ∧ ∃ body, new = ⟨next, body⟩ :: old := by
  cases h with
  | same => exact absurd rfl hnext
  | removed _ => exact absurd rfl hnext
  | added body => exact ⟨rfl, body, rfl⟩

/-- A post that a request takes out leaves no post with its id. -/
theorem gone (h : Posts d old next new next') {q : Post} (hq : q ∈ old) (hgone : q ∉ new) :
    ∀ q' ∈ new, q'.id ≠ q.id := by
  cases h with
  | same => exact absurd hq hgone
  | @removed id _ =>
    have hid : q.id = id := by
      by_cases hne : q.id = id
      · exact hne
      · exact absurd (List.mem_filter.mpr ⟨hq, by simpa using hne⟩) hgone
    intro q' hq'
    have := (List.mem_filter.mp hq').2
    simp only [bne_iff_ne, ne_eq] at this
    exact hid ▸ this
  | added body => exact absurd (List.mem_cons_of_mem _ hq) hgone

/-- What is there after is there before, or is new with the id `next`. -/
theorem new_of_mem (h : Posts d old next new next') {q : Post} (hq : q ∈ new) :
    q ∈ old ∨ (q.id = next ∧ next' = next + 1) := by
  cases h with
  | same => exact .inl hq
  | removed _ => exact .inl (List.mem_filter.mp hq).1
  | added body =>
    rcases List.mem_cons.mp hq with rfl | hq
    · exact .inr ⟨rfl, rfl⟩
    · exact .inl hq

end Posts

variable (config : Config)

/-- A post stays on the board until a request made as its author asks to delete it. -/
theorem handle_keeps (b : Board N C) (r : Request N C) (m : N) {q : Post}
    (hq : q ∈ b.postsOf m) :
    q ∈ (b.handle config r).1.postsOf m ∨ (m = r.name ∧ r.deletes = some q.id) := by
  by_cases hm : m = r.name
  · subst hm
    exact ((handle_posts config r).keeps hq).imp id fun h => ⟨rfl, h⟩
  · left
    simpa [postsOf, handle_get?_ne config r hm] using hq

/-- A request or a deadline passing. -/
abbrev Event (N C : Type) := Request N C ⊕ Deadline N

def apply (b : Board N C) : Event N C → Board N C
  | .inl r => (b.handle config r).1
  | .inr d => b.fire d

def run (b : Board N C) (es : List (Event N C)) : Board N C :=
  es.foldl (apply config) b

/-- An accepted post is never lost: it is on the board after any requests and deadlines, unless
one of them is a request made as its author to delete it. -/
theorem run_keeps (es : List (Event N C)) (b : Board N C) (m : N) {q : Post}
    (hq : q ∈ b.postsOf m)
    (hes : ∀ r, .inl r ∈ es → r.name = m → r.deletes ≠ some q.id) :
    q ∈ (run config b es).postsOf m := by
  induction es generalizing b with
  | nil => exact hq
  | cons e es ih =>
    refine ih _ ?_ fun r hr => hes r (List.mem_cons_of_mem _ hr)
    cases e with
    | inl r =>
      rcases handle_keeps config b r m hq with h | ⟨hm, hd⟩
      · exact h
      · exact absurd hd (hes r List.mem_cons_self hm.symm)
    | inr d => simpa [apply, postsOf_fire] using hq

/-- When a request is accepted as a new post, the post is the account's newest, with the id
`next` had. -/
theorem handle_accepts (b : Board N C) (r : Request N C)
    (h : (b.handle config r).1.next ≠ b.next) :
    (b.handle config r).1.next = b.next + 1 ∧
      ∃ body, (b.handle config r).1.postsOf r.name = ⟨b.next, body⟩ :: b.postsOf r.name :=
  (handle_posts config r).added_of_next h

/-! ## Fresh ids -/

/-- Every post's id is below the next one. -/
def Fresh (b : Board N C) : Prop :=
  ∀ a, ∀ q ∈ b.postsOf a, q.id < b.next

theorem next_le_handle (b : Board N C) (r : Request N C) : b.next ≤ (b.handle config r).1.next :=
  (handle_posts config r).next_le

theorem Fresh.handle {b : Board N C} (h : b.Fresh) (r : Request N C) :
    (b.handle config r).1.Fresh := by
  intro a q hq
  by_cases ha : a = r.name
  · subst ha
    rcases (handle_posts config r).new_of_mem hq with hq | ⟨hid, hnext⟩
    · exact Nat.lt_of_lt_of_le (h _ q hq) (next_le_handle config b r)
    · rw [hid, hnext]; exact Nat.lt_succ_self _
  · have : q ∈ b.postsOf a := by simpa [postsOf, handle_get?_ne config r ha] using hq
    exact Nat.lt_of_lt_of_le (h a q this) (next_le_handle config b r)

theorem Fresh.fire {b : Board N C} (h : b.Fresh) (d : Deadline N) : (b.fire d).Fresh := by
  intro a q hq
  rw [next_fire]
  exact h a q (by simpa [postsOf_fire] using hq)

theorem fresh_init : (({} : Board N C)).Fresh := by
  intro a q hq
  simp [postsOf, get?, lookup] at hq

/-! ## Gone -/

/-- The account `a` has no post with the id `id`, and no post accepted from now on will have
it. -/
def Gone (b : Board N C) (a : N) (id : PostId) : Prop :=
  id < b.next ∧ ∀ q ∈ b.postsOf a, q.id ≠ id

/-- A post that a request takes off its author's account is gone. -/
theorem gone_of_removed {b : Board N C} (hb : b.Fresh) (r : Request N C) {q : Post}
    (hq : q ∈ b.postsOf r.name) (hgone : q ∉ (b.handle config r).1.postsOf r.name) :
    (b.handle config r).1.Gone r.name q.id := by
  exact ⟨Nat.lt_of_lt_of_le (hb _ q hq) (next_le_handle config b r),
    (handle_posts config r).gone hq hgone⟩

theorem Gone.handle {b : Board N C} {a : N} {id : PostId} (h : b.Gone a id)
    (r : Request N C) : (b.handle config r).1.Gone a id := by
  refine ⟨Nat.lt_of_lt_of_le h.1 (next_le_handle config b r), fun q hq => ?_⟩
  by_cases ha : a = r.name
  · subst ha
    rcases (handle_posts config r).new_of_mem hq with hq | ⟨hid, _⟩
    · exact h.2 q hq
    · rw [hid]; exact Nat.ne_of_gt h.1
  · exact h.2 q (by simpa [postsOf, handle_get?_ne config r ha] using hq)

theorem Gone.fire {b : Board N C} {a : N} {id : PostId} (h : b.Gone a id) (d : Deadline N) :
    (b.fire d).Gone a id :=
  ⟨(next_fire b d).symm ▸ h.1, fun q hq => h.2 q (by simpa [postsOf_fire] using hq)⟩

/-- A post gone stays gone through any requests and deadlines. -/
theorem Gone.run {b : Board N C} {a : N} {id : PostId} (h : b.Gone a id) (es : List (Event N C)) :
    (Board.run config b es).Gone a id := by
  induction es generalizing b with
  | nil => exact h
  | cons e es ih =>
    cases e with
    | inl r => exact ih (h.handle config r)
    | inr d => exact ih (h.fire d)

end Board

end Rookery
