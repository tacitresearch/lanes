import Rookery.Proofs.Posts

/-!
# Reads: timelines, deleted posts, secrets

- A timeline is exactly the posts of the account and of the accounts it follows, newest first,
  and the newest of them when there are more than it holds (`mem_feed`, `sorted_timeline`,
  `length_timeline`, `timeline_complete`).
- Every read the board answers is a timeline or an account's posts, as they are now
  (`handle_feed`): an answer the memo of API requests remembers is never a read (`Quiet`). So a
  post that is gone is in no read (`handle_feed_gone`).
- A reply carries the secrets of the account it answers and of no other (`handle_secret`).
-/

set_option linter.unusedSectionVars false

namespace Rookery

open Lanes

variable {N C : Type} [DecidableEq N] [DecidableEq C]

/-- A reply that carries neither a secret nor any post: what the memo may remember. -/
def Reply.quiet {N : Type} : Reply N → Bool
  | .loggedIn .. | .token .. | .feed _ => false
  | _ => true

namespace Board

/-! ## Timelines -/

theorem mem_feed (b : Board N C) (n : N) (following : List N) (x : N × Post) :
    x ∈ b.feed n following ↔ (x.1 = n ∨ x.1 ∈ following) ∧ x.2 ∈ b.postsOf x.1 := by
  obtain ⟨a, q⟩ := x
  simp only [feed, List.mem_mergeSort, List.mem_flatMap, List.mem_cons, List.mem_map,
    Prod.mk.injEq]
  constructor
  · rintro ⟨a', ha', q', hq', rfl, rfl⟩
    exact ⟨ha', hq'⟩
  · rintro ⟨ha, hq⟩
    exact ⟨a, ha, q, hq, rfl, rfl⟩

/-- Newest first: each post is at least as new as every one after it. -/
theorem sorted_feed (b : Board N C) (n : N) (following : List N) :
    (b.feed n following).Pairwise fun x y => y.2.id ≤ x.2.id := by
  have h := List.pairwise_mergeSort (le := fun (x y : N × Post) => decide (y.2.id ≤ x.2.id))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; exact Nat.le_trans hbc hab)
    (fun a b => by
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      exact Nat.le_total _ _)
    ((n :: following).flatMap fun a => (b.postsOf a).map (a, ·))
  exact h.imp fun h => by simpa using h

variable (config : Config)

theorem length_timeline (b : Board N C) (n : N) (following : List N) :
    (b.timeline config n following).length ≤ config.timelineMax :=
  List.length_take_le _ _

theorem sorted_timeline (b : Board N C) (n : N) (following : List N) :
    (b.timeline config n following).Pairwise fun x y => y.2.id ≤ x.2.id :=
  (sorted_feed b n following).sublist (List.take_sublist _ _)

theorem mem_timeline {b : Board N C} {n : N} {following : List N} {x : N × Post}
    (h : x ∈ b.timeline config n following) :
    (x.1 = n ∨ x.1 ∈ following) ∧ x.2 ∈ b.postsOf x.1 :=
  (mem_feed b n following x).mp (List.mem_of_mem_take h)

/-- A post of the account or of one it follows that its timeline leaves out is older than every
post the timeline shows, and the timeline is full. -/
theorem timeline_complete {b : Board N C} {n : N} {following : List N} {x : N × Post}
    (hx : (x.1 = n ∨ x.1 ∈ following) ∧ x.2 ∈ b.postsOf x.1)
    (hout : x ∉ b.timeline config n following) :
    (b.timeline config n following).length = config.timelineMax ∧
      ∀ y ∈ b.timeline config n following, x.2.id ≤ y.2.id := by
  have hfeed := (mem_feed b n following x).mpr hx
  have hsplit := List.take_append_drop config.timelineMax (b.feed n following)
  have hdrop : x ∈ (b.feed n following).drop config.timelineMax := by
    rw [← hsplit] at hfeed
    rcases List.mem_append.mp hfeed with h | h
    · exact absurd h hout
    · exact h
  have hsorted := sorted_feed b n following
  rw [← hsplit, List.pairwise_append] at hsorted
  refine ⟨?_, fun y hy => hsorted.2.2 y hy x hdrop⟩
  have hlen : config.timelineMax < (b.feed n following).length := by
    have := List.length_pos_of_mem hdrop
    rw [List.length_drop] at this
    omega
  simp only [timeline, List.length_take]
  omega

/-! ## What the memo remembers -/

/-- Every answer the memo of API requests remembers is quiet. -/
def Quiet (b : Board N C) : Prop :=
  ∀ e ∈ b.memo.entries, ∀ r ∈ e.2.2, r.quiet = true

theorem quiet_init : (({} : Board N C)).Quiet := by
  intro e he
  simp at he

theorem mem_of_seen {memo : Once.Memo N (Reply N)} {n : N} {seq : Nat} {replies : List (Reply N)}
    (h : memo.seen n seq = .again replies) : ∃ e ∈ memo.entries, e.2.2 = replies := by
  unfold Once.Memo.seen Once.Memo.find? at h
  split at h
  · next last effs heq =>
    split at h
    · cases h
      obtain ⟨e, he, he'⟩ := Option.map_eq_some_iff.mp heq
      exact ⟨e, List.mem_of_find?_eq_some he, by rw [he']⟩
    · split at h <;> cases h
  · cases h

theorem Quiet.headD {b : Board N C} (h : b.Quiet) {n : N} {seq : Nat}
    {replies : List (Reply N)} (hs : b.memo.seen n seq = .again replies) :
    (replies.headD .stale).quiet = true := by
  obtain ⟨e, he, rfl⟩ := mem_of_seen hs
  cases hr : e.2.2 with
  | nil => rfl
  | cons r rs => exact h e he r (hr ▸ List.mem_cons_self)

theorem act_memo (b : Board N C) (n : N) (p : Profile N C) (op : Op N) :
    (b.act config n p op).1.memo = b.memo := by
  cases op with
  | post body => simp only [act, post]; split; rfl; split <;> rfl
  | delete id => simp only [act, delete]; split <;> rfl
  | follow whom => simp only [act, follow]; split; rfl; split; rfl; split <;> rfl
  | unfollow whom | timeline => rfl

theorem act_quiet (b : Board N C) (n : N) (p : Profile N C) {op : Op N} (hop : op ≠ .timeline) :
    (b.act config n p op).2.1.quiet = true := by
  cases op with
  | post body => simp only [act, post]; split; rfl; split <;> rfl
  | delete id => simp only [act, delete]; split <;> rfl
  | follow whom => simp only [act, follow]; split; rfl; split; rfl; split <;> rfl
  | unfollow whom => rfl
  | timeline => exact absurd rfl hop

theorem Quiet.record {b : Board N C} (h : b.Quiet) (n : N) (seq : Nat) {r : Reply N}
    (hr : r.quiet = true) : ∀ e ∈ (b.memo.record n seq [r]).entries, ∀ r' ∈ e.2.2,
      r'.quiet = true := by
  intro e he r' hr'
  simp only [Once.Memo.record, List.mem_cons, List.mem_filter] at he
  rcases he with rfl | ⟨he, _⟩
  · simp only [List.mem_singleton] at hr'
    exact hr' ▸ hr
  · exact h e he r' hr'

theorem Quiet.withSession {b : Board N C} (h : b.Quiet) {n : N} {session : Sid}
    {f : Profile N C → Board N C × Reply N × Timers} (hf : ∀ p, (f p).1.memo = b.memo) :
    (b.withSession n session f).1.Quiet := by
  unfold Board.withSession
  split
  · split
    · intro e he; rw [hf] at he; exact h e he
    · exact h
  · exact h

theorem Quiet.handle {b : Board N C} (h : b.Quiet) (r : Request N C) :
    (b.handle config r).1.Quiet := by
  cases r with
  | signUp req n c bot =>
    simp only [Board.handle, signUp]
    split
    · exact h
    · split
      · exact h
      · exact h
  | logIn req n c at_s => simp only [Board.handle]; split; exact h; exact h
  | logOut req n session | newToken req n session at_s => exact h.withSession fun _ => rfl
  | web req n session op => exact h.withSession fun p => act_memo config b n p op
  | api req n token seq op =>
    simp only [Board.handle]
    split
    · next p _ =>
      unfold api
      split
      · exact h
      · split
        · intro e he; rw [act_memo] at he; exact h e he
        · next hop =>
          split
          · exact h
          · exact h
          · have hq := act_quiet config b n p hop
            intro e he
            simp only [act_memo] at he
            exact h.record n seq hq e he
    · exact h
  | profile req n json => exact h

theorem Quiet.fire {b : Board N C} (h : b.Quiet) (d : Deadline N) : (b.fire d).Quiet := by
  cases d <;> exact h

/-! ## Every read is of the board as it is -/

/-- A read is a timeline of the account it is made as, or the posts of the account it reads. -/
def ReadOf (b : Board N C) (r : Request N C) (list : List (N × Post)) : Prop :=
  (∃ p, b.get? r.name = some p ∧ list = b.timeline config r.name p.following) ∨
    list = ((b.postsOf r.name).map (r.name, ·)).take config.timelineMax

theorem act_feed {b : Board N C} {n : N} {p : Profile N C} {op : Op N} {list : List (N × Post)}
    (h : (b.act config n p op).2.1 = .feed list) : list = b.timeline config n p.following := by
  cases op with
  | post body =>
    simp only [act, post] at h; split at h; cases h; split at h <;> cases h
  | delete id => simp only [act, delete] at h; split at h <;> cases h
  | follow whom =>
    simp only [act, follow] at h; split at h; cases h; split at h; cases h; split at h <;> cases h
  | unfollow whom => cases h
  | timeline => simp only [act, Reply.feed.injEq] at h; exact h.symm

theorem handle_feed {b : Board N C} (hq : b.Quiet) {r : Request N C} {list : List (N × Post)}
    (h : (b.handle config r).2.1 = .feed list) : b.ReadOf config r list := by
  cases r with
  | signUp req n c bot =>
    simp only [handle, signUp] at h; split at h; cases h; split at h <;> cases h
  | logIn req n c at_s =>
    simp only [handle, logIn] at h; split at h
    · split at h; cases h; split at h <;> cases h
    · cases h
  | logOut req n session =>
    simp only [handle, withSession] at h; split at h; split at h <;> cases h; cases h
  | newToken req n session at_s =>
    simp only [handle, withSession] at h; split at h; split at h <;> cases h; cases h
  | web req n session op =>
    simp only [handle, withSession] at h
    split at h
    · next p hp =>
      split at h
      · exact .inl ⟨p, hp, act_feed config h⟩
      · cases h
    · cases h
  | api req n token seq op =>
    simp only [handle] at h
    split at h
    · next p hp =>
      unfold api at h
      split at h
      · cases h
      · split at h
        · exact .inl ⟨p, hp, act_feed config h⟩
        · next hop =>
          split at h
          · next replies hs =>
            have := hq.headD hs
            simp only at h
            rw [h] at this
            cases this
          · cases h
          · have := act_quiet config b n p hop
            simp only at h
            rw [h] at this
            cases this
    · cases h
  | profile req n json =>
    simp only [handle, Reply.feed.injEq] at h
    exact .inr h.symm

/-- A post that is gone is in no read: not in any timeline, not in any account's posts. -/
theorem ReadOf.gone {b : Board N C} {r : Request N C} {list : List (N × Post)}
    (h : b.ReadOf config r list) {a : N} {id : PostId} (hgone : b.Gone a id) :
    ∀ x ∈ list, ¬ (x.1 = a ∧ x.2.id = id) := by
  rintro ⟨a', q⟩ hx ⟨rfl, rfl⟩
  rcases h with ⟨p, _, rfl⟩ | rfl
  · exact hgone.2 q (mem_timeline config hx).2 rfl
  · obtain ⟨⟨a'', q'⟩, hq', heq⟩ := List.mem_map.mp (List.mem_of_mem_take hx)
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    exact hgone.2 _ hq' rfl

/-- A deleted post appears in no read answered after its deletion. -/
theorem handle_feed_gone {b : Board N C} (hq : b.Quiet) {a : N} {id : PostId}
    (hgone : b.Gone a id) {r : Request N C} {list : List (N × Post)}
    (h : (b.handle config r).2.1 = .feed list) : ∀ x ∈ list, ¬ (x.1 = a ∧ x.2.id = id) :=
  (handle_feed config hq h).gone config hgone

/-! ## Secrets -/

omit [DecidableEq N] in
theorem secretOf_of_quiet {r : Reply N} (h : r.quiet = true) : r.secretOf = none := by
  cases r <;> first | rfl | cases h

theorem act_secret (b : Board N C) (n : N) (p : Profile N C) (op : Op N) :
    (b.act config n p op).2.1.secretOf = none := by
  cases op with
  | post body => simp only [act, post]; split; rfl; split <;> rfl
  | delete id => simp only [act, delete]; split <;> rfl
  | follow whom => simp only [act, follow]; split; rfl; split; rfl; split <;> rfl
  | unfollow whom | timeline => rfl

/-- A reply carries the secrets of no account but the one the request is made as, and a read of
an account's posts carries none. -/
theorem handle_secret {b : Board N C} (hq : b.Quiet) {r : Request N C} {m : N}
    (h : (b.handle config r).2.1.secretOf = some m) : m = r.name ∧ ∀ q n j, r ≠ .profile q n j := by
  have nope : ∀ {x : Reply N}, x.secretOf = none → x.secretOf = some m → False := by
    intro x h₁ h₂; rw [h₁] at h₂; cases h₂
  cases r with
  | signUp req n c bot =>
    simp only [Board.handle, signUp] at h; split at h; cases h; split at h <;> cases h
  | logIn req n c at_s =>
    simp only [Board.handle, logIn] at h; split at h
    · split at h
      · cases h
      · split at h
        · simp only [Reply.secretOf, Option.some.injEq] at h
          exact ⟨h.symm, nofun⟩
        · cases h
    · cases h
  | logOut req n session =>
    simp only [Board.handle, withSession] at h; split at h; split at h <;> cases h; cases h
  | newToken req n session at_s =>
    simp only [Board.handle, withSession] at h; split at h
    · split at h
      · simp only [Reply.secretOf, Option.some.injEq] at h
        exact ⟨h.symm, nofun⟩
      · cases h
    · cases h
  | web req n session op =>
    simp only [Board.handle, withSession] at h
    split at h
    · split at h
      · exact (nope (act_secret config b n _ op) h).elim
      · cases h
    · cases h
  | api req n token seq op =>
    simp only [Board.handle] at h
    split at h
    · next p hp =>
      unfold api at h
      split at h
      · cases h
      · split at h
        · exact (nope (act_secret config b n p op) h).elim
        · split at h
          · next replies hs => exact (nope (secretOf_of_quiet (hq.headD hs)) h).elim
          · cases h
          · exact (nope (act_secret config b n p op) h).elim
    · cases h
  | profile req n json => cases h

end Board

end Rookery
