import Rookery.Proofs.Reads

/-!
# Limits: the rate limit, exactly once, the bounds

- No account gets more than `maxPerWindow` posts accepted in a window: from a board where its
  window holds `w`, at most `maxPerWindow - w` of any requests are accepted as its posts before
  its window deadline passes (`rate_limit`).
- An API change sent twice with one sequence number is acted on once: the second changes
  nothing and gets the first's answer (`handle_api_again`); another change with that number
  changes nothing either and is answered `reused` (`handle_api_reused`).
- Every bound of `Config` holds of every board the requests and deadlines reach (`Bounded`).
-/

set_option linter.unusedSectionVars false

namespace Rookery

open Lanes

variable {N C : Type} [DecidableEq N] [DecidableEq C]

namespace Board

/-! ## The rate limit -/

/-- Posts accepted in `n`'s current window. -/
def windowOf (b : Board N C) (n : N) : Nat :=
  ((b.get? n).map (·.window)).getD 0

/-- What one request can do to the window of the account it is made as: nothing, or count a
post accepted, which it does only below the limit. -/
inductive Window (max w next : Nat) : Nat → Nat → Prop
  | same : Window max w next w next
  | counted : w < max → Window max w next (w + 1) (next + 1)

theorem Window.counts {max w next w' next' : Nat} (h : Window max w next w' next') :
    (next' = next → w' = w) ∧ (next' ≠ next → w' = w + 1 ∧ w < max) := by
  cases h with
  | same => exact ⟨fun _ => rfl, fun h => absurd rfl h⟩
  | counted hlt => exact ⟨fun h => absurd h (Nat.succ_ne_self _), fun _ => ⟨rfl, hlt⟩⟩

theorem windowOf_of_get? {b : Board N C} {n : N} {p : Profile N C} (h : b.get? n = some p) :
    b.windowOf n = p.window := by
  simp [windowOf, h]

theorem same_set {max : Nat} {b : Board N C} {n : N} {p p' : Profile N C}
    (hp : b.get? n = some p) (hw : p'.window = p.window) :
    Window max (b.windowOf n) b.next ((b.set n p').windowOf n) (b.set n p').next := by
  rw [windowOf_of_get? hp, windowOf_of_get? (get?_set_self hp p'), hw]
  exact .same

variable (config : Config)

theorem act_window {b : Board N C} {n : N} {p : Profile N C} (hp : b.get? n = some p)
    (op : Op N) :
    Window config.maxPerWindow (b.windowOf n) b.next ((b.act config n p op).1.windowOf n)
      (b.act config n p op).1.next := by
  cases op with
  | post body =>
    simp only [act, post]
    split
    · exact .same
    · split
      · exact .same
      · next hw _ =>
        have h := Window.counted (max := config.maxPerWindow) (next := b.next)
          (Nat.lt_of_not_le hw)
        rw [windowOf_of_get? hp]
        have e : ({ b.set n { p with posts := ⟨b.next, body⟩ :: p.posts, window := p.window + 1 }
            with next := b.next + 1 } : Board N C).windowOf n = p.window + 1 :=
          windowOf_of_get? (get?_set_self hp _)
        simp only [e]
        exact h
  | delete id =>
    simp only [act, delete]
    split
    · exact same_set hp rfl
    · exact .same
  | follow whom =>
    simp only [act, follow]
    split
    · exact .same
    · split
      · exact .same
      · split
        · exact .same
        · exact same_set hp rfl
  | unfollow whom => exact same_set hp rfl
  | timeline => exact .same

theorem withSession_window {b : Board N C} {n : N} (session : Sid)
    {f : Profile N C → Board N C × Reply N × Timers}
    (hf : ∀ p, b.get? n = some p → Window config.maxPerWindow (b.windowOf n) b.next
      ((f p).1.windowOf n) (f p).1.next) :
    Window config.maxPerWindow (b.windowOf n) b.next
      ((b.withSession n session f).1.windowOf n) (b.withSession n session f).1.next := by
  unfold withSession
  split
  · next p hp =>
    split
    · exact hf p hp
    · exact .same
  · exact .same

theorem handle_window (b : Board N C) (r : Request N C) :
    Window config.maxPerWindow (b.windowOf r.name) b.next ((b.handle config r).1.windowOf r.name)
      (b.handle config r).1.next := by
  cases r with
  | signUp req n c bot =>
    simp only [handle, signUp, Request.name]
    split
    · exact .same
    · next hn =>
      split
      · exact .same
      · have h : ({ b with accounts := b.accounts ++ [(n, { credential := c, bot })] } :
            Board N C).windowOf n = 0 :=
          windowOf_of_get? (p := { credential := c, bot }) (lookup_append_self hn _)
        rw [h, show b.windowOf n = 0 by simp [windowOf, hn]]
        exact .same
  | logIn req n c =>
    simp only [handle, Request.name]
    split
    · next p hp => exact same_set hp (logIn_window ..)
    · exact .same
  | logOut req n session =>
    exact withSession_window config (n := n) session fun p hp => same_set hp rfl
  | newToken req n session =>
    exact withSession_window config (n := n) session fun p hp => same_set hp rfl
  | web req n session op =>
    exact withSession_window config session fun p hp => act_window config hp op
  | api req n token seq op =>
    simp only [handle, Request.name]
    split
    · next p hp =>
      unfold api
      split
      · exact .same
      · split
        · exact act_window config hp op
        · split
          · exact .same
          · exact .same
          · exact act_window config hp op
    · exact .same
  | profile req n json => exact .same

theorem windowOf_handle_ne (b : Board N C) (r : Request N C) {m : N} (hm : m ≠ r.name) :
    (b.handle config r).1.windowOf m = b.windowOf m := by
  simp [windowOf, handle_get?_ne config r hm]

/-- A deadline other than `n`'s window passing leaves `n`'s window as it is; `n`'s empties it. -/
theorem windowOf_fire (b : Board N C) (d : Deadline N) (n : N) :
    (b.fire d).windowOf n = if d = .window n then 0 else b.windowOf n := by
  cases d with
  | window m =>
    simp only [fire, windowOf, get?_update, Deadline.window.injEq]
    by_cases h : n = m
    · subst h; cases b.get? n <;> simp
    · simp [h, Ne.symm h]
  | expire m session =>
    simp only [fire, windowOf, get?_update, reduceCtorEq, ite_false]
    split <;> cases b.get? n <;> rfl
  | unlock m =>
    simp only [fire, windowOf, get?_update, reduceCtorEq, ite_false]
    split
    · cases b.get? n with
      | none => rfl
      | some p => simp only [Option.map_some, Option.getD_some]; split <;> rfl
    · rfl

/-- How many of `es` are accepted as posts of `n`. -/
def accepted (n : N) : Board N C → List (Event N C) → Nat
  | _, [] => 0
  | b, .inl r :: es =>
    (if r.name = n ∧ (b.handle config r).1.next ≠ b.next then 1 else 0)
      + accepted n (b.handle config r).1 es
  | b, .inr d :: es => accepted n (b.fire d) es

/-- The rate limit: of any requests and deadlines in which `n`'s window does not end, no more are
accepted as posts of `n` than its window has room for. -/
theorem rate_limit (n : N) (es : List (Event N C)) (hes : ∀ d, .inr d ∈ es → d ≠ .window n)
    (b : Board N C) (hb : b.windowOf n ≤ config.maxPerWindow) :
    accepted config n b es + b.windowOf n ≤ config.maxPerWindow := by
  induction es generalizing b with
  | nil => simpa [accepted] using hb
  | cons e es ih =>
    have hes' := fun d hd => hes d (List.mem_cons_of_mem _ hd)
    cases e with
    | inr d =>
      have hd := hes d List.mem_cons_self
      have hw : (b.fire d).windowOf n = b.windowOf n := by simp [windowOf_fire, hd]
      simp only [accepted]
      exact hw ▸ ih hes' _ (hw ▸ hb)
    | inl r =>
      simp only [accepted]
      by_cases hn : r.name = n
      · subst hn
        obtain ⟨hsame, hcount⟩ := (handle_window config b r).counts
        by_cases hnext : (b.handle config r).1.next = b.next
        · have hw := hsame hnext
          simp only [hnext, ne_eq, not_true_eq_false, and_false, ite_false, Nat.zero_add]
          exact hw ▸ ih hes' _ (hw ▸ hb)
        · obtain ⟨hw, hlt⟩ := hcount hnext
          have := ih hes' _ (by rw [hw]; exact hlt)
          simp only [hnext, ne_eq, not_false_eq_true, and_self, ite_true]
          rw [hw] at this
          omega
      · have hw := windowOf_handle_ne config b r (Ne.symm hn)
        simp only [hn, false_and, ite_false, Nat.zero_add]
        exact hw ▸ ih hes' _ (hw ▸ hb)

/-! ## Exactly once -/

theorem act_token {b : Board N C} {n : N} {p : Profile N C} (hp : b.get? n = some p) (op : Op N) :
    ∃ p', (b.act config n p op).1.get? n = some p' ∧ p'.token = p.token := by
  cases op with
  | post body =>
    simp only [act, post]
    split
    · exact ⟨p, hp, rfl⟩
    · split
      · exact ⟨p, hp, rfl⟩
      · exact ⟨_, get?_set_self hp _, rfl⟩
  | delete id =>
    simp only [act, delete]
    split
    · exact ⟨_, get?_set_self hp _, rfl⟩
    · exact ⟨p, hp, rfl⟩
  | follow whom =>
    simp only [act, follow]
    split
    · exact ⟨p, hp, rfl⟩
    · split
      · exact ⟨p, hp, rfl⟩
      · split
        · exact ⟨p, hp, rfl⟩
        · exact ⟨_, get?_set_self hp _, rfl⟩
  | unfollow whom => exact ⟨_, get?_set_self hp _, rfl⟩
  | timeline => exact ⟨p, hp, rfl⟩

theorem seen_record {E : Type} (memo : Once.Memo N E) (n : N) (seq : Nat) (effs : List E) :
    (memo.record n seq effs).seen n seq = .again effs := by
  simp [Once.Memo.seen]

/-- A change sent through the API twice with one sequence number is acted on once: the second
time it changes nothing, whatever it asks, and gets the first's answer if it asks the same. -/
theorem handle_api_again (b : Board N C) (req req' : ReqId) (n : N) (token seq : Nat)
    {op op' : Op N} (hop : op ≠ .timeline) (hop' : op' ≠ .timeline) :
    ((b.handle config (.api req n token seq op)).1.handle config (.api req' n token seq op')).1
        = (b.handle config (.api req n token seq op)).1 ∧
      (op' = op → ((b.handle config (.api req n token seq op)).1.handle config
          (.api req' n token seq op')).2.1 = (b.handle config (.api req n token seq op)).2.1) := by
  cases hp : b.get? n with
  | none => simp [Board.handle, hp]
  | some p =>
    simp only [Board.handle, hp]
    unfold api
    by_cases ht : p.token = 0 ∨ token ≠ p.token
    · simp [ht, hp]
    · simp only [ht, hop, ite_false]
      cases hs : b.memo.seen n seq with
      | again replies =>
        simp only [hp, ht, hop', hs, true_and, ite_false]
        rintro rfl
        rfl
      | stale => simp [hp, ht, hop', hs]
      | fresh =>
        obtain ⟨p', hp', htoken⟩ := act_token config hp op
        have hp'' : ({ (b.act config n p op).1 with
            memo := (b.act config n p op).1.memo.record n seq [(op, (b.act config n p op).2.1)] } :
              Board N C).get? n = some p' := hp'
        simp only [hp'', htoken, ht, hop', seen_record, true_and, ite_false]
        rintro rfl
        simp [recalled]

/-- Another change sent through the API with the sequence number of one the board acted on is
refused: it is answered `reused`. -/
theorem handle_api_reused (b : Board N C) (req req' : ReqId) (n : N) (token seq : Nat)
    {op op' : Op N} (hop : op ≠ .timeline) (hop' : op' ≠ .timeline) (hne : op' ≠ op)
    (hacted : (b.handle config (.api req n token seq op)).2.1 ≠ .stale ∧
      (b.handle config (.api req n token seq op)).2.1 ≠ .badToken ∧
      (b.handle config (.api req n token seq op)).2.1 ≠ .reused) :
    ((b.handle config (.api req n token seq op)).1.handle config
      (.api req' n token seq op')).2.1 = .reused := by
  obtain ⟨hs₁, hb₁, hr₁⟩ := hacted
  cases hp : b.get? n with
  | none => simp [Board.handle, hp] at hb₁
  | some p =>
    simp only [Board.handle, hp] at hs₁ hb₁ hr₁ ⊢
    unfold api at hs₁ hb₁ hr₁ ⊢
    by_cases ht : p.token = 0 ∨ token ≠ p.token
    · simp [ht] at hb₁
    · simp only [ht, hop, ite_false] at hs₁ hb₁ hr₁ ⊢
      cases hs : b.memo.seen n seq with
      | again replies =>
        simp only [hs] at hr₁
        obtain ⟨r, rfl⟩ : ∃ r, replies = [(op, r)] := ⟨_, eq_of_recalled_ne hr₁⟩
        simp [hp, ht, hop', hs, recalled, Ne.symm hne]
      | stale => simp [hs] at hs₁
      | fresh =>
        obtain ⟨p', hp', htoken⟩ := act_token config hp op
        have hp'' : ({ (b.act config n p op).1 with
            memo := (b.act config n p op).1.memo.record n seq [(op, (b.act config n p op).2.1)] } :
              Board N C).get? n = some p' := hp'
        simp [hp'', htoken, ht, hop', seen_record, recalled, Ne.symm hne]

/-! ## The bounds -/

/-- Every bound of `Config` on one account. -/
structure Fine (config : Config) (p : Profile N C) : Prop where
  posts : p.posts.length ≤ config.maxPosts
  following : p.following.length ≤ config.maxFollows
  window : p.window ≤ config.maxPerWindow
  sessions : p.sessions.ids.length ≤ config.maxSessions
  attempts : Auth.Attempts.Bounded config.maxFailures p.attempts

/-- Every bound of `Config`: on the number of accounts, and on each. -/
def Bounded (b : Board N C) : Prop :=
  b.accounts.length ≤ config.maxAccounts ∧ ∀ x ∈ b.accounts, Fine config x.2

theorem Bounded.get? {b : Board N C} (h : b.Bounded config) {n : N} {p : Profile N C}
    (hp : b.get? n = some p) : Fine config p :=
  h.2 _ (mem_of_lookup hp)

theorem Bounded.set {b : Board N C} (h : b.Bounded config) {n : N} {p p' : Profile N C}
    (hp : b.get? n = some p) (hp' : Fine config p → Fine config p') :
    (b.set n p').Bounded config := by
  refine ⟨by simpa [Board.set, Board.update, length_modify] using h.1, fun x hx => ?_⟩
  obtain ⟨y, hy, rfl⟩ := mem_modify (show x ∈ modify n (fun _ => p') b.accounts from hx)
  simp only
  split
  · exact hp' (h.get? config hp)
  · exact h.2 y hy

theorem act_bounded {b : Board N C} (h : b.Bounded config) {n : N} {p : Profile N C}
    (hp : b.get? n = some p) (op : Op N) : (b.act config n p op).1.Bounded config := by
  have hf := h.get? config hp
  cases op with
  | post body =>
    simp only [act, post]
    split
    · exact h
    · split
      · exact h
      · next hw hposts =>
        exact h.set config hp fun f =>
          { f with
            posts := by simp only [List.length_cons]; omega
            window := by simp only; omega }
  | delete id =>
    simp only [act, delete]
    split
    · exact h.set config hp fun f =>
        { f with posts := Nat.le_trans (List.length_filter_le _ _) f.posts }
    · exact h
  | follow whom =>
    simp only [act, follow]
    split
    · exact h
    · split
      · exact h
      · split
        · exact h
        · next hmax =>
          exact h.set config hp fun f =>
            { f with following := by simp only [List.length_cons]; omega }
  | unfollow whom =>
    exact h.set config hp fun f =>
      { f with following := Nat.le_trans (List.length_erase_le) f.following }
  | timeline => exact h

theorem Bounded.withSession {b : Board N C} (h : b.Bounded config) {n : N} {session : Sid}
    {f : Profile N C → Board N C × Reply N × Timers}
    (hf : ∀ p, b.get? n = some p → (f p).1.Bounded config) :
    (b.withSession n session f).1.Bounded config := by
  unfold Board.withSession
  split
  · next p hp =>
    split
    · exact hf p hp
    · exact h
  · exact h

theorem close_fine {p : Profile N C} (f : Fine config p) (session : Sid) :
    Fine config { p with sessions := p.sessions.close session } :=
  { f with sessions := Nat.le_trans (Auth.Sessions.length_close_le ..) f.sessions }

theorem logIn_fine (n : N) (req : ReqId) {p : Profile N C} (c : C) (f : Fine config p) :
    Fine config (logIn config n req p c).1 := by
  unfold logIn
  split
  · exact f
  · split
    · exact { f with
        sessions := Auth.Sessions.length_start_le ..
        attempts := Auth.Attempts.bounded_succeed .. }
    · exact { f with attempts := Auth.Attempts.bounded_fail .. }

theorem Bounded.handle {b : Board N C} (h : b.Bounded config) (r : Request N C) :
    (b.handle config r).1.Bounded config := by
  cases r with
  | signUp req n c bot =>
    simp only [Board.handle, signUp]
    split
    · exact h
    · split
      · exact h
      · next hfull =>
        refine ⟨by simp only [List.length_append, List.length_singleton]; omega, fun x hx => ?_⟩
        rcases List.mem_append.mp hx with hx | hx
        · exact h.2 x hx
        · simp only [List.mem_singleton] at hx
          subst hx
          exact ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _,
            by simp [Auth.Attempts.Bounded]; omega⟩
  | logIn req n c =>
    simp only [Board.handle]
    split
    · next p hp => exact h.set config hp (logIn_fine config n req c)
    · exact h
  | logOut req n session =>
    exact h.withSession config fun p hp => h.set config hp fun f => close_fine config f session
  | newToken req n session =>
    exact h.withSession config fun p hp => h.set config hp fun f => { f with }
  | web req n session op => exact h.withSession config fun p hp => act_bounded config h hp op
  | api req n token seq op =>
    simp only [Board.handle]
    split
    · next p hp =>
      unfold api
      split
      · exact h
      · split
        · exact act_bounded config h hp op
        · split
          · exact h
          · exact h
          · exact act_bounded config h hp op
    · exact h
  | profile req n json => exact h

theorem Bounded.update {b : Board N C} (h : b.Bounded config) (n : N)
    {g : Profile N C → Profile N C} (hg : ∀ p, Fine config p → Fine config (g p)) :
    (b.update n g).Bounded config := by
  refine ⟨by simpa [Board.update, length_modify] using h.1, fun x hx => ?_⟩
  obtain ⟨y, hy, rfl⟩ := mem_modify (show x ∈ modify n g b.accounts from hx)
  simp only
  split
  · exact hg _ (h.2 y hy)
  · exact h.2 y hy

theorem Bounded.fire {b : Board N C} (h : b.Bounded config) (d : Deadline N) :
    (b.fire d).Bounded config := by
  cases d with
  | window n => exact h.update config n fun p f => { f with window := Nat.zero_le _ }
  | expire n session => exact h.update config n fun p f => close_fine config f session
  | unlock n =>
    refine h.update config n fun p f => ?_
    split
    · exact { f with attempts := by simp [Auth.Attempts.Bounded, Auth.Attempts.unlock]; omega }
    · exact f

theorem bounded_init : (({} : Board N C)).Bounded config :=
  ⟨Nat.zero_le _, fun x hx => by simp at hx⟩

end Board

end Rookery
