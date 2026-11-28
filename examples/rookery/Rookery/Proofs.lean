import Rookery
import Lanes.Proofs

/-!
# What is proved

Of every transaction (`handler`), and so, through `Db.invariant`, of every database the store's
model allows at `SERIALIZABLE`, with lost `COMMIT`s, failures, retries, calls taking effect late
and restarts:

- **A request changes only the rows of the account it is made as** (`others_kept`): a row of
  `members`, `posts`, `follows`, `windows`, the failed log-ins or the API changes whose key does
  not name the account is there after the transaction exactly when it was there before. So only
  a post's author deletes it, and no request touches another account's follows, window, failed
  log-ins or remembered changes.
- **Every bound of a member's window and failed log-ins holds** (`bounded_always`): no window
  holds more than `maxPerWindow` posts, and no account more than `maxFailures` failed log-ins,
  an account with that many being locked.
- **A response names the account the request was made as** (`handler_name`), the only one the
  bridge signs a session or a token for.
- **A change sent again with its `seq` is not acted on again** (`api_again`): while its key is
  stored, the transaction writes nothing.

Each works the same way: every operation a transaction may ask satisfies `Good` (`run_good`),
and what every operation keeps, the transaction keeps (`Txn.All.keeps`, `Txn.All.others`).
-/

namespace Rookery

open Lanes Lanes.Db

variable (config : Config)

/-- What an operation writes is under a key `K` admits. -/
def KeyIs (K : Row → Prop) (o : Op) : Prop := ∀ k, o.writtenKey = some k → K k

/-- What an operation writes to the table of `t` reads back as a value `P` admits. -/
def WrittenOk {α : Type} (t : TableOf α) (P : α → Prop) (o : Op) : Prop :=
  ∀ r, o.written = some r → ∀ a, t.ofRow r = some a → P a

def failuresT : TableOf Auth.Rows.AttemptsRow := Auth.Rows.Failures.table config.failures
def sessionsT : TableOf Auth.Rows.SessionRow := Auth.Rows.Sessions.table config.sessions

/-- A window holds no more than `maxPerWindow` posts. -/
def Window.Within (w : Window) : Prop := w.count.toInt ≤ config.maxPerWindow

/-- An operation a request made as `n` may ask: on a table of the schema; a write to a member's
table under a key that names `n`; a window it writes within its bound, and failed log-ins within
theirs. -/
def Good (n : String) (o : Op) : Prop :=
  (o.table = members.table ∧ KeyIs (· = [.text n]) o) ∨
  (o.table = posts.table ∧ KeyIs (·.head? = some (.text n)) o) ∨
  (o.table = follows.table ∧ KeyIs (·.head? = some (.text n)) o) ∨
  (o.table = windows.table ∧ KeyIs (· = [.text n]) o ∧ WrittenOk windows (Window.Within config) o) ∨
  (o.table = counters.table) ∨
  (o.table = keys.table ∧ KeyIs (fun k => ∃ seq, k = [.text (keyOf n seq)]) o) ∨
  (o.table = (failuresT config).table ∧ KeyIs (· = [.text n]) o ∧
    WrittenOk (failuresT config) (fun a => Auth.Attempts.Bounded config.maxFailures a.attempts) o) ∨
  (o.table = (sessionsT config).table)

/-! ## The tables' names are distinct -/

theorem names :
    [members.table.name, posts.table.name, follows.table.name, windows.table.name,
      counters.table.name, keys.table.name, (failuresT config).table.name,
      (sessionsT config).table.name] =
    ["members", "posts", "follows", "windows", "counters", "api_keys", "login_attempts",
      "sessions"] := rfl

example (m : Member) : members.table.keyOf (members.toRow m) = [.text m.name] := rfl
example (p : Post) : posts.table.keyOf (posts.toRow p) = [.text p.author, .int p.id] := rfl

/-! ## What `Good` gives -/

theorem failuresT_name : (failuresT config).table.name = "login_attempts" := rfl
theorem sessionsT_name : (sessionsT config).table.name = "sessions" := rfl

section
variable {config} {n : String} {o : Op}

theorem Good.members (h : Good config n o) : o.WritesWithin members.table (· = [.text n]) := by
  rcases h with ⟨ht, hk⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -, -⟩ | ht | ⟨ht, -⟩ | ⟨ht, -, -⟩ | ht
  · exact fun _ => ⟨ht, hk⟩
  all_goals intro hn; rw [ht] at hn; try simp only [failuresT_name, sessionsT_name] at hn
  all_goals exact absurd hn (by decide)

theorem Good.posts (h : Good config n o) : o.WritesWithin posts.table (·.head? = some (.text n)) := by
  rcases h with ⟨ht, -⟩ | ⟨ht, hk⟩ | ⟨ht, -⟩ | ⟨ht, -, -⟩ | ht | ⟨ht, -⟩ | ⟨ht, -, -⟩ | ht
  case inr.inl => exact fun _ => ⟨ht, hk⟩
  all_goals intro hn; rw [ht] at hn; try simp only [failuresT_name, sessionsT_name] at hn
  all_goals exact absurd hn (by decide)

theorem Good.follows (h : Good config n o) : o.WritesWithin follows.table (·.head? = some (.text n)) := by
  rcases h with ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, hk⟩ | ⟨ht, -, -⟩ | ht | ⟨ht, -⟩ | ⟨ht, -, -⟩ | ht
  case inr.inr.inl => exact fun _ => ⟨ht, hk⟩
  all_goals intro hn; rw [ht] at hn; try simp only [failuresT_name, sessionsT_name] at hn
  all_goals exact absurd hn (by decide)

theorem Good.windows (h : Good config n o) :
    o.table.name = windows.table.name →
      o.table = windows.table ∧ KeyIs (· = [.text n]) o ∧ WrittenOk windows (Window.Within config) o := by
  rcases h with ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, hk, hw⟩ | ht | ⟨ht, -⟩ | ⟨ht, -, -⟩ | ht
  case inr.inr.inr.inl => exact fun _ => ⟨ht, hk, hw⟩
  all_goals intro hn; rw [ht] at hn; try simp only [failuresT_name, sessionsT_name] at hn
  all_goals exact absurd hn (by decide)

theorem Good.keys (h : Good config n o) :
    o.WritesWithin keys.table (fun k => ∃ seq, k = [.text (keyOf n seq)]) := by
  rcases h with ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -, -⟩ | ht | ⟨ht, hk⟩ | ⟨ht, -, -⟩ | ht
  case inr.inr.inr.inr.inr.inl => exact fun _ => ⟨ht, hk⟩
  all_goals intro hn; rw [ht] at hn; try simp only [failuresT_name, sessionsT_name] at hn
  all_goals exact absurd hn (by decide)

theorem Good.failures (h : Good config n o) :
    o.table.name = (failuresT config).table.name →
      o.table = (failuresT config).table ∧ KeyIs (· = [.text n]) o ∧
        WrittenOk (failuresT config) (fun a => Auth.Attempts.Bounded config.maxFailures a.attempts) o := by
  rcases h with ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -, -⟩ | ht | ⟨ht, -⟩ | ⟨ht, hk, hw⟩ | ht
  case inr.inr.inr.inr.inr.inr.inl => exact fun _ => ⟨ht, hk, hw⟩
  all_goals intro hn; rw [ht] at hn; try simp only [failuresT_name, sessionsT_name] at hn
  all_goals exact absurd hn (by decide)

end

/-! ## Each operation rookery asks is `Good` -/

section
variable {config} {n : String}

theorem keyIs_none {K : Row → Prop} {o : Op} (h : o.writtenKey = none) : KeyIs K o :=
  fun k hk => by rw [h] at hk; cases hk

theorem writtenOk_none {β : Type} {t : TableOf β} {P : β → Prop} {o : Op} (h : o.written = none) :
    WrittenOk t P o :=
  fun r hr => by rw [h] at hr; cases hr

theorem good_members (o : Op) (ht : o.table = members.table) (hk : KeyIs (· = [.text n]) o) :
    Good config n o := .inl ⟨ht, hk⟩
theorem good_posts (o : Op) (ht : o.table = posts.table) (hk : KeyIs (·.head? = some (.text n)) o) :
    Good config n o := .inr (.inl ⟨ht, hk⟩)
theorem good_follows (o : Op) (ht : o.table = follows.table) (hk : KeyIs (·.head? = some (.text n)) o) :
    Good config n o := .inr (.inr (.inl ⟨ht, hk⟩))
theorem good_windows (o : Op) (ht : o.table = windows.table) (hk : KeyIs (· = [.text n]) o)
    (hw : WrittenOk windows (Window.Within config) o) : Good config n o := .inr (.inr (.inr (.inl ⟨ht, hk, hw⟩)))
theorem good_counters (o : Op) (ht : o.table = counters.table) : Good config n o :=
  .inr (.inr (.inr (.inr (.inl ht))))
theorem good_keys (o : Op) (ht : o.table = keys.table) (hk : KeyIs (fun k => ∃ seq, k = [.text (keyOf n seq)]) o) :
    Good config n o := .inr (.inr (.inr (.inr (.inr (.inl ⟨ht, hk⟩)))))
theorem good_failures (o : Op) (ht : o.table = (failuresT config).table) (hk : KeyIs (· = [.text n]) o)
    (hw : WrittenOk (failuresT config) (fun a => Auth.Attempts.Bounded config.maxFailures a.attempts) o) :
    Good config n o := .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨ht, hk, hw⟩))))))
theorem good_sessions (o : Op) (ht : o.table = (sessionsT config).table) : Good config n o :=
  .inr (.inr (.inr (.inr (.inr (.inr (.inr ht))))))

/-- A read of a member's table, under any key. -/
macro "read_good" : tactic => `(tactic| first
  | exact good_members _ rfl (keyIs_none rfl)
  | exact good_posts _ rfl (keyIs_none rfl)
  | exact good_follows _ rfl (keyIs_none rfl)
  | exact good_windows _ rfl (keyIs_none rfl) (writtenOk_none rfl)
  | exact good_counters _ rfl
  | exact good_keys _ rfl (keyIs_none rfl)
  | exact good_failures _ rfl (keyIs_none rfl) (writtenOk_none rfl)
  | exact good_sessions _ rfl)

/-- A write to a member's table under its key. -/
macro "write_good" : tactic => `(tactic| first
  | exact good_members _ rfl fun k hk => (Option.some.inj hk).symm
  | exact good_posts _ rfl fun k hk => by cases hk; rfl
  | exact good_follows _ rfl fun k hk => by cases hk; rfl
  | exact good_counters _ rfl
  | exact good_sessions _ rfl)

theorem take_good (c : String) : (take c).All (Good config n) :=
  Txn.All.bind (TableOf.get_all _ _ (by read_good)) fun _ =>
    Txn.All.bind (TableOf.upsert_all _ _ (by write_good)) fun _ => .pure _

end

section
variable {config} {n : String}

/-- A write to a member's table under its key. -/
macro "key_good" : tactic => `(tactic| first
  | exact good_members _ rfl fun k hk => (Option.some.inj hk).symm
  | exact good_posts _ rfl fun k hk => by cases hk; rfl
  | exact good_follows _ rfl fun k hk => by cases hk; rfl
  | exact good_keys _ rfl fun k hk => ⟨_, (Option.some.inj hk).symm⟩
  | exact good_counters _ rfl
  | exact good_sessions _ rfl)

theorem failures_read_good : (Auth.Rows.Failures.read config.failures n).All (Good config n) :=
  Txn.All.bind (TableOf.get_all _ _ (by read_good)) fun _ => .pure _

theorem failures_write_good (hlimit : config.maxFailures < 2 ^ 63) {a : Auth.Attempts}
    (ha : Auth.Attempts.Bounded config.maxFailures a) :
    (Auth.Rows.Failures.write config.failures n a).All (Good config n) :=
  Txn.All.map _ (Txn.All.single (good_failures _ rfl (fun k hk => (Option.some.inj hk).symm)
    fun r hr b hb => by
      simp only [Op.written, Option.some.injEq] at hr
      subst hr
      change (failuresT config).ofRow ((failuresT config).toRow _) = some b at hb
      rw [(failuresT config).ofRow_toRow] at hb
      cases hb
      rw [Auth.Rows.Failures.attempts_of (by have := ha.1; omega)]
      exact ha))

theorem failed_good (hlimit : config.maxFailures < 2 ^ 63) :
    (Auth.Rows.Failures.failed config.failures n).All (Good config n) :=
  Txn.All.bind failures_read_good fun _ =>
    Txn.All.bind (failures_write_good hlimit (Auth.Attempts.bounded_fail _ _)) fun _ => .pure _

theorem succeeded_good (hlimit : config.maxFailures < 2 ^ 63) :
    (Auth.Rows.Failures.succeeded config.failures n).All (Good config n) :=
  Txn.All.bind failures_read_good fun _ => failures_write_good hlimit (Auth.Attempts.bounded_succeed _ _)

theorem unlock_good (hlimit : config.maxFailures < 2 ^ 63) :
    (Auth.Rows.Failures.unlock config.failures n).All (Good config n) :=
  failures_write_good hlimit (by simp [Auth.Attempts.Bounded, Auth.Attempts.unlock]; omega)

theorem locked_good : (Auth.Rows.Failures.locked config.failures n).All (Good config n) :=
  Txn.All.bind failures_read_good fun _ => .pure _

theorem open_good (id at_s : Int64) (u : String) :
    (Auth.Rows.Sessions.open config.sessions id u at_s).All (Good config n) :=
  Txn.All.single (good_sessions _ rfl)

theorem close_good (id : Int64) : (Auth.Rows.Sessions.close config.sessions id).All (Good config n) :=
  Txn.All.map _ (Txn.All.single (good_sessions _ rfl))

theorem ofUser_good (u : String) (limit : Nat) :
    (Auth.Rows.Sessions.ofUser config.sessions u limit).All (Good config n) :=
  TableOf.lookup_all _ _ _ _ (good_sessions _ rfl)

theorem accepts_good (id at_s : Int64) :
    (Auth.Rows.Sessions.accepts config.sessions id at_s).All (Good config n) := by
  refine Txn.All.bind (TableOf.get_all _ _ (good_sessions _ rfl)) fun r => ?_
  split
  · dsimp only
    split
    · exact Txn.All.bind (Txn.All.map _ (Txn.All.single (good_sessions _ rfl))) fun _ => .pure _
    · exact .pure _
  · exact .pure _

syntax "txn_good" : tactic
macro_rules
  | `(tactic| txn_good) => `(tactic| first
    | exact Txn.All.pure _
    | exact Txn.All.abort _
    | exact TableOf.get_all _ _ (by read_good)
    | exact TableOf.scan_all _ _ (by read_good)
    | exact TableOf.lookup_all _ _ _ _ (by read_good)
    | exact TableOf.insert_all _ _ (by key_good)
    | exact TableOf.update_all _ _ (by key_good)
    | exact TableOf.upsert_all _ _ (by key_good)
    | exact TableOf.delete_all _ _ (by key_good)
    | exact take_good _
    | exact failed_good (by assumption)
    | exact succeeded_good (by assumption)
    | exact unlock_good (by assumption)
    | exact locked_good
    | exact open_good _ _ _
    | exact close_good _
    | exact ofUser_good _ _
    | exact accepts_good _ _
    | (refine Txn.All.bind ?_ fun _ => ?_ <;> txn_good)
    | (split <;> txn_good)
    | (dsimp only; txn_good)
    | (refine Txn.All.map _ ?_; txn_good)
    | (refine Txn.All.mapM _ (fun _ => ?_) _; txn_good))

theorem signUp_good (hash : String) (bot : Bool) : (signUp config n hash bot).All (Good config n) := by
  unfold signUp; txn_good

theorem openSession_good (at_s : Int64) : (openSession config at_s n).All (Good config n) := by
  unfold openSession; txn_good

theorem logIn_good (hlimit : config.maxFailures < 2 ^ 63) (at_s : Int64) (checked : Checked) :
    (logIn config at_s n checked).All (Good config n) := by
  unfold logIn
  have := openSession_good (config := config) (n := n) at_s
  txn_good

end

section
variable {config} {n : String}

theorem window_written (hmax : config.maxPerWindow < 2 ^ 63) (s : Int64) {count : Nat}
    (h : count < config.maxPerWindow) :
    WrittenOk windows (Window.Within config)
      (.upsert windows.table (windows.toRow { name := n, start_s := s, count := Int64.ofNat (count + 1) })) :=
  fun r hr w hw => by
    simp only [Op.written, Option.some.injEq] at hr
    subst hr
    rw [windows.ofRow_toRow] at hw
    cases hw
    have hlt : count + 1 < 2 ^ 63 := by omega
    simp only [Window.Within, Int64.toInt_ofNat_of_lt hlt]
    omega

theorem session_good (at_s sid : Int64) : (session config at_s n sid).All (Good config n) :=
  Txn.All.bind (accepts_good _ _) fun _ => .pure _

theorem post_good (hmax : config.maxPerWindow < 2 ^ 63) (at_s : Int64) (body : String) :
    (post config at_s n body).All (Good config n) := by
  unfold post
  refine Txn.All.bind (TableOf.get_all _ _ (by read_good)) fun _ => ?_
  dsimp only
  split
  all_goals
    split
    · exact .pure _
    · next hc =>
      refine Txn.All.bind (TableOf.scan_all _ _ (by read_good)) fun _ => ?_
      split
      · exact .pure _
      · refine Txn.All.bind (take_good _) fun _ => ?_
        refine Txn.All.bind (TableOf.insert_all _ _ (by key_good)) fun _ => ?_
        exact Txn.All.bind (TableOf.upsert_all _ _ (good_windows _ rfl (fun k hk => (Option.some.inj hk).symm)
          (window_written hmax _ (Nat.lt_of_not_le hc)))) fun _ => .pure _

theorem follow_good (whom : String) : (follow config n whom).All (Good config n) := by
  unfold follow; txn_good

theorem postsOf_good (m : String) : (postsOf config m).All (Good config n) := by
  unfold postsOf; txn_good

theorem timeline_good : (timeline config n).All (Good config n) := by
  unfold timeline
  refine Txn.All.bind (TableOf.scan_all _ _ (by read_good)) fun _ => ?_
  exact Txn.All.bind (Txn.All.mapM _ (fun m => postsOf_good m) _) fun _ => .pure _

theorem act_good (hmax : config.maxPerWindow < 2 ^ 63) (at_s : Int64) (op : Action) :
    (act config at_s n op).All (Good config n) := by
  cases op with
  | post body => exact post_good hmax at_s body.val
  | delete id => unfold act; txn_good
  | follow whom => exact follow_good whom.val
  | unfollow whom => unfold act; txn_good
  | timeline => exact Txn.All.map _ timeline_good

theorem change_good (hmax : config.maxPerWindow < 2 ^ 63) (at_s : Int64) (m : Member) (seq : Int64)
    (op : Action) : (change config at_s n m seq op).All (Good config n) := by
  unfold change
  refine Txn.All.bind ?_ fun _ => by split; exact .pure _
  unfold Keys.once
  refine Txn.All.bind (TableOf.get_all _ _ (by read_good)) fun found => ?_
  split
  · exact .pure _
  · refine Txn.All.bind ?_ fun a => Txn.All.bind (TableOf.insert_all _ _ (by key_good)) fun ok => by
      split
      · exact .pure _
      · exact .abort _
    refine Txn.All.bind (act_good hmax at_s op) fun reply => ?_
    dsimp only
    split
    · exact Txn.All.bind (TableOf.delete_all _ _ (by key_good)) fun _ =>
        Txn.All.bind (TableOf.update_all _ _ (by key_good)) fun _ => .pure _
    · exact .pure _

theorem api_good (hmax : config.maxPerWindow < 2 ^ 63) (at_s token seq : Int64) (op : Action) :
    (api config at_s n token seq op).All (Good config n) := by
  unfold api
  have := act_good (config := config) (n := n) hmax at_s op
  have := change_good (config := config) (n := n) hmax at_s
  refine Txn.All.bind (TableOf.get_all _ _ (by read_good)) fun _ => ?_
  split
  · exact .pure _
  · split
    · exact .pure _
    · split
      · assumption
      · split
        · exact .pure _
        · apply change_good hmax

end

/-- Every operation of every transaction of a request is `Good` for the account it is made as. -/
theorem run_good (hlimit : config.maxFailures < 2 ^ 63) (hmax : config.maxPerWindow < 2 ^ 63)
    (at_s : Int64) (r : Request) : (run config at_s r).All (Good config r.name.val) := by
  cases r with
  | signUp n hash bot => exact signUp_good hash bot
  | logIn n checked => exact logIn_good hlimit at_s checked
  | logOut n sid =>
    exact Txn.All.bind (session_good _ _) fun _ => by
      split
      · exact Txn.All.bind (close_good _) fun _ => .pure _
      · exact .pure _
  | newToken n sid =>
    refine Txn.All.bind (session_good _ _) fun _ => ?_
    unfold Request.name
    txn_good
  | web n sid op =>
    exact Txn.All.bind (session_good _ _) fun _ => by
      split
      · exact act_good hmax at_s op
      · exact .pure _
  | api n token seq op => exact api_good hmax at_s token seq op
  | profile n json => exact Txn.All.map _ (postsOf_good _)

theorem handler_good (hlimit : config.maxFailures < 2 ^ 63) (hmax : config.maxPerWindow < 2 ^ 63)
    (a : Ask) : (handler config a).All (Good config a.request.name.val) :=
  Txn.All.bind (run_good config hlimit hmax a.at_s a.request) fun _ => .pure _

/-! ## The claims -/

section
variable (hlimit : config.maxFailures < 2 ^ 63) (hmax : config.maxPerWindow < 2 ^ 63)
include hlimit hmax

/-- **A request changes only the rows of the account it is made as.** In each of `members`,
`windows` and the failed log-ins, a row whose key is not the account's name; in `posts` and
`follows`, a row whose key does not start with it; in the API changes, a row whose key is not a
change of it: each is there after the transaction exactly when it was there before. -/
theorem others_kept (a : Ask) {db : Db} {r : Response} {db' : Db}
    (h : (handler config a).run db = .ok (r, db')) (x : Row) :
    let n := a.request.name.val
    (members.table.keyOf x ≠ [.text n] → (x ∈ db'.rows members.table.name ↔ x ∈ db.rows members.table.name)) ∧
    ((posts.table.keyOf x).head? ≠ some (.text n) → (x ∈ db'.rows posts.table.name ↔ x ∈ db.rows posts.table.name)) ∧
    ((follows.table.keyOf x).head? ≠ some (.text n) →
      (x ∈ db'.rows follows.table.name ↔ x ∈ db.rows follows.table.name)) ∧
    (windows.table.keyOf x ≠ [.text n] → (x ∈ db'.rows windows.table.name ↔ x ∈ db.rows windows.table.name)) ∧
    ((failuresT config).table.keyOf x ≠ [.text n] →
      (x ∈ db'.rows (failuresT config).table.name ↔ x ∈ db.rows (failuresT config).table.name)) ∧
    ((¬ ∃ seq, keys.table.keyOf x = [.text (keyOf n seq)]) →
      (x ∈ db'.rows keys.table.name ↔ x ∈ db.rows keys.table.name)) := by
  have hg := handler_good config hlimit hmax a
  refine ⟨fun hx => ?_, fun hx => ?_, fun hx => ?_, fun hx => ?_, fun hx => ?_, fun hx => ?_⟩
  · exact Txn.All.others (hg.mono fun _ h => h.members) h hx
  · exact Txn.All.others (hg.mono fun _ h => h.posts) h hx
  · exact Txn.All.others (hg.mono fun _ h => h.follows) h hx
  · exact Txn.All.others (hg.mono fun _ h hn => ⟨(h.windows hn).1, (h.windows hn).2.1⟩) h hx
  · exact Txn.All.others (hg.mono fun _ h hn => ⟨(h.failures hn).1, (h.failures hn).2.1⟩) h hx
  · exact Txn.All.others (hg.mono fun _ h => h.keys) h hx

/-- The bounds a member's rows keep: no window holds more than `maxPerWindow` posts, and no
account has more than `maxFailures` failed log-ins, one with that many being locked. -/
def Bounded (db : Db) : Prop :=
  windows.Every (Window.Within config) db ∧
    (failuresT config).Every (fun a => Auth.Attempts.Bounded config.maxFailures a.attempts) db

omit hlimit hmax in
/-- An operation that writes to the table of `t` only values `P` admits keeps every row of it
admitted. -/
theorem every_apply {α : Type} (t : TableOf α) {P : α → Prop} (o : Op)
    (ht : o.table.name = t.table.name → o.table = t.table ∧ WrittenOk t P o)
    {db : Db} {r : o.Ret} {db' : Db} (h : o.apply db = .ok (r, db')) (hP : t.Every P db) :
    t.Every P db' := by
  intro x hx a ha
  rw [Op.rows_apply o h] at hx
  split at hx
  · next hc =>
    obtain ⟨-, hw⟩ := ht hc.2.symm
    rw [← hc.2] at hx
    rcases o.onRows_sub _ x hx with hx | hx
    · exact hP x (hc.2 ▸ hx) a ha
    · exact hw x hx a ha
  · exact hP x hx a ha

theorem preserves : Preserves (handler config) (Bounded config) := fun a =>
  (handler_good config hlimit hmax a).keeps fun _ h _ _ _ hb ha =>
    ⟨every_apply _ _ (fun hn => ⟨(h.windows hn).1, (h.windows hn).2.2⟩) ha hb.1,
      every_apply _ _ (fun hn => ⟨(h.failures hn).1, (h.failures hn).2.2⟩) ha hb.2⟩

omit hlimit hmax in
theorem rows_empty (s : Schema) (name : String) : (Db.empty s).rows name = [] := by
  simp only [Db.empty, Db.rows]
  induction s with
  | nil => rfl
  | cons t s ih =>
    simp only [List.map_cons, List.lookup]
    split
    · rfl
    · exact ih

omit hlimit hmax in
theorem bounded_empty : Bounded config (Db.empty (schema config)) := by
  constructor <;> intro x hx <;> simp [rows_empty] at hx

/-- **Every bound of a member's window and failed log-ins holds** in every database the store
may hold after any run of the front beside the store's model: with lost `COMMIT`s, failures,
calls taking effect late, restarts, and every call still outstanding taking effect. -/
theorem bounded_always (cfg : Db.Config) {events : List (Event sig)} {s : Db.State Ask Response}
    (hrun : (Db.outside cfg (handler config) (Db.empty (schema config)) port).after events = some s) :
    ∀ w ∈ s.worlds, ∀ w' ∈ w.expand (handler config) w.fuel, Bounded config w'.db :=
  Db.invariant cfg port (bounded_empty config) (preserves config hlimit hmax) hrun

end

/-- **A response names the account the request was made as**, the only one the bridge signs a
session or a token for. -/
theorem handler_name (a : Ask) {db : Db} {r : Response} {db' : Db}
    (h : (handler config a).run db = .ok (r, db')) : r.name = a.request.name := by
  obtain ⟨reply, db₁, -, h₂⟩ := Txn.run_bind_ok_inv h
  simp only [Txn.pure_eq, Txn.run_pure, Except.ok.injEq, Prod.mk.injEq] at h₂
  rw [← h₂.1]

/-! ## A change sent again -/

theorem timeline_reads (n : String) : (timeline config n).Reads :=
  (TableOf.scan_reads _ _).bind fun _ =>
    (Txn.Reads.mapM _ (fun _ => TableOf.scan_reads _ _) _).bind fun _ => .pure _

/-- Under a key the database holds, `once` reads, and writes nothing. -/
theorem once_held {A : Type} (k : Keys A) (key : String) (body : Txn A) {db : Db}
    (held : ∃ x ∈ db.rows k.name, k.table.keyOf x = [.text key]) {a : A} {db' : Db}
    (h : (k.once key body).run db = .ok (a, db')) : db' = db := by
  unfold Keys.once at h
  obtain ⟨found, db₁, h₁, h₂⟩ := Txn.run_bind_ok_inv h
  have hdb₁ := (TableOf.get_reads _ _).run h₁
  subst hdb₁
  simp only [TableOf.get] at h₁
  obtain ⟨row, db₂, h₃, h₄⟩ := Txn.run_bind_ok_inv h₁
  have ha := Txn.run_single h₃
  obtain rfl := Op.apply_read _ rfl ha
  have hrow := (Op.apply_ok _ ha).2
  obtain ⟨x, hx, hkx⟩ := held
  have hsome : row.isSome := by
    rw [hrow]
    simp only [Op.onRows, Op.table]
    exact List.find?_isSome.mpr ⟨x, hx, by simp [Table.hasKey, hkx, Keys.rows]⟩
  cases row with
  | none => simp at hsome
  | some r =>
    cases found with
    | some p =>
      simp at h₂
      exact h₂.2.symm
    | none =>
      exfalso
      simp only [Functor.map] at h₄
      obtain ⟨b, db₃, -, h₅⟩ := Txn.run_bind_ok_inv h₄
      simp at h₅

/-- **A change sent again with its `seq` is not acted on again.** While the database holds the
key of an account's change numbered `seq`, the transaction of an API request of that account
with that `seq` writes nothing: it answers what the change was answered, `reused` for another
change, `stale` or `badToken`. -/
theorem api_again (at_s token seq : Int64) (n : Name) (op : Action) {db : Db}
    (held : ∃ x ∈ db.rows keys.name, keys.table.keyOf x = [.text (keyOf n.val seq)]) {r : Response}
    {db' : Db} (h : (handler config ⟨at_s, .api n token seq op⟩).run db = .ok (r, db')) : db' = db := by
  obtain ⟨reply, db₁, h₁, h₂⟩ := Txn.run_bind_ok_inv h
  simp only [Txn.pure_eq, Txn.run_pure, Except.ok.injEq, Prod.mk.injEq] at h₂
  rw [← h₂.2]
  simp only [run, api] at h₁
  obtain ⟨found, db₂, h₃, h₄⟩ := Txn.run_bind_ok_inv h₁
  have hdb₂ := (TableOf.get_reads _ _).run h₃
  subst hdb₂
  split at h₄
  · (simp at h₄; exact h₄.2.symm)
  · split at h₄
    · (simp at h₄; exact h₄.2.symm)
    · split at h₄
      · next hop =>
        subst hop
        exact (Txn.Reads.bind (timeline_reads config _) fun _ => .pure _).run h₄
      · split at h₄
        · (simp at h₄; exact h₄.2.symm)
        · simp only [change] at h₄
          obtain ⟨rem, db₃, h₅, h₆⟩ := Txn.run_bind_ok_inv h₄
          have := once_held keys _ _ held h₅
          subst this
          split at h₆ <;> (simp at h₆; exact h₆.2.symm)

end Rookery
