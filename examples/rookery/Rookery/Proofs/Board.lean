import Rookery.Spec
import Rookery.Proofs.Table

/-!
# What one request does to the board

The facts every claim is built from, about `Board.handle` and `Board.fire`, the functions the
spec and the actor both run:

- a request changes only the account it is made as (`handle_get?_ne`), and a deadline changes
  no account's posts (`postsOf_fire`);
- what it does to that account's posts is one of three things (`handle_posts`): nothing; take
  out the posts with an id the request asked to delete; or put a new post first, with the next
  id, and count it.
-/

set_option linter.unusedSectionVars false

namespace Rookery

open Lanes

variable {N C : Type} [DecidableEq N] [DecidableEq C]

namespace Op

def deletes : Op N → Option PostId
  | .delete id => some id
  | _ => none

end Op

namespace Request

/-- The post a request asks to delete, if it asks that. -/
def deletes : Request N C → Option PostId
  | .web _ _ _ op | .api _ _ _ _ op => op.deletes
  | _ => none

end Request

namespace Board

/-- What one request can do to the posts of the account it is made as: nothing, take out the
posts with the id it asks to delete, or put a new post first with the next id. -/
inductive Posts (deletes : Option PostId) (old : List Post) (next : PostId) :
    List Post → PostId → Prop
  | same : Posts deletes old next old next
  | removed {id : PostId} : deletes = some id →
    Posts deletes old next (old.filter (·.id != id)) next
  | added (body : Body) : Posts deletes old next (⟨next, body⟩ :: old) (next + 1)

theorem get?_update (b : Board N C) (n m : N) (f : Profile N C → Profile N C) :
    (b.update n f).get? m = if m = n then (b.get? m).map f else b.get? m :=
  lookup_modify m n f b.accounts

theorem get?_set (b : Board N C) (n m : N) (p : Profile N C) :
    (b.set n p).get? m = if m = n then (b.get? m).map fun _ => p else b.get? m :=
  get?_update b n m _

theorem get?_set_ne (b : Board N C) {n m : N} (h : m ≠ n) (p : Profile N C) :
    (b.set n p).get? m = b.get? m := by
  simp [get?_set, h]

theorem get?_set_self {b : Board N C} {n : N} {p₀ : Profile N C} (h : b.get? n = some p₀)
    (p : Profile N C) : (b.set n p).get? n = some p := by
  simp [get?_set, h]

theorem postsOf_of_get? {b : Board N C} {n : N} {p : Profile N C} (h : b.get? n = some p) :
    b.postsOf n = p.posts := by
  simp [postsOf, h]

theorem postsOf_of_none {b : Board N C} {n : N} (h : b.get? n = none) : b.postsOf n = [] := by
  simp [postsOf, h]

theorem postsOf_set_self {b : Board N C} {n : N} {p₀ : Profile N C} (h : b.get? n = some p₀)
    (p : Profile N C) : (b.set n p).postsOf n = p.posts :=
  postsOf_of_get? (get?_set_self h p)

/-- A log-in changes no post. -/
theorem posts_logIn (config : Config) (n : N) (req : ReqId) (p : Profile N C) (c : C) (at_s : Nat) :
    (logIn config n req p c at_s).1.posts = p.posts := by
  unfold logIn
  split
  · rfl
  · split <;> rfl

theorem logIn_window (config : Config) (n : N) (req : ReqId) (p : Profile N C) (c : C) (at_s : Nat) :
    (logIn config n req p c at_s).1.window = p.window := by
  unfold logIn
  split
  · rfl
  · split <;> rfl

/-! ## A request changes only its own account -/

section Others

variable (config : Config) {b : Board N C} {n m : N} {p : Profile N C}

theorem act_get?_ne (h : m ≠ n) (op : Op N) : (b.act config n p op).1.get? m = b.get? m := by
  cases op with
  | post body =>
    simp only [act, post]
    split
    · rfl
    · split
      · rfl
      · exact get?_set_ne b h _
  | delete id =>
    simp only [act, delete]
    split
    · exact get?_set_ne b h _
    · rfl
  | follow whom =>
    simp only [act, follow]
    split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · exact get?_set_ne b h _
  | unfollow whom => exact get?_set_ne b h _
  | timeline => rfl

theorem withSession_get?_ne (session : Sid)
    {f : Profile N C → Board N C × Reply N × Timers}
    (hf : ∀ p, b.get? n = some p → (f p).1.get? m = b.get? m) :
    (b.withSession n session f).1.get? m = b.get? m := by
  unfold withSession
  split
  · next p hp =>
    split
    · exact hf p hp
    · rfl
  · rfl

theorem api_get?_ne (h : m ≠ n) (token seq : Nat) (op : Op N) :
    (b.api config n p token seq op).1.get? m = b.get? m := by
  unfold api
  split
  · rfl
  · split
    · exact act_get?_ne config h op
    · split
      · rfl
      · rfl
      · exact act_get?_ne config h op

/-- A request changes no account but the one it is made as: not its record, not its posts. -/
theorem handle_get?_ne (r : Request N C) (h : m ≠ r.name) :
    (b.handle config r).1.get? m = b.get? m := by
  cases r with
  | signUp req n c bot =>
    simp only [handle, signUp]
    split
    · rfl
    · split
      · rfl
      · exact lookup_append_of_ne (Ne.symm h) _ _
  | logIn req n c at_s =>
    simp only [handle]
    split
    · exact get?_set_ne b h _
    · rfl
  | logOut req n session => exact withSession_get?_ne session fun _ _ => get?_set_ne b h _
  | newToken req n session at_s => exact withSession_get?_ne session fun _ _ => get?_set_ne b h _
  | web req n session op =>
    exact withSession_get?_ne session fun _ _ => act_get?_ne config h op
  | api req n token seq op =>
    simp only [handle]
    split
    · exact api_get?_ne config h token seq op
    · rfl
  | profile req n json => rfl

end Others

/-! ## What a request does to its own account's posts -/

section Own

variable (config : Config) {b : Board N C} {n : N} {p : Profile N C}

theorem act_posts (hp : b.get? n = some p) (op : Op N) :
    Posts op.deletes (b.postsOf n) b.next ((b.act config n p op).1.postsOf n)
      (b.act config n p op).1.next := by
  rw [postsOf_of_get? hp]
  cases op with
  | post body =>
    simp only [act, post]
    split
    · rw [postsOf_of_get? hp]; exact .same
    · split
      · rw [postsOf_of_get? hp]; exact .same
      · exact (postsOf_set_self hp _).symm ▸ .added body
  | delete id =>
    simp only [act, delete]
    split
    · rw [postsOf_set_self hp]; exact .removed rfl
    · rw [postsOf_of_get? hp]; exact .same
  | follow whom =>
    simp only [act, follow]
    split
    · rw [postsOf_of_get? hp]; exact .same
    · split
      · rw [postsOf_of_get? hp]; exact .same
      · split
        · rw [postsOf_of_get? hp]; exact .same
        · rw [postsOf_set_self hp]; exact .same
  | unfollow whom => simp only [act]; rw [postsOf_set_self hp]; exact .same
  | timeline => simp only [act]; rw [postsOf_of_get? hp]; exact .same

theorem withSession_posts {deletes : Option PostId} (session : Sid)
    {f : Profile N C → Board N C × Reply N × Timers}
    (hf : ∀ p, b.get? n = some p → Posts deletes (b.postsOf n) b.next ((f p).1.postsOf n)
      (f p).1.next) :
    Posts deletes (b.postsOf n) b.next ((b.withSession n session f).1.postsOf n)
      (b.withSession n session f).1.next := by
  unfold withSession
  split
  · next p hp =>
    split
    · exact hf p hp
    · exact .same
  · exact .same

theorem api_posts (hp : b.get? n = some p) (token seq : Nat) (op : Op N) :
    Posts op.deletes (b.postsOf n) b.next ((b.api config n p token seq op).1.postsOf n)
      (b.api config n p token seq op).1.next := by
  unfold api
  split
  · exact .same
  · split
    · exact act_posts config hp op
    · split
      · exact .same
      · exact .same
      · exact act_posts config hp op

/-- What a request does to the posts of the account it is made as: nothing, take out those with
the id it asks to delete, or put a new post first with the next id. -/
theorem handle_posts (r : Request N C) :
    Posts r.deletes (b.postsOf r.name) b.next ((b.handle config r).1.postsOf r.name)
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
            Board N C).postsOf n = [] :=
          postsOf_of_get? (p := { credential := c, bot }) (lookup_append_self hn _)
        rw [postsOf_of_none hn]
        simp only [h]
        exact .same
  | logIn req n c at_s =>
    simp only [handle, Request.name]
    split
    · next p hp =>
      rw [postsOf_set_self hp, posts_logIn, postsOf_of_get? hp]
      exact .same
    · exact .same
  | logOut req n session =>
    exact withSession_posts (n := n) session fun p hp => by
      rw [postsOf_set_self hp, postsOf_of_get? hp]; exact .same
  | newToken req n session at_s =>
    exact withSession_posts (n := n) session fun p hp => by
      rw [postsOf_set_self hp, postsOf_of_get? hp]; exact .same
  | web req n session op => exact withSession_posts session fun p hp => act_posts config hp op
  | api req n token seq op =>
    simp only [handle, Request.name]
    split
    · next p hp => exact api_posts config hp token seq op
    · exact .same
  | profile req n json => exact .same

end Own

theorem postsOf_fire (b : Board N C) (d : Deadline N) (m : N) :
    (b.fire d).postsOf m = b.postsOf m := by
  cases d with
  | window n | expire n session =>
    simp only [fire, postsOf, get?_update]
    split <;> cases b.get? m <;> rfl
  | unlock n =>
    simp only [fire, postsOf, get?_update]
    split
    · cases b.get? m with
      | none => rfl
      | some p => simp only [Option.map_some, Option.getD_some]; split <;> rfl
    · rfl

theorem next_fire (b : Board N C) (d : Deadline N) : (b.fire d).next = b.next := by
  cases d <;> rfl

end Board

end Rookery
