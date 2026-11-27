import Lanes.Semantics
import Rookery.Proofs.Refines

/-!
# What is proved of the spec holds of the system's runs

`Rookery.implements` makes every run of the system a run of its spec, and
`System.Implements.history` reads that run as a sequence of `Board.handle` and `Board.fire`
calls, in real-time order. So the statements about the spec's functions become statements about
what the system hands over, in every environment whose link from the outside does not
duplicate:

- `output_secret`: a response carries the secrets of no account but the one its request, which
  arrived before it, was made as, and a read of an account's posts carries none;
- `output_read`: a list of posts handed over is a read, for the request it answers, of a board
  the spec's functions reach: the timeline of the account it was made as, or an account's posts;
- `deleted_unread`: once the system has confirmed a delete made through the web, no read whose
  request arrives afterwards shows that post, when requests have distinct ids, as the server's
  do.
-/

set_option linter.unusedSectionVars false

namespace Rookery

open Lanes

variable {N C : Type} [DecidableEq N] [DecidableEq C] (config : Config)

/-- An act of the spec as an event of `Board.run`. -/
def toEvent : Service.Act (Request N C) (Deadline N) → Board.Event N C
  | .take r => .inl r
  | .fire d => .inr d

theorem play_eq (b : Board N C) (acts : List (Service.Act (Request N C) (Deadline N))) :
    (spec N C config).play b acts = Board.run config b (acts.map toEvent) := by
  induction acts generalizing b with
  | nil => rfl
  | cons a acts ih => cases a <;> exact ih _

theorem sound_run (es : List (Board.Event N C)) {b : Board N C} (h : Sound config b) :
    Sound config (Board.run config b es) := by
  induction es generalizing b with
  | nil => exact h
  | cons e es ih =>
    cases e with
    | inl r => exact ih ((board_inductive config).step b (.request r) h)
    | inr d => exact ih ((board_inductive config).step b (.deadline d) h)

/-- Every board a history of the spec reaches is sound. -/
theorem sound_play (acts : List (Service.Act (Request N C) (Deadline N))) :
    Sound config ((spec N C config).play {} acts) := by
  rw [play_eq]
  exact sound_run config _ (board_inductive config).init

/-- Only a request has outputs, and its one output is its response. -/
theorem act_output {b : Board N C} {a : Service.Act (Request N C) (Deadline N)} {o : Response N}
    (h : o ∈ ((spec N C config).act b a).2) :
    ∃ r, a = .take r ∧ o = ⟨r.req, (b.handle config r).2.1, r.json⟩ := by
  cases a with
  | take r => exact ⟨r, rfl, by simpa [Service.act, spec] using h⟩
  | fire d => simp [Service.act, spec] at h

variable {env : EnvModel (sig N C)} (henv : (env.link none ()).duplicating = false)
  {evs : List (Lanes.Event (sig N C))} {c : SysState (system N C config)}
  (hrun : (SysState.init (system N C config) env).run env evs = some c)

include henv hrun

/-- A response carries the secrets of no account but the one its request, which arrived before
it, was made as, and a read of an account's posts carries none. -/
theorem output_secret {i : ℕ} {o : Response N} (hi : evs[i]? = some (.output o)) {m : N}
    (hm : o.reply.secretOf = some m) :
    ∃ p < i, ∃ r, evs[p]? = some (.input r) ∧ o.req = r.req ∧ m = r.name ∧
      ∀ q n j, r ≠ .profile q n j := by
  obtain ⟨acts, a, ho, harr⟩ := (implements config env henv).produced hrun hi
  obtain ⟨r, rfl, rfl⟩ := act_output config ho
  obtain ⟨hname, hprof⟩ := Board.handle_secret config (sound_play config acts).2.2 hm
  obtain ⟨p, hp, hin⟩ := harr r rfl
  exact ⟨p, hp, r, hin, rfl, hname, hprof⟩

/-- A list of posts handed over is a read, for the request it answers, which arrived before it,
of a board the spec's functions reach. -/
theorem output_read {i : ℕ} {o : Response N} (hi : evs[i]? = some (.output o))
    {list : List (N × Post)} (hfeed : o.reply = .feed list) :
    ∃ p < i, ∃ r, evs[p]? = some (.input r) ∧ o.req = r.req ∧
      ∃ es, (Board.run config {} es).ReadOf config r list := by
  obtain ⟨acts, a, ho, harr⟩ := (implements config env henv).produced hrun hi
  obtain ⟨r, rfl, rfl⟩ := act_output config ho
  obtain ⟨p, hp, hin⟩ := harr r rfl
  refine ⟨p, hp, r, hin, rfl, acts.map toEvent, ?_⟩
  rw [← play_eq]
  exact Board.handle_feed config (sound_play config acts).2.2 hfeed

omit henv hrun in
/-- A delete made through the web and answered `deleted` leaves its post gone. -/
theorem Board.handle_delete_gone {b : Board N C} (hb : b.Fresh) {req : ReqId} {a : N} {s : Sid}
    {id : PostId} (h : (b.handle config (.web req a s (.delete id))).2.1 = .deleted) :
    (b.handle config (.web req a s (.delete id))).1.Gone a id := by
  cases hp : b.get? a with
  | none => simp [Board.handle, Board.withSession, hp] at h
  | some p =>
    by_cases hlive : p.sessions.live s = true
    · by_cases hany : p.posts.any (·.id == id) = true
      · obtain ⟨q, hq, hqid⟩ := List.any_eq_true.mp hany
        have hqid : q.id = id := by simpa using hqid
        have hgone : (b.handle config (.web req a s (.delete id))).1.Gone a q.id :=
          Board.gone_of_removed config hb (.web req a s (.delete id)) (q := q)
            (show q ∈ b.postsOf a by rw [Board.postsOf_of_get? hp]; exact hq)
            (show q ∉ (b.handle config (.web req a s (.delete id))).1.postsOf a by
              simp only [Board.handle, Board.withSession, hp, hlive, ↓reduceIte, Board.act,
                Board.delete, hany]
              rw [Board.postsOf_set_self hp]
              simp [hqid])
        rwa [hqid] at hgone
      · simp [Board.handle, Board.withSession, hp, hlive, Board.act, Board.delete, hany] at h
    · simp [Board.handle, Board.withSession, hp, hlive] at h

/-- Once the system has handed over `deleted` for a delete made through the web, no read whose
request arrives afterwards shows that post, when the requests that arrive have distinct ids. -/
theorem deleted_unread
    (hdistinct : ∀ (p p' : ℕ) (r r' : Request N C), evs[p]? = some (Lanes.Event.input r) →
      evs[p']? = some (Lanes.Event.input r') → r.req = r'.req → p = p')
    {p₁ i p₂ l : ℕ} {req : ReqId} {a : N} {s : Sid} {id : PostId} {json json' : Bool}
    {r₂ : Request N C} {list : List (N × Post)}
    (hdel : evs[p₁]? = some (.input (.web req a s (.delete id))))
    (hconfirm : evs[i]? = some (.output ⟨req, .deleted, json⟩))
    (hread : evs[p₂]? = some (.input r₂)) (hafter : i < p₂)
    (hshown : evs[l]? = some (.output ⟨r₂.req, .feed list, json'⟩)) :
    ∀ x ∈ list, ¬ (x.1 = a ∧ x.2.id = id) := by
  obtain ⟨acts, cut, hex⟩ := (implements config env henv).history hrun
  obtain ⟨k₁, hk₁, a₁, ha₁, ho₁⟩ := hex.shown i _ hconfirm
  obtain ⟨r₁, rfl, heq₁⟩ := act_output config ho₁
  obtain ⟨q₁, hq₁, hcq₁⟩ := hex.taken k₁ r₁ ha₁
  simp only [Response.mk.injEq] at heq₁
  obtain ⟨hreq₁, hdeleted, -⟩ := heq₁
  obtain rfl := hdistinct _ _ _ _ hq₁ hdel hreq₁.symm
  obtain rfl : r₁ = .web req a s (.delete id) := by
    rw [hdel] at hq₁
    simpa using hq₁.symm
  obtain ⟨k₂, hk₂, a₂, ha₂, ho₂⟩ := hex.shown l _ hshown
  obtain ⟨r₂', rfl, heq₂⟩ := act_output config ho₂
  obtain ⟨q₂, hq₂, hcq₂⟩ := hex.taken k₂ r₂' ha₂
  simp only [Response.mk.injEq] at heq₂
  obtain ⟨hreq₂, hfeed, -⟩ := heq₂
  obtain rfl := hdistinct _ _ _ _ hq₂ hread hreq₂.symm
  obtain rfl : r₂' = r₂ := by
    rw [hread] at hq₂
    simpa using hq₂.symm
  have hlt : k₁ + 1 ≤ k₂ := by
    have := hex.mono (i + 1) q₂ hafter
    omega
  have hgone : ((spec N C config).play {} (acts.take (k₁ + 1))).Gone a id := by
    rw [List.take_add_one, ha₁, Option.toList_some, Service.play_concat]
    exact Board.handle_delete_gone config (sound_play config (acts.take k₁)).2.1 hdeleted.symm
  have hgone₂ : ((spec N C config).play {} (acts.take k₂)).Gone a id := by
    rw [show k₂ = (k₁ + 1) + (k₂ - (k₁ + 1)) by omega, List.take_add, Service.play_append,
      play_eq config _ ((acts.drop (k₁ + 1)).take _)]
    exact hgone.run config _
  exact Board.handle_feed_gone config (sound_play config (acts.take k₂)).2.2 hgone₂ hfeed.symm

end Rookery
