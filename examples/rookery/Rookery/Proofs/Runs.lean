import Lanes.Semantics
import Rookery.Proofs.Traces

/-!
# Posts kept and API changes acted on once, of the system's runs

Two more claims of the spec carried to every run of the system through
`System.Implements.history`, when requests have distinct ids, as the server's do:

- `posted_kept`, `shown_kept`: a post the system answered `posted` to a web post, or showed in
  a read, is on its author's account in the board of every later read, until a request made as
  its author to delete it arrives. A read shows at most `timelineMax` posts, so the post need
  not be in the list handed over: the read is of a board that holds it, and the timeline claims
  (`Board.timeline_complete`) say which posts that read shows;
- `api_once`: of the API changes an account sends with one sequence number, every reply other
  than `stale` and `badToken` is the same: the board acts on one of them, and answers each
  other as it answered that one or refuses it.

An API post answered `posted` is not a trigger of `posted_kept`: a repeat of its `seq` is
answered `posted` from the memo even after the post was deleted.
-/

set_option linter.unusedSectionVars false

namespace Rookery

open Lanes

variable {N C : Type} [DecidableEq N] [DecidableEq C] (config : Config)

/-! ## The memo of API changes -/

namespace Board

/-- After an API change of `n` with sequence number `s` was answered `R`, the memo of `n` holds
a later number, or `s` with `R` first. -/
def MemoAfter (b : Board N C) (n : N) (s : Nat) (R : Reply N) : Prop :=
  ∃ last rs, b.memo.find? n = some (last, rs) ∧ (s < last ∨ (s = last ∧ rs.headD .stale = R))

theorem fire_memo (b : Board N C) (d : Deadline N) : (b.fire d).memo = b.memo := by
  cases d <;> rfl

theorem withSession_memo {b : Board N C} {n : N} {session : Sid}
    {f : Profile N C → Board N C × Reply N × Timers} (hf : ∀ p, (f p).1.memo = b.memo) :
    (b.withSession n session f).1.memo = b.memo := by
  unfold withSession
  split
  · split
    · exact hf _
    · rfl
  · rfl

/-- A request changes the memo only as an API change it acts on: the memo records it. -/
theorem handle_memo (b : Board N C) (r : Request N C) :
    (b.handle config r).1.memo = b.memo ∨ ∃ req n token seq op p reply,
      r = .api req n token seq op ∧ b.memo.seen n seq = .fresh ∧
        (b.handle config r).1.memo = b.memo.record n seq [reply] ∧ b.get? n = some p := by
  cases r with
  | signUp req n c bot =>
    left
    simp only [handle, signUp]
    split
    · rfl
    · split <;> rfl
  | logIn req n c => left; simp only [handle]; split <;> rfl
  | logOut req n session | newToken req n session => exact .inl (withSession_memo fun _ => rfl)
  | web req n session op => exact .inl (withSession_memo fun p => act_memo config b n p op)
  | api req n token seq op =>
    simp only [handle]
    split
    · next p hp =>
      unfold api
      split
      · exact .inl rfl
      · split
        · exact .inl (act_memo config b n p op)
        · split
          · exact .inl rfl
          · exact .inl rfl
          · next hfresh =>
            right
            refine ⟨req, n, token, seq, op, p, (b.act config n p op).2.1, rfl, hfresh, ?_, hp⟩
            simp [act_memo]
    · exact .inl rfl
  | profile req n json => exact .inl rfl

theorem MemoAfter.handle {b : Board N C} {n : N} {s : Nat} {R : Reply N}
    (h : b.MemoAfter n s R) (r : Request N C) : (b.handle config r).1.MemoAfter n s R := by
  obtain ⟨last, rs, hfind, hlast⟩ := h
  rcases handle_memo config b r with hsame | ⟨req, n', token, seq, op, p, reply, rfl, hfresh,
    hmemo, -⟩
  · exact ⟨last, rs, hsame ▸ hfind, hlast⟩
  · unfold MemoAfter
    rw [hmemo]
    by_cases hn : n = n'
    · subst hn
      simp only [Once.Memo.seen, hfind] at hfresh
      refine ⟨seq, [reply], by simp, .inl ?_⟩
      split at hfresh
      · cases hfresh
      · split at hfresh
        · cases hfresh
        · omega
    · exact ⟨last, rs, by rw [Once.Memo.find?_record_of_ne _ _ _ hn]; exact hfind, hlast⟩

theorem MemoAfter.run {b : Board N C} {n : N} {s : Nat} {R : Reply N} (h : b.MemoAfter n s R)
    (es : List (Event N C)) : (Board.run config b es).MemoAfter n s R := by
  induction es generalizing b with
  | nil => exact h
  | cons e es ih =>
    cases e with
    | inl r => exact ih (h.handle config r)
    | inr d =>
      obtain ⟨last, rs, hfind, hlast⟩ := h
      exact ih (b := b.fire d) ⟨last, rs, by rw [fire_memo]; exact hfind, hlast⟩

theorem seen_again {memo : Once.Memo N (Reply N)} {n : N} {s : Nat} {rs : List (Reply N)}
    (h : memo.seen n s = .again rs) : memo.find? n = some (s, rs) := by
  unfold Once.Memo.seen at h
  cases hf : memo.find? n with
  | none => simp [hf] at h
  | some e =>
    obtain ⟨last, effs⟩ := e
    simp only [hf] at h
    split at h
    · next hs =>
      cases h
      rw [hs]
    · split at h <;> cases h

/-- An API change answered with something other than `stale` and `badToken` leaves the memo
of its account with its sequence number and that answer. -/
theorem handle_api_memoAfter (b : Board N C) {req : ReqId} {n : N} {token s : Nat} {op : Op N}
    (hop : op ≠ .timeline) (hstale : (b.handle config (.api req n token s op)).2.1 ≠ .stale)
    (hbad : (b.handle config (.api req n token s op)).2.1 ≠ .badToken) :
    (b.handle config (.api req n token s op)).1.MemoAfter n s
      (b.handle config (.api req n token s op)).2.1 := by
  simp only [handle] at hstale hbad ⊢
  split at hstale
  · next p hp =>
    simp only [hp] at hbad ⊢
    unfold api at hstale hbad ⊢
    split at hstale
    · next ht => simp [ht] at hbad
    · next ht =>
      simp only [ht, hop, ↓reduceIte] at hstale hbad ⊢
      split at hstale
      · next rs hseen =>
        exact ⟨s, rs, seen_again hseen, .inr ⟨rfl, rfl⟩⟩
      · next hseen => simp at hstale
      · next hseen =>
        exact ⟨s, [(act config b n p op).2.1], by simp [act_memo], .inr ⟨rfl, rfl⟩⟩
  · next hp => simp [hp] at hbad

/-- Once the memo of `n` is past an answer `R` to sequence number `s`, an API change of `n` with
`s` is answered `R`, `stale` or `badToken`. -/
theorem MemoAfter.api {b : Board N C} {n : N} {s : Nat} {R : Reply N} (h : b.MemoAfter n s R)
    {req : ReqId} {token : Nat} {op : Op N} (hop : op ≠ .timeline) :
    (b.handle config (.api req n token s op)).2.1 = R ∨
      (b.handle config (.api req n token s op)).2.1 = .stale ∨
      (b.handle config (.api req n token s op)).2.1 = .badToken := by
  obtain ⟨last, rs, hfind, hlast⟩ := h
  simp only [Board.handle]
  split
  · next p hp =>
    unfold Board.api
    split
    · exact .inr (.inr rfl)
    · have hseen : b.memo.seen n s = if s = last then .again rs else if s < last then .stale
          else .fresh := by
        simp [Once.Memo.seen, hfind]
      rw [hseen]
      by_cases hs : s = last
      · simp only [hs, ↓reduceIte]
        rcases hlast with hlt | ⟨-, hR⟩
        · omega
        · exact .inl hR
      · have hlt : s < last := by omega
        simp [hs, hlt]
  · exact .inr (.inr rfl)

/-- A web post answered `posted id` put the post with that id on its author's account. -/
theorem handle_web_posted {b : Board N C} {req : ReqId} {a : N} {s : Sid}
    {body : {s : String // Body.valid s}} {id : PostId}
    (h : (b.handle config (.web req a s (.post body))).2.1 = .posted id) :
    ⟨id, body⟩ ∈ (b.handle config (.web req a s (.post body))).1.postsOf a := by
  cases hp : b.get? a with
  | none => simp [handle, withSession, hp] at h
  | some p =>
    by_cases hlive : p.sessions.live s = true
    · have hw : ¬ config.maxPerWindow ≤ p.window := by
        intro hw; simp [handle, withSession, hp, hlive, act, post, hw] at h
      have hm : ¬ config.maxPosts ≤ p.posts.length := by
        intro hm; simp [handle, withSession, hp, hlive, act, post, hw, hm] at h
      simp only [handle, withSession, hp, hlive, ↓reduceIte, act, post, hw, hm] at h ⊢
      obtain rfl : b.next = id := by simpa using h
      show _ ∈ (b.set a _).postsOf a
      rw [postsOf_set_self hp]
      exact List.mem_cons_self
    · simp [handle, withSession, hp, hlive] at h

/-- Every post a read lists is on the account it is listed under. -/
theorem ReadOf.mem_postsOf {b : Board N C} {r : Request N C} {list : List (N × Post)}
    (h : b.ReadOf config r list) {a : N} {q : Post} (hx : (a, q) ∈ list) : q ∈ b.postsOf a := by
  rcases h with ⟨p, -, rfl⟩ | rfl
  · exact (mem_timeline config hx).2
  · obtain ⟨q', hq', heq⟩ := List.mem_map.mp (List.mem_of_mem_take hx)
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    exact hq'

end Board

/-! ## A history, read from its outputs -/

section History

variable {evs : List (Lanes.Event (sig N C))} {acts : List (Service.Act (Request N C) (Deadline N))}
  {cut : ℕ → ℕ} (hex : System.Implements.Explains (spec N C config) evs acts cut)
  (hdistinct : ∀ (p p' : ℕ) (r r' : Request N C), evs[p]? = some (Lanes.Event.input r) →
    evs[p']? = some (Lanes.Event.input r') → r.req = r'.req → p = p')

include hex

/-- The board after the first `k` acts of the history. -/
abbrev boardAt (acts : List (Service.Act (Request N C) (Deadline N))) (k : ℕ) : Board N C :=
  (spec N C config).play {} (acts.take k)

include hdistinct in
/-- A response handed over is that of an act of the history taking the request that arrived
with its id, before the next position and after the request arrived. -/
theorem take_of_output {i : ℕ} {o : Response N} (hi : evs[i]? = some (.output o)) {p : ℕ}
    {r : Request N C} (hp : evs[p]? = some (.input r)) (hreq : o.req = r.req) :
    ∃ k < cut (i + 1), cut p ≤ k ∧ acts[k]? = some (.take r) ∧
      o = ⟨r.req, ((boardAt config acts k).handle config r).2.1, r.json⟩ := by
  obtain ⟨k, hk, a, ha, ho⟩ := hex.shown i o hi
  obtain ⟨r₁, rfl, rfl⟩ := act_output config ho
  obtain ⟨q, hq, hcq⟩ := hex.taken k r₁ ha
  obtain rfl := hdistinct _ _ _ _ hq hp hreq
  obtain rfl : r₁ = r := by
    rw [hp] at hq
    simpa using hq.symm
  exact ⟨k, hk, hcq, ha, rfl⟩

omit hex in
theorem boardAt_succ {k : ℕ} {r : Request N C} (ha : acts[k]? = some (.take r)) :
    boardAt config acts (k + 1) = ((boardAt config acts k).handle config r).1 := by
  rw [boardAt, List.take_add_one, ha, Option.toList_some, Service.play_concat]
  rfl

omit hex in
/-- The board after more acts of the history is the board before them run through them. -/
theorem boardAt_le {k k' : ℕ} (hk : k ≤ k') :
    boardAt config acts k' =
      Board.run config (boardAt config acts k) (((acts.drop k).take (k' - k)).map toEvent) := by
  rw [boardAt, show k' = k + (k' - k) by omega, List.take_add, Service.play_append,
    play_eq config _ ((acts.drop k).take _)]
  simp

/-- An input that takes effect before an output's act did arrived before that output. -/
theorem arrived_before {l : ℕ} {o : Response N} (hl : evs[l]? = some (.output o)) {k : ℕ}
    (hk : k < cut (l + 1)) {p : ℕ} {x : Request N C} (hp : evs[p]? = some (.input x))
    (hcp : cut p ≤ k) : p < l := by
  by_contra hpl
  have hne : p ≠ l := by
    rintro rfl
    rw [hl] at hp
    cases hp
  have := hex.mono (l + 1) p (by omega)
  omega

/-- An event of the history between two of its positions is an act there. -/
theorem mem_segment {k k' : ℕ} {e : Board.Event N C}
    (he : e ∈ ((acts.drop k).take (k' - k)).map toEvent) :
    ∃ j, k ≤ j ∧ j < k' ∧ ∃ a, acts[j]? = some a ∧ toEvent a = e := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
  obtain ⟨j, hkj, hjk, hj⟩ := mem_take_drop ha
  exact ⟨j, hkj, by omega, a, hj, rfl⟩

/-- A post on its author's account in the board after `k₀` acts is there after `k` acts, if no
request made as its author to delete it arrives before the output at `l` whose act is the `k`th. -/
theorem kept_until {k₀ k : ℕ} (hk : k₀ ≤ k) {a : N} {q : Post}
    (hq : q ∈ (boardAt config acts k₀).postsOf a) {l : ℕ} {o : Response N}
    (hl : evs[l]? = some (.output o)) (hkl : k < cut (l + 1))
    (hkept : ∀ p r, evs[p]? = some (.input r) → p < l → r.name = a → r.deletes ≠ some q.id) :
    q ∈ (boardAt config acts k).postsOf a := by
  rw [boardAt_le config hk]
  refine Board.run_keeps config _ _ a hq fun r hr hname => ?_
  obtain ⟨j, -, hjk, act, hj, hact⟩ := mem_segment config hex hr
  cases act with
  | take x =>
    obtain rfl : x = r := by simpa [toEvent] using hact
    obtain ⟨p, hp, hcp⟩ := hex.taken j x hj
    exact hkept p x hp (arrived_before config hex hl (by omega) hp hcp) hname
  | fire d => cases hact

end History

/-! ## Of every run -/

variable {env : EnvModel (sig N C)} (henv : (env.link none ()).duplicating = false)
  {evs : List (Lanes.Event (sig N C))} {c : SysState (system N C config)}
  (hrun : (SysState.init (system N C config) env).run env evs = some c)
  (hdistinct : ∀ (p p' : ℕ) (r r' : Request N C), evs[p]? = some (Lanes.Event.input r) →
    evs[p']? = some (Lanes.Event.input r') → r.req = r'.req → p = p')

include henv hrun hdistinct

/-- The board of a read, given the post on its author's account before it: from the act of
the read on, it is a read of a board the spec reaches that holds the post. -/
theorem read_holds {acts : List (Service.Act (Request N C) (Deadline N))} {cut : ℕ → ℕ}
    (hex : System.Implements.Explains (spec N C config) evs acts cut) {k₀ : ℕ} {a : N}
    {q : Post} (hq : q ∈ (boardAt config acts k₀).postsOf a) {p₂ l : ℕ} {r₂ : Request N C}
    {list : List (N × Post)} {json : Bool} (hread : evs[p₂]? = some (.input r₂))
    (hshown : evs[l]? = some (.output ⟨r₂.req, .feed list, json⟩)) (hk₀ : k₀ ≤ cut p₂)
    (hkept : ∀ p r, evs[p]? = some (.input r) → p < l → r.name = a → r.deletes ≠ some q.id) :
    ∃ es, (Board.run config {} es).ReadOf config r₂ list ∧ q ∈ (Board.run config {} es).postsOf a := by
  obtain ⟨k₂, hk₂, hcp₂, ha₂, ho₂⟩ := take_of_output config hex hdistinct hshown hread rfl
  simp only [Response.mk.injEq] at ho₂
  refine ⟨(acts.take k₂).map toEvent, ?_, ?_⟩
  · rw [← play_eq]
    exact Board.handle_feed config (sound_play config (acts.take k₂)).2.2 ho₂.2.1.symm
  · rw [← play_eq]
    exact kept_until config hex (by omega) hq hshown hk₂ hkept

/-- A post the system answered `posted` to a web post is on its author's account in the board
of every read whose request arrives after that answer, until a request made as its author to
delete it arrives: that read is a read of a board the spec reaches that holds the post. -/
theorem posted_kept {p₁ i p₂ l : ℕ} {req : ReqId} {a : N} {s : Sid}
    {body : {s : String // Body.valid s}} {id : PostId} {json json' : Bool} {r₂ : Request N C}
    {list : List (N × Post)}
    (hpost : evs[p₁]? = some (.input (.web req a s (.post body))))
    (hposted : evs[i]? = some (.output ⟨req, .posted id, json⟩))
    (hread : evs[p₂]? = some (.input r₂)) (hafter : i < p₂)
    (hshown : evs[l]? = some (.output ⟨r₂.req, .feed list, json'⟩))
    (hkept : ∀ p r, evs[p]? = some (.input r) → p < l → r.name = a → r.deletes ≠ some id) :
    ∃ es, (Board.run config {} es).ReadOf config r₂ list ∧
      ⟨id, body⟩ ∈ (Board.run config {} es).postsOf a := by
  obtain ⟨acts, cut, hex⟩ := (implements config env henv).history hrun
  obtain ⟨k₁, hk₁, -, ha₁, ho₁⟩ := take_of_output config hex hdistinct hposted hpost rfl
  simp only [Response.mk.injEq] at ho₁
  have hq : ⟨id, body⟩ ∈ (boardAt config acts (k₁ + 1)).postsOf a := by
    rw [boardAt_succ config ha₁]
    exact Board.handle_web_posted config ho₁.2.1.symm
  exact read_holds config henv hrun hdistinct hex hq hread hshown
    (by have := hex.mono (i + 1) p₂ hafter; omega) hkept

/-- A post the system showed in a read is on its author's account in the board of every read
whose request arrives after it was shown, until a request made as its author to delete it
arrives: that read is a read of a board the spec reaches that holds the post. -/
theorem shown_kept {i p₂ l : ℕ} {req : ReqId} {a : N} {q : Post} {json json' : Bool}
    {list₁ list : List (N × Post)} {r₂ : Request N C}
    (hshow : evs[i]? = some (.output ⟨req, .feed list₁, json⟩)) (hx : (a, q) ∈ list₁)
    (hread : evs[p₂]? = some (.input r₂)) (hafter : i < p₂)
    (hshown : evs[l]? = some (.output ⟨r₂.req, .feed list, json'⟩))
    (hkept : ∀ p r, evs[p]? = some (.input r) → p < l → r.name = a → r.deletes ≠ some q.id) :
    ∃ es, (Board.run config {} es).ReadOf config r₂ list ∧
      q ∈ (Board.run config {} es).postsOf a := by
  obtain ⟨acts, cut, hex⟩ := (implements config env henv).history hrun
  obtain ⟨k₁, hk₁, a₁, ha₁, ho₁⟩ := hex.shown i _ hshow
  obtain ⟨r₁, rfl, heq⟩ := act_output config ho₁
  simp only [Response.mk.injEq] at heq
  have hq : q ∈ (boardAt config acts k₁).postsOf a :=
    Board.ReadOf.mem_postsOf config
      (Board.handle_feed config (sound_play config (acts.take k₁)).2.2 heq.2.1.symm) hx
  exact read_holds config henv hrun hdistinct hex hq hread hshown
    (by have := hex.mono (i + 1) p₂ hafter; omega) hkept

/-- The board acts on one API change of an account for each sequence number: every two replies
the system hands over to API changes made as one account with one sequence number are the same,
unless one is `stale` or `badToken`. -/
theorem api_once {i j p₁ p₂ : ℕ} {o₁ o₂ : Response N} {req₁ req₂ token₁ token₂ s : ℕ} {n : N}
    {op₁ op₂ : Op N} (hi : evs[i]? = some (.output o₁)) (hj : evs[j]? = some (.output o₂))
    (hp₁ : evs[p₁]? = some (.input (.api req₁ n token₁ s op₁)))
    (hp₂ : evs[p₂]? = some (.input (.api req₂ n token₂ s op₂)))
    (h₁ : o₁.req = req₁) (h₂ : o₂.req = req₂) (hop₁ : op₁ ≠ .timeline) (hop₂ : op₂ ≠ .timeline)
    (hr₁ : o₁.reply ≠ .stale ∧ o₁.reply ≠ .badToken)
    (hr₂ : o₂.reply ≠ .stale ∧ o₂.reply ≠ .badToken) :
    o₁.reply = o₂.reply := by
  obtain ⟨acts, cut, hex⟩ := (implements config env henv).history hrun
  obtain ⟨k₁, -, -, ha₁, rfl⟩ := take_of_output config hex hdistinct hi hp₁ h₁
  obtain ⟨k₂, -, -, ha₂, rfl⟩ := take_of_output config hex hdistinct hj hp₂ h₂
  have hlt : ∀ {k k' : ℕ} {req req' token token' : ℕ} {op op' : Op N}, k < k' →
      acts[k]? = some (.take (.api req n token s op)) → op ≠ .timeline → op' ≠ .timeline →
      ((boardAt config acts k).handle config (.api req n token s op)).2.1 ≠ .stale →
      ((boardAt config acts k).handle config (.api req n token s op)).2.1 ≠ .badToken →
      ((boardAt config acts k').handle config (.api req' n token' s op')).2.1 ≠ .stale →
      ((boardAt config acts k').handle config (.api req' n token' s op')).2.1 ≠ .badToken →
      ((boardAt config acts k).handle config (.api req n token s op)).2.1 =
        ((boardAt config acts k').handle config (.api req' n token' s op')).2.1 := by
    intro k k' req req' token token' op op' hkk ha hop hop' hs hb hs' hb'
    have hm := Board.handle_api_memoAfter config _ hop hs hb
    rw [← boardAt_succ config ha] at hm
    have hm' := hm.run config (((acts.drop (k + 1)).take (k' - (k + 1))).map toEvent)
    rw [← boardAt_le config (by omega)] at hm'
    rcases hm'.api config (req := req') (token := token') hop' with h | h | h
    · exact h.symm
    · exact absurd h hs'
    · exact absurd h hb'
  rcases Nat.lt_trichotomy k₁ k₂ with hk | rfl | hk
  · exact hlt hk ha₁ hop₁ hop₂ hr₁.1 hr₁.2 hr₂.1 hr₂.2
  · rw [ha₁] at ha₂
    simp only [Option.some.injEq, Service.Act.take.injEq, Request.api.injEq] at ha₂
    obtain ⟨rfl, -, rfl, -, rfl⟩ := ha₂
    rfl
  · exact (hlt hk ha₂ hop₂ hop₁ hr₂.1 hr₂.2 hr₁.1 hr₁.2).symm

end Rookery
