/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Videos.Spec

/-!
# What an output shows

Of every input and every site, no output shows a video (`Site.quiet_handle`): only a read does.
Of every read and every site: each video it shows is a ready video of the site, and a private
one only in an answer to a session of its owner that the site lets in at the read's time
(`Site.shows_read`). Every claim about what is shown rests on this: a private video is its
owner's alone (`Videos.Proofs.Private`), a deleted one is shown no more (`Gone`), a listed one
was confirmed by the store (`Confirmed`).
-/

set_option linter.unusedSectionVars false

namespace Videos

open Lanes

/-- What an output shows of a video: a ready video of the site, and a private one only to a
session of its owner that lets in a request of `at_s` under `life`. -/
def Site.Shows (s : Site) (life : Auth.Lifetime) (at_s : Nat) (o : Out) : Prop :=
  ∀ c ∈ o.cards, ∃ w ∈ s.videos, c = s.card w ∧ w.status.isReady = true ∧
    (w.visibility = .private →
      ∃ req sid r, o = .reply req (some (w.owner, sid)) r ∧ s.accepts life at_s w.owner sid = true)

namespace Site

variable (config : Config)

theorem shows_of_cards {s : Site} {life : Auth.Lifetime} {at_s : Nat} {o : Out}
    (h : o.cards = []) : s.Shows life at_s o := by
  intro c hc
  simp [h] at hc

/-- Every output shows nothing. -/
def Quiet (outs : List Out) : Prop := ∀ o ∈ outs, o.cards = []

theorem quiet_nil : Quiet [] := by simp [Quiet]

theorem quiet_append {a b : List Out} (ha : Quiet a) (hb : Quiet b) : Quiet (a ++ b) := by
  intro o ho
  rcases List.mem_append.mp ho with h | h
  · exact ha o h
  · exact hb o h

theorem quiet_answer {req : ReqId} {viewer : Viewer} {r : Reply} (h : r.cards = []) :
    Quiet (answer req viewer r) := by
  simp [Quiet, answer, Out.cards, h]

theorem quiet_schedule (key : Key) (retry : Schedule.Retry) (at_s at_ms : Nat) :
    Quiet [schedule key retry at_s at_ms] := by
  simp [Quiet, schedule, Out.cards]

theorem quiet_start (round : Round) : Quiet [start config round] := quiet_schedule _ _ _ _

theorem quiet_unstart (video : Video) : Quiet (unstart video) := by
  unfold unstart
  split
  · simp [Quiet, Out.cards]
  · exact quiet_nil

theorem quiet_orphan (l : List Out) (h : ∀ o ∈ l, ∃ v, o = .orphan v) : Quiet l := by
  intro o ho
  obtain ⟨v, rfl⟩ := h o ho
  rfl

theorem quiet_expiry (v : VideoId) (at_s : Nat) : Quiet (expiry config v at_s) := by
  unfold expiry
  split
  · exact quiet_schedule _ _ _ _
  · exact quiet_nil

theorem quiet_unexpire (v : VideoId) : Quiet (unexpire config v) := by
  unfold unexpire
  split
  · simp [Quiet, Out.cards]
  · exact quiet_nil

theorem quiet_waiterOf (video : Video) (viewer : Viewer) (r : Reply) (h : r.cards = []) :
    Quiet (waiterOf video viewer r) := by
  unfold waiterOf
  split
  · exact quiet_answer h
  · exact quiet_nil

theorem viewer_accepts {s : Site} {life : Auth.Lifetime} {at_s : Nat} {x : Viewer} {m : Member}
    {sid : Sid} (h : s.viewer life at_s x = some (m, sid)) : s.accepts life at_s m sid = true := by
  unfold Site.viewer at h
  split at h
  · split at h
    · next hl => cases h; exact hl
    · cases h
  · cases h

theorem quiet_signIn (s : Site) (req : ReqId) (who : Who) (name : String) (at_s : Nat) :
    Quiet (s.signIn config req who name at_s).2 :=
  quiet_answer rfl

theorem quiet_visit (to : Member) (v : Visit) : Quiet [.visit to v] := by
  simp [Quiet, Out.cards]

theorem quiet_withSession {s : Site} {life : Auth.Lifetime} {at_s : Nat} {req : ReqId}
    {m : Member} {session : Sid} {f : Viewer → Site × List Out} (hf : ∀ v, Quiet (f v).2) :
    Quiet (s.withSession life at_s req m session f).2 := by
  unfold withSession
  split
  · exact hf _
  · exact quiet_answer rfl

theorem quiet_owned {s : Site} {req : ReqId} {viewer : Viewer} {m : Member} {v : VideoId}
    {f : Video → Site × List Out} (hf : ∀ w, Quiet (f w).2) :
    Quiet (s.owned req viewer m v f).2 := by
  unfold owned
  split
  · split
    · exact hf _
    · exact quiet_answer rfl
  · exact quiet_answer rfl

theorem quiet_seen {s : Site} {req : ReqId} {viewer : Viewer} {m : Member} {v : VideoId}
    {f : Video → Site × List Out} (hf : ∀ w, Quiet (f w).2) :
    Quiet (s.seen req viewer m v f).2 := by
  unfold seen
  split
  · split
    · exact hf _
    · exact quiet_answer rfl
  · exact quiet_answer rfl

theorem quiet_create (s : Site) (req : ReqId) (viewer : Viewer) (m : Member) (title : Title)
    (about : About) (visibility : Visibility) (media : Media) (at_s : Nat) :
    Quiet (s.create config req viewer m title about visibility media at_s).2 := by
  unfold create
  split
  · exact quiet_answer rfl
  · exact quiet_append (quiet_answer rfl) (quiet_expiry config _ _)

theorem quiet_check (s : Site) (req : ReqId) (viewer : Viewer) (video : Video) (at_s : Nat) :
    Quiet (s.check config req viewer video at_s).2 := by
  unfold check
  dsimp only
  split
  · exact quiet_append (quiet_append (quiet_waiterOf video viewer _ rfl) (quiet_answer rfl))
      (quiet_start config _)
  · exact quiet_append (quiet_waiterOf video viewer _ rfl) (quiet_schedule _ _ _ _)

theorem quiet_uploaded (s : Site) (req : ReqId) (viewer : Viewer) (at_s : Nat) (video : Video) :
    Quiet (s.uploaded config req viewer at_s video).2 := by
  unfold uploaded
  split
  · exact quiet_check config s req viewer video at_s
  · exact quiet_answer rfl

theorem quiet_retry (s : Site) (req : ReqId) (viewer : Viewer) (video : Video) :
    Quiet (s.retry config req viewer video).2 := by
  unfold retry
  split
  · exact quiet_append (quiet_answer rfl) (quiet_start config _)
  · exact quiet_answer rfl

theorem quiet_report (s : Site) (req : ReqId) (r : Report) (signature : String) :
    Quiet (s.report config req r signature).2 := by
  unfold report
  split
  · exact quiet_answer rfl
  · exact quiet_answer rfl

theorem quiet_like (s : Site) (req : ReqId) (viewer : Viewer) (m : Member) (video : Video)
    (on : Bool) : Quiet (s.like req viewer m video on).2 :=
  quiet_answer rfl

theorem quiet_comment (s : Site) (req : ReqId) (viewer : Viewer) (m : Member) (name : String)
    (video : Video) (body : Remark) : Quiet (s.comment config req viewer m name video body).2 := by
  unfold comment
  split
  · exact quiet_answer rfl
  · exact quiet_answer rfl

theorem quiet_uncomment (s : Site) (req : ReqId) (viewer : Viewer) (m : Member) (video : Video)
    (c : CommentId) : Quiet (s.uncomment req viewer m video c).2 := by
  unfold uncomment
  split
  · exact quiet_answer rfl
  · exact quiet_answer rfl

theorem quiet_delete (s : Site) (req : ReqId) (viewer : Viewer) (at_s : Nat) (video : Video) :
    Quiet (s.delete config req viewer at_s video).2 :=
  quiet_append (quiet_append (quiet_append (quiet_append (quiet_waiterOf video viewer _ rfl)
    (quiet_answer rfl)) (quiet_schedule _ _ _ _)) (quiet_unexpire config _)) (quiet_unstart _)

theorem quiet_found (s : Site) (video : Video) (size : Nat) :
    Quiet (s.found config video size).2 :=
  quiet_append (quiet_append (quiet_waiterOf video none _ rfl) (quiet_unexpire config _))
    (quiet_start config _)

theorem quiet_unconfirmed (s : Site) (video : Video) (req : ReqId) (r : Reply) (h : r.cards = []) :
    Quiet (s.unconfirmed video req r).2 := by
  unfold unconfirmed
  split
  · exact quiet_answer h
  · exact quiet_nil

theorem quiet_checked (s : Site) (video : Video) (req : ReqId) (o : Outcome) :
    Quiet (s.checked config video req o).2 := by
  unfold checked
  split
  · exact quiet_found config _ _ _
  · exact quiet_unconfirmed s video req _ rfl
  · split
    · exact quiet_found config _ _ _
    · exact quiet_unconfirmed s video req _ rfl
  all_goals first
    | exact quiet_unconfirmed s video req _ rfl
    | exact quiet_nil

theorem quiet_expired (s : Site) (video : Video) (o : Outcome) :
    Quiet (s.expired config video o).2 := by
  unfold expired
  split
  · exact quiet_found config _ _ _
  · exact quiet_waiterOf video none _ rfl
  · exact quiet_nil

theorem quiet_awaiting {s : Site} {v : VideoId} {f : Video → Site × List Out}
    (hf : ∀ w, Quiet (f w).2) : Quiet (s.awaiting v f).2 := by
  unfold awaiting
  split
  · split
    · exact hf _
    · exact quiet_nil
  · exact quiet_nil

theorem quiet_job (s : Site) (key : Key) (o : Outcome) : Quiet (s.job config key o).2 := by
  cases key with
  | check v req => exact quiet_awaiting fun _ => quiet_checked config _ _ _ _
  | expire v => exact quiet_awaiting fun _ => quiet_expired config _ _ _
  | transcode r => exact quiet_nil
  | delete v =>
    refine quiet_orphan _ fun o' ho => ?_
    simp only [job] at ho
    split at ho
    · exact ⟨v, by simpa using ho⟩
    · cases ho

theorem quiet_recover (s : Site) : Quiet s.recover.2 := by
  unfold Site.recover
  intro o ho
  obtain ⟨v, -, hv⟩ := List.mem_filterMap.mp ho
  split at hv
  · cases hv; rfl
  · cases hv
theorem shows_watch (s : Site) (life : Auth.Lifetime) (req : ReqId) (viewer : Viewer)
    (v : VideoId) (at_s : Nat) (hviewer : ∀ m sid, viewer = some (m, sid) → s.accepts life at_s m sid = true) :
    ∀ o ∈ (s.watch req viewer v at_s).2, s.Shows life at_s o := by
  unfold watch
  dsimp only
  split
  · next video hfind =>
    split
    · next hvis =>
      intro o ho c hc
      simp only [answer, List.mem_singleton] at ho
      subst ho
      simp only [Out.cards, Reply.cards, List.mem_singleton] at hc
      subst hc
      have hmem := List.mem_of_find?_eq_some hfind
      simp only [Video.visibleTo, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq,
        beq_iff_eq] at hvis
      refine ⟨video, hmem, rfl, hvis.1, fun hp => ?_⟩
      rcases hvis.2 with h | h
      · exact absurd hp h
      · cases hv : viewer with
        | none => simp [hv] at h
        | some p =>
          obtain ⟨m, sid⟩ := p
          simp only [hv, Option.map_some, Option.some.injEq] at h
          subst h
          exact ⟨req, sid, _, rfl, hviewer _ _ hv⟩
    · split
      · split <;> exact fun o ho => shows_of_cards (by simp [answer] at ho; subst ho; rfl)
      · exact fun o ho => shows_of_cards (by simp [answer] at ho; subst ho; rfl)
  · exact fun o ho => shows_of_cards (by simp [answer] at ho; subst ho; rfl)

theorem shows_feed (s : Site) (life : Auth.Lifetime) (at_s : Nat) (req : ReqId) (viewer : Viewer)
    (before : Option Cursor) : ∀ o ∈ (s.feed config req viewer before).2, s.Shows life at_s o := by
  unfold feed
  intro o ho c hc
  simp only [answer, List.mem_singleton] at ho
  subst ho
  simp only [Out.cards, Reply.cards, List.mem_map] at hc
  obtain ⟨w, hw, rfl⟩ := hc
  have hw' := List.mem_filter.mp ((List.mem_mergeSort (le := fun a b : Video => !a.cursor.lt b.cursor)).mp
    (List.mem_of_mem_take hw))
  simp only [Video.listed, Bool.and_eq_true, beq_iff_eq] at hw'
  exact ⟨w, hw'.1, rfl, hw'.2.1.1, fun hp => by simp [hp] at hw'⟩

theorem shows_channel (s : Site) (life : Auth.Lifetime) (at_s : Nat) (req : ReqId)
    (viewer : Viewer) (whose : Member)
    (hviewer : ∀ m sid, viewer = some (m, sid) → s.accepts life at_s m sid = true) :
    ∀ o ∈ (s.channel req viewer whose).2, s.Shows life at_s o := by
  unfold channel
  split
  · intro o ho c hc
    simp only [answer, List.mem_singleton] at ho
    subst ho
    simp only [Out.cards, Reply.cards, List.mem_map] at hc
    obtain ⟨w, hw, rfl⟩ := hc
    obtain ⟨hw, hshown⟩ := List.mem_filter.mp hw
    obtain ⟨hw, howner⟩ := List.mem_filter.mp hw
    simp only [beq_iff_eq] at howner
    refine ⟨w, hw, rfl, ?_, fun hp => ?_⟩
    · split at hshown
      · exact hshown
      · simp only [Video.listed, Bool.and_eq_true] at hshown
        exact hshown.1
    · split at hshown
      · next hown =>
        cases hv : viewer with
        | none => simp [hv] at hown
        | some p =>
          obtain ⟨m, sid⟩ := p
          simp only [hv, Option.map_some, beq_iff_eq, Option.some.injEq] at hown
          subst hown
          rw [howner]
          exact ⟨req, sid, _, rfl, hviewer _ _ hv⟩
      · simp [Video.listed, hp] at hshown
  · exact fun o ho => shows_of_cards (by simp [answer] at ho; subst ho; rfl)

theorem quiet_request (s : Site) (c : Command) (at_s : Nat) : Quiet (s.request config c at_s).2 := by
  cases c with
  | signIn req who name => exact quiet_signIn config s req who name at_s
  | signOut req m session => exact quiet_withSession fun _ => quiet_answer rfl
  | create req m session title about visibility media =>
    exact quiet_withSession fun _ => quiet_create config _ _ _ _ _ _ _ _ _
  | uploaded req m session v =>
    exact quiet_withSession fun _ => quiet_owned fun _ => quiet_uploaded config _ _ _ _ _
  | like req m session v on => exact quiet_withSession fun _ => quiet_visit _ _
  | comment req m session v body => exact quiet_withSession fun _ => quiet_visit _ _
  | uncomment req m session v c => exact quiet_withSession fun _ => quiet_visit _ _
  | delete req m session v =>
    exact quiet_withSession fun _ => quiet_owned fun _ => quiet_delete config _ _ _ _ _
  | retry req m session v =>
    exact quiet_withSession fun _ => quiet_owned fun _ => quiet_retry config _ _ _ _
  | report req r signature => exact quiet_report config s req r signature

theorem quiet_visitIn (s : Site) (v : Visit) : Quiet (s.visit config v).2 := by
  cases v with
  | like req viewer m v on => exact quiet_seen fun _ => quiet_like _ _ _ _ _ _
  | comment req viewer m name v body => exact quiet_seen fun _ => quiet_comment config _ _ _ _ _ _ _
  | uncomment req viewer m v c => exact quiet_seen fun _ => quiet_uncomment _ _ _ _ _ _

/-- No output of an input shows a video: only a read does. -/
theorem quiet_handle (s : Site) (i : Input) : Quiet (s.handle config i).2 := by
  cases i with
  | request c at_s => exact quiet_request config s c at_s
  | job key o => exact quiet_job config s key o
  | noticed _ => exact quiet_nil
  | visit v => exact quiet_visitIn config s v

theorem shows_handle (s : Site) (i : Input) :
    ∀ o ∈ (s.handle config i).2, s.Shows config.lifetime i.at_s o :=
  fun o ho => shows_of_cards (quiet_handle config s i o ho)

/-- Every video a read shows is a ready video of the site, and a private one is shown only to a
session of its owner that the site lets in at the read's time. -/
theorem shows_read (s : Site) (r : Read) (at_s : Nat) :
    ∀ o ∈ s.read config r at_s, s.Shows config.lifetime at_s o := by
  cases r with
  | watch viewer v => exact shows_watch s _ 0 _ v at_s fun _ _ h => viewer_accepts h
  | feed viewer before => exact shows_feed config s _ _ 0 _ before
  | channel viewer whose => exact shows_channel s _ _ 0 _ whose fun _ _ h => viewer_accepts h

/-- A read has one output, the reply to it. -/
theorem read_reply (s : Site) (r : Read) (at_s : Nat) :
    ∃ viewer reply, s.read config r at_s = [.reply 0 viewer reply] := by
  cases r with
  | watch viewer v =>
    simp only [read, watch, answer]
    split
    · split
      · exact ⟨_, _, rfl⟩
      · split
        · split <;> exact ⟨_, _, rfl⟩
        · exact ⟨_, _, rfl⟩
    · exact ⟨_, _, rfl⟩
  | feed viewer before => exact ⟨_, _, rfl⟩
  | channel viewer whose =>
    simp only [read, channel, answer]
    split <;> exact ⟨_, _, rfl⟩

theorem shows_recover (s : Site) (at_s : Nat) :
    ∀ o ∈ s.recover.2, s.Shows config.lifetime at_s o :=
  fun o ho => shows_of_cards (quiet_recover s o ho)

end Site

end Videos
