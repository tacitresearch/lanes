/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Videos.Web

/-!
# Reads from the state

The feed, a watch page and a channel page are reads (`Web.read?`): `Web.view` answers them from
the site's state, and they never enter the system. Of every request the view names, every id and
every state of the system (`Web.view_answers`): the bridge decodes the request as the input
`read?` gives, the site takes that input to the state it was in, with one output, and the bridge
encodes that output as the view's response. So a read answered by a peek at a batch boundary
(`Lanes.Batch.run_peeks`) is the answer the request would get if it were the next entry of the
journal there and delivered at once, and leaving it out of the journal changes nothing else
(`Lanes.Batch.run_erase_peeks`).
-/

namespace Videos.Web

open Lanes Lanes.Http

/-- A read's input: the feed, a watch or a channel, under the id it is asked with. -/
private theorem read?_cases {r : Http.Request} {c : ReqId → Command} (h : read? r = some c) :
    (∃ viewer before, c = fun id => .feed id viewer before)
      ∨ (∃ viewer v, c = fun id => .watch id viewer v)
      ∨ (∃ viewer whom, c = fun id => .channel id viewer whom) := by
  simp only [read?, dispatch, List.findSome?_cons, List.findSome?_nil, Route.handle] at h
  cases hh : Routes.home.match? r <;> cases hw : Routes.watch.match? r <;>
    cases hc : Routes.channel.match? r <;>
    simp only [hh, hw, hc, Option.map_none, Option.map_some, reduceCtorEq,
      Option.some.injEq] at h <;> subst h
  all_goals first
    | exact .inl ⟨_, _, rfl⟩
    | exact .inr (.inl ⟨_, _, rfl⟩)
    | exact .inr (.inr ⟨_, _, rfl⟩)

/-- A read leaves the site as it was and answers with one reply, the same under every id. -/
private theorem read_handle (config : Config) (site : Site) (c : ReqId → Command)
    (hc : (∃ viewer before, c = fun id => .feed id viewer before)
      ∨ (∃ viewer v, c = fun id => .watch id viewer v)
      ∨ (∃ viewer whom, c = fun id => .channel id viewer whom)) (at_s : Nat) :
    ∃ viewer reply, ∀ id, site.handle config (.request (c id) at_s) = (site, [.reply id viewer reply]) := by
  rcases hc with ⟨viewer, before, rfl⟩ | ⟨viewer, v, rfl⟩ | ⟨viewer, whom, rfl⟩
  · exact ⟨_, _, fun _ => rfl⟩
  · simp only [Site.handle, Site.request, Site.watch, answer]
    split
    · split
      · exact ⟨_, _, fun _ => rfl⟩
      · split
        · split <;> exact ⟨_, _, fun _ => rfl⟩
        · exact ⟨_, _, fun _ => rfl⟩
    · exact ⟨_, _, fun _ => rfl⟩
  · simp only [Site.handle, Site.request, Site.channel, answer]
    split <;> exact ⟨_, _, fun _ => rfl⟩

/-- What a view answers is what the system answers the same request with: the bridge decodes it
as an input that leaves the site as it was, and encodes the input's one output as the view's
response from that site. -/
theorem view_answers (config : Config) (s : Settings) {r : Http.Request}
    {v : Http.View (system config)} (h : view config s r = some v) (id : ReqId)
    (state : (i : Unit ⊕ Unit) → (system config).State i) :
    ∃ x, (bridge s).decode id r = .ok (.inr x)
      ∧ ((state (.inr ())).handle config x).1 = state (.inr ())
      ∧ (((state (.inr ())).handle config x).2.filterMap fun o => (bridge s).encode (.inr o))
        = [(id, v.answer fun i _ => state i)] := by
  simp only [view] at h
  split at h
  · cases h
  · next hbody =>
    cases hr : read? r with
    | none => simp [hr] at h
    | some c =>
      simp only [hr, Option.map_some, Option.some.injEq] at h
      subst h
      obtain ⟨viewer, reply, hh⟩ := read_handle config (state (.inr ())) c (read?_cases hr) (arrived r)
      refine ⟨.request (c id) (arrived r), ?_, ?_, ?_⟩
      · simp only [bridge, decode, hbody, hr]; rfl
      · rw [hh]
      · simp only [hh, readResponse]
        rfl

end Videos.Web
