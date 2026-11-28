/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Videos.Web
import Videos.Proofs.Shows

/-!
# Reads from the state

The feed, a watch page and a channel page are reads (`Web.read?`): `Web.view` answers them from
the states of the members' actors, and they never enter the system. A watch page reads the
video's owner and the viewer, a channel page the channel's member and the viewer, and the feed
every member's actor started (`Lanes.Batch.Peek.others`). Of every request the view names and
every kernel of the shard (`Web.view_answers`): the response is the spec's read
(`Site.read`) of the sites of those members put together (`Site.union`), each member's site its
actor's state in that kernel, and for the feed every member's actor not among them has the
empty site, as one not started has. With the peek at a batch boundary (`Lanes.Batch.run_peeks`),
the response is what the spec answers from the members' states there, and leaving it out of
the journal changes nothing else (`Lanes.Batch.run_erase_peeks`). The read has one output, its
reply, which the bridge encodes (`Web.readResponse_read`).

A read over several members sees each at the same boundary, and a boundary is not a quiet
point (`docs/decisions/D108-reads-from-state.md`): a like may be let in by the liker's actor and
not yet taken by the owner's. The read then shows the video without it, as if the like came
after the read.
-/

namespace Videos.Web

open Lanes Lanes.Http

/-- A read's one output is its reply, which the bridge encodes. -/
theorem readResponse_read (config : Config) (s : Settings) (site : Site) (rd : Read) (at_s : Nat) :
    ∃ viewer reply, site.read config rd at_s = [.reply 0 viewer reply]
      ∧ readResponse s (site.read config rd at_s) = encodeReply s viewer reply := by
  obtain ⟨viewer, reply, h⟩ := site.read_reply config rd at_s
  exact ⟨viewer, reply, h, by rw [h]; rfl⟩

abbrev Shard (config : Config) (s : Settings) := Http.admittedFronted (system config) (bridge s)

theorem mem_memberSites {config : Config} {s : Settings}
    {others : List ((i : (admittedFrontedSig fullSig).Id) × (Shard config s).State i)}
    {p : Member × Site} (h : p ∈ memberSites config (unfront others)) :
    (⟨.inr (.inr p.1), p.2⟩ : (i : (admittedFrontedSig fullSig).Id) × (Shard config s).State i)
      ∈ others := by
  simp only [memberSites, unfront, List.mem_filterMap] at h
  obtain ⟨⟨i, t⟩, hmem, hx⟩ := h
  cases i with
  | inl e => cases hx
  | inr m =>
    cases hx
    obtain ⟨⟨j, u⟩, hmem', hy⟩ := hmem
    cases j with
    | inl _ => cases hy
    | inr j => cases hy; exact hmem'

theorem mem_memberSites_of {config : Config} {s : Settings}
    {others : List ((i : (admittedFrontedSig fullSig).Id) × (Shard config s).State i)}
    {m : Member} {t : Site}
    (h : (⟨.inr (.inr m), t⟩ : (i : (admittedFrontedSig fullSig).Id) × (Shard config s).State i)
      ∈ others) :
    m ∈ (memberSites config (unfront others)).map (·.1) := by
  simp only [memberSites, unfront, List.mem_map, List.mem_filterMap]
  exact ⟨(m, t), ⟨⟨.inr m, t⟩, ⟨_, h, rfl⟩, rfl⟩, rfl⟩

/-- What a view answers, from any kernel of the shard behind the server: the spec's read of the
sites of the members it reads, each its actor's state in the kernel. For the feed, those are
the members whose actors were started; every other member's actor has the empty site. -/
theorem view_answers (config : Config) (s : Settings) {r : Http.Request}
    {v : Http.View (system config)} (h : view config s r = some v)
    (k : Kernel (Http.admittedFronted (system config) (bridge s))) :
    ∃ rd sites, read? r = some rd ∧
      (v.fronted (bridge := bridge s)).respond
          (Batch.Peek.of k (v.reads.map .inr) (frontEvery v.every))
        = readResponse s (Site.read config (Site.union sites) rd (arrived r)) ∧
      (rd.every = false →
        sites = rd.names.map fun m => (m, ((k.cell (.inr (.inr m))).state : Site))) ∧
      (rd.every = true →
        (∀ p ∈ sites, p.2 = ((k.cell (.inr (.inr p.1))).state : Site)) ∧
          ∀ m, m ∉ sites.map (·.1) → ((k.cell (.inr (.inr m))).state : Site) = {}) := by
  simp only [view] at h
  split at h
  · cases h
  · cases hr : read? r with
    | none => simp [hr] at h
    | some rd =>
      simp only [hr, Option.map_some, Option.some.injEq] at h
      subst h
      refine ⟨rd, _, rfl, View.fronted_respond _ k, fun hev => ?_, fun hev => ⟨?_, ?_⟩⟩
      · simp only [sitesOf, hev, Bool.false_eq_true, ↓reduceIte]
        simp
      · intro p hp
        simp only [sitesOf, hev, ↓reduceIte] at hp
        exact (Batch.Peek.others_of (mem_memberSites hp)).2
      · intro m hm
        simp only [sitesOf, hev, ↓reduceIte] at hm
        refine Batch.Peek.init_of_not_others (ids := (rd.names.map Sum.inr).map Sum.inr)
          (every := frontEvery fun i => true && isMember i)
          (by simp [frontEvery, isMember]) fun hin => hm ?_
        obtain ⟨⟨i, t⟩, hx, hi⟩ := List.mem_map.mp hin
        cases hi
        exact mem_memberSites_of hx

end Videos.Web
