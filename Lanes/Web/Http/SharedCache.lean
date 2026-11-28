/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Web.Http.Basic
public import Lanes.Outside.Basic

/-!
# A shared cache in front

A CDN or a proxy keeps responses and answers later requests with them, without asking the
origin, as RFC 9111 allows a shared cache to. It keys a response by its request's target and
the request headers its `Vary` names, so it may give one client a response made for another:
a page that shows a session's records, stored, is everyone's.

`storable` is what RFC 9111 lets a shared cache store and reuse: an answer to a `GET` that is
not `no-store`, `private` or `no-cache`, does not vary on `*`, and is either explicitly fresh
(`max-age`, `s-maxage`, `Expires`, `public`) or of a status a cache may keep without being told
(200, 203, 204, 206, 300, 301, 308, 404, 405, 410, 414, 501); one to a request with
`Authorization` only if it says `public`, `s-maxage` or `must-revalidate`. `outside` is the cache
as a model: it sends no input, and keeps every response the system gives that it may.

Proved: a response is served only if it may be stored, so never one that says `private` or
`no-store` (`SharedCache.serve_storable`), and only to a request whose varying headers are the
stored one's (`SharedCache.serve_reuses`). The check apps use is `leaks`: of exchanges with the
origin, the pairs where the cache may give the second request the first's response and the
origin gave it another. If there are none, whatever the cache keeps of those exchanges, it
gives each of their requests what the origin gave it (`SharedCache.serve_of_leaks`).

Not yet checked against a real service: no run recorded through a CDN or Varnish
(`oracles/README.md`).
-/

@[expose] public section

namespace Lanes.Http.SharedCache

/-- The directives of the response's `Cache-Control` fields, lowercased, without arguments. -/
def directives (r : Response) : List String :=
  (r.headers.filter (·.1.toLower == "cache-control")).flatMap fun (_, value) =>
    (value.splitOn ",").map fun d => ((d.splitOn "=").headD "").trimAscii.toString.toLower

def says (r : Response) (directive : String) : Bool := (directives r).contains directive

/-- The request headers the response varies on, lowercased. -/
def vary (r : Response) : List String :=
  (r.headers.filter (·.1.toLower == "vary")).flatMap fun (_, value) =>
    (value.splitOn ",").map fun h => h.trimAscii.toString.toLower

def explicitlyFresh (r : Response) : Bool :=
  says r "max-age" || says r "s-maxage" || says r "public"
    || r.headers.any (·.1.toLower == "expires")

/-- The statuses RFC 9110 lets a cache keep without being told how long. -/
def heuristic (status : Nat) : Bool :=
  [200, 203, 204, 206, 300, 301, 308, 404, 405, 410, 414, 501].contains status

def storable (request : Request) (r : Response) : Bool :=
  request.method == .get && !says r "no-store" && !says r "private" && !says r "no-cache"
    && !(vary r).contains "*" && (explicitlyFresh r || heuristic r.status)
    && ((request.header? "authorization").isNone || says r "public" || says r "s-maxage"
      || says r "must-revalidate")

/-- Whether the cache may answer `request` with `stored`, kept from its answer to `earlier`. -/
def reuses (earlier : Request) (stored : Response) (request : Request) : Bool :=
  request.method == .get && request.path == earlier.path && request.query == earlier.query
    && (vary stored).all fun h => request.header? h == earlier.header? h

/-- What the cache holds, newest first. -/
abbrev Store := List (Request × Response)

def Store.observe (store : Store) (request : Request) (r : Response) : Store :=
  if storable request r then (request, r) :: store else store

/-- What the cache may answer `request` with: the newest response it holds for it. It may also
not have it, evicted, and ask the origin. -/
def Store.serve? (store : Store) (request : Request) : Option Response :=
  (store.find? fun (earlier, r) => reuses earlier r request).map (·.2)

/-- The cache in front of a system whose responses `port` reads, with the request each
answers. -/
def outside {σ : Signature} (port : σ.Out → Option (Request × Response)) : Outside σ Store where
  init := []
  allow _ _ := none
  observe store out := match port out with
    | some (request, r) => store.observe request r
    | none => store

/-- Every response the cache holds is one it may store. -/
def Store.Sound (store : Store) : Prop := ∀ e ∈ store, storable e.1 e.2 = true

theorem Store.sound_observe {store : Store} (h : store.Sound) (request : Request) (r : Response) :
    (store.observe request r).Sound := by
  intro e he
  simp only [Store.observe] at he
  split at he
  · next hs =>
    rcases List.mem_cons.mp he with rfl | he
    · exact hs
    · exact h e he
  · exact h e he

theorem Store.sound_after {σ : Signature} (port : σ.Out → Option (Request × Response))
    {events : List (Event σ)} {store : Store} (h : (outside port).after events = some store) :
    store.Sound :=
  (outside port).after_invariant (fun _ => True) Store.Sound (by simp [Store.Sound, outside])
    (fun _ _ _ _ h => by simp [outside] at h)
    (fun store out hs _ => by
      simp only [outside]
      split
      · exact Store.sound_observe hs _ _
      · exact hs)
    (fun _ _ => trivial) h

theorem Store.serve_mem {store : Store} {request : Request} {r : Response}
    (h : store.serve? request = some r) :
    ∃ earlier, (earlier, r) ∈ store ∧ reuses earlier r request = true := by
  simp only [Store.serve?, Option.map_eq_some_iff] at h
  obtain ⟨⟨earlier, r'⟩, hfind, rfl⟩ := h
  exact ⟨earlier, List.mem_of_find?_eq_some hfind, by simpa using List.find?_some hfind⟩

/-- In every run, the cache serves only responses it may store: never one that is `private` or
`no-store`. -/
theorem serve_storable {σ : Signature} (port : σ.Out → Option (Request × Response))
    {events : List (Event σ)} {store : Store} (h : (outside port).after events = some store)
    {request : Request} {r : Response} (hserve : store.serve? request = some r) :
    ∃ earlier, storable earlier r = true ∧ says r "private" = false ∧ says r "no-store" = false := by
  obtain ⟨earlier, hmem, -⟩ := Store.serve_mem hserve
  have hs := Store.sound_after port h _ hmem
  refine ⟨earlier, hs, ?_, ?_⟩ <;>
    simp only [storable, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hs <;>
    simp [hs]

/-- And only to a request whose headers it varies on are the stored request's. -/
theorem serve_reuses {store : Store} {request : Request} {r : Response}
    (hserve : store.serve? request = some r) :
    ∃ earlier, (earlier, r) ∈ store ∧ ∀ name ∈ vary r, request.header? name = earlier.header? name := by
  obtain ⟨earlier, hmem, hreuse⟩ := Store.serve_mem hserve
  refine ⟨earlier, hmem, fun name hname => ?_⟩
  simp only [reuses, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hreuse
  exact hreuse.2 name hname

/-- The pairs of exchanges where a shared cache may give the second request the first's
response, and the origin gave it another status or body. -/
def leaks (exchanges : List (Request × Response)) :
    List ((Request × Response) × (Request × Response)) :=
  exchanges.flatMap fun a => (exchanges.filter fun b =>
    storable a.1 a.2 && reuses a.1 a.2 b.1 && (a.2.status, a.2.body) != (b.2.status, b.2.body)).map (a, ·)

/-- With no leaks among some exchanges, a cache that kept any of them gives each of their
requests the status and body the origin gave it, or asks the origin. -/
theorem serve_of_leaks {exchanges : List (Request × Response)} (hleaks : leaks exchanges = [])
    {store : Store} (hstore : ∀ e ∈ store, e ∈ exchanges) (hsound : store.Sound)
    {b : Request × Response} (hb : b ∈ exchanges) {r : Response} (hserve : store.serve? b.1 = some r) :
    (r.status, r.body) = (b.2.status, b.2.body) := by
  obtain ⟨earlier, hmem, hreuse⟩ := Store.serve_mem hserve
  have ha := hstore _ hmem
  have hs := hsound _ hmem
  simp only [leaks, List.flatMap_eq_nil_iff, List.map_eq_nil_iff, List.filter_eq_nil_iff] at hleaks
  have := hleaks _ ha b hb
  simp only [hs, hreuse, Bool.true_and, bne_iff_ne, ne_eq,
    Decidable.not_not] at this
  exact this

end Lanes.Http.SharedCache
