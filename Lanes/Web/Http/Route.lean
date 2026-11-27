/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Web.Http.Basic
public import Std.Data.String.ToNat

/-!
Typed routes. A `Route α` is one description of a URL shape that both prints links and matches
requests, so the two cannot drift apart: `Route.match?_link` proves a link printed by a route is
matched by that route, with the value it was printed from. Views take their links from routes,
so a link to a route that does not exist does not compile.
-/

@[expose] public section

namespace Lanes.Http

/-- What a path segment must be to reach the server as it was written: not empty, and not `.`
or `..`, which browsers remove from a URL however they are escaped. -/
def Segment.Clean (s : String) : Prop :=
  s ≠ "" ∧ s ≠ "." ∧ s ≠ ".."

instance (s : String) : Decidable (Segment.Clean s) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- A printer and a parser for a run of path segments that carry an `α`. `sound` is what makes
it a route and not two unrelated functions. `clean` is what makes its links safe to follow: no
segment is empty, so a link cannot begin with `//` and name another host. -/
structure Path (α : Type) where
  print : α → List String
  parse : List String → Option (α × List String)
  sound : ∀ a rest, parse (print a ++ rest) = some (a, rest)
  clean : ∀ a, ∀ s ∈ print a, Segment.Clean s

/-- A piece of text that can be a path segment. -/
structure Slug where
  text : String
  clean : Segment.Clean text

namespace Slug

def ofString? (s : String) : Option Slug :=
  if h : Segment.Clean s then some ⟨s, h⟩ else none

instance : ToString Slug := ⟨(·.text)⟩

instance : DecidableEq Slug := fun a b =>
  if h : a.text = b.text then isTrue (by cases a; cases b; simp_all)
  else isFalse (fun heq => h (heq ▸ rfl))

end Slug

namespace Path

/-- A fixed segment, such as `accounts`. -/
def seg (name : String) (h : Segment.Clean name := by decide) : Path Unit where
  print _ := [name]
  parse
    | s :: rest => if s = name then some ((), rest) else none
    | [] => none
  sound _ rest := by simp
  clean _ s hs := by simp only [List.mem_singleton] at hs; exact hs ▸ h

def slug : Path Slug where
  print s := [s.text]
  parse
    | s :: rest => (Slug.ofString? s).map (·, rest)
    | [] => none
  sound s rest := by simp [Slug.ofString?, s.clean]
  clean a s hs := by simp only [List.mem_singleton] at hs; exact hs ▸ a.clean

private theorem toString_nat_clean (n : Nat) : Segment.Clean (toString n) := by
  have hdigit : ∀ c ∈ (toString n).toList, c.isDigit = true := fun c hc => by
    rw [show toString n = n.repr from rfl, Nat.toList_repr] at hc
    exact Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
  refine ⟨Nat.repr_ne_empty, ?_, ?_⟩ <;> intro heq <;> rw [heq] at hdigit
  · exact absurd (hdigit '.' (by simp)) (by decide)
  · exact absurd (hdigit '.' (by simp)) (by decide)

/-- Only the canonical spelling is a number: `7`, not `007`, so one resource has one URL. -/
def nat : Path Nat where
  print n := [toString n]
  parse
    | s :: rest => (s.toNat?.filter fun n => toString n = s).map (·, rest)
    | [] => none
  sound n rest := by simp
  clean n s hs := by simp only [List.mem_singleton] at hs; exact hs ▸ toString_nat_clean n

def root : Path Unit where
  print _ := []
  parse rest := some ((), rest)
  sound _ _ := rfl
  clean _ _ hs := nomatch hs

/-- One path after another. -/
def append {α β : Type} (p : Path α) (q : Path β) : Path (α × β) where
  print x := p.print x.1 ++ q.print x.2
  parse segments := do
    let (a, rest) ← p.parse segments
    let (b, rest) ← q.parse rest
    return ((a, b), rest)
  sound x rest := by simp [List.append_assoc, p.sound, q.sound]
  clean x s hs := (List.mem_append.mp hs).elim (p.clean x.1 s) (q.clean x.2 s)

/-- A fixed prefix: `"accounts" /> nat`. -/
def pre {α : Type} (name : String) (p : Path α) (h : Segment.Clean name := by decide) :
    Path α where
  print a := name :: p.print a
  parse
    | s :: rest => if s = name then p.parse rest else none
    | [] => none
  sound a rest := by simp [p.sound]
  clean a s hs := by
    rcases List.mem_cons.mp hs with rfl | hs
    · exact h
    · exact p.clean a s hs

@[inherit_doc] infixr:60 " /> " => pre

end Path

structure Route (α : Type) where
  method : Method
  path : Path α

namespace Route

variable {α : Type}

def get (path : Path α) : Route α := ⟨.get, path⟩
def post (path : Path α) : Route α := ⟨.post, path⟩
def put (path : Path α) : Route α := ⟨.put, path⟩
def patch (path : Path α) : Route α := ⟨.patch, path⟩
def delete (path : Path α) : Route α := ⟨.delete, path⟩

/-- The value a request carries for this route, if the route matches it entirely. -/
def match? (r : Route α) (request : Request) : Option α :=
  if request.method = r.method then
    match r.path.parse request.path with
    | some (a, []) => some a
    | _ => none
  else none

def link (r : Route α) (a : α) : String :=
  "/" ++ "/".intercalate ((r.path.print a).map percentEncode)

/-- What to do with a request this route matches. -/
def handle {β : Type} (r : Route α) (f : α → Request → β) (request : Request) : Option β :=
  (r.match? request).map (f · request)

/-- A request made from a route's link is matched by that route, with the same value. -/
theorem match?_link (r : Route α) (a : α) (request : Request)
    (hmethod : request.method = r.method) (hpath : request.path = r.path.print a) :
    r.match? request = some a := by
  have := r.path.sound a []
  simp only [List.append_nil] at this
  simp [match?, hmethod, hpath, this]

/-- The segments of a link decode to the path the route printed, whatever characters it has. -/
theorem decode_link_segments (r : Route α) (a : α) :
    ((r.path.print a).map percentEncode).mapM (percentDecode ·) = some (r.path.print a) := by
  induction r.path.print a with
  | nil => rfl
  | cons s rest ih => simp [List.mapM_cons, percentDecode_percentEncode, ih]

end Route

/-- The answer of the first handler that matches, as built with `Route.handle`. -/
def dispatch {β : Type} (handlers : List (Request → Option β)) (request : Request) : Option β :=
  handlers.findSome? (· request)

end Lanes.Http
