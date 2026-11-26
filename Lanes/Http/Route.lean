/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Http.Basic
public import Std.Data.String.ToNat

/-!
Typed routes. A `Route α` is one description of a URL shape that both prints links and matches
requests, so the two cannot drift apart: `Route.match?_link` proves a link printed by a route is
matched by that route, with the value it was printed from. Views take their links from routes,
so a link to a route that does not exist does not compile.
-/

@[expose] public section

namespace Lanes.Http

/-- A printer and a parser for a run of path segments that carry an `α`. `sound` is what makes
it a route and not two unrelated functions. -/
structure Path (α : Type) where
  print : α → List String
  parse : List String → Option (α × List String)
  sound : ∀ a rest, parse (print a ++ rest) = some (a, rest)

namespace Path

/-- A fixed segment, such as `accounts`. -/
def seg (name : String) : Path Unit where
  print _ := [name]
  parse
    | s :: rest => if s = name then some ((), rest) else none
    | [] => none
  sound _ rest := by simp

def str : Path String where
  print s := [s]
  parse
    | s :: rest => some (s, rest)
    | [] => none
  sound _ _ := rfl

def nat : Path Nat where
  print n := [toString n]
  parse
    | s :: rest => s.toNat?.map (·, rest)
    | [] => none
  sound n rest := by simp

def root : Path Unit where
  print _ := []
  parse rest := some ((), rest)
  sound _ _ := rfl

/-- One path after another. -/
def append {α β : Type} (p : Path α) (q : Path β) : Path (α × β) where
  print x := p.print x.1 ++ q.print x.2
  parse segments := do
    let (a, rest) ← p.parse segments
    let (b, rest) ← q.parse rest
    return ((a, b), rest)
  sound x rest := by simp [List.append_assoc, p.sound, q.sound]

/-- A fixed prefix: `"accounts" /> nat`. -/
def pre {α : Type} (name : String) (p : Path α) : Path α where
  print a := name :: p.print a
  parse
    | s :: rest => if s = name then p.parse rest else none
    | [] => none
  sound a rest := by simp [p.sound]

@[inherit_doc] infixr:60 " /> " => pre

end Path

/-- The methods a route can have. `HEAD` and `OPTIONS` are answered by the server, not routed. -/
inductive Verb where
  | get | post | put | patch | delete
  deriving DecidableEq, Repr, Hashable

def Verb.method : Verb → Method
  | .get => .get
  | .post => .post
  | .put => .put
  | .patch => .patch
  | .delete => .delete

structure Route (α : Type) where
  verb : Verb
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
  if request.method = r.verb.method then
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
    (hmethod : request.method = r.verb.method) (hpath : request.path = r.path.print a) :
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
