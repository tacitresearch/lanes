/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
The multipart upload's model (`Lanes/Outside/Multipart.lean`) on runs written out, and two
model checks against it (rule 5.1).

- The server's flow (`S3.Multipart.Flow`), the code `S3.upload` runs, as an actor: the store
  answers each call once, late, never, `unknown`, refused for a moment, refused because the
  upload is gone or because a part is wrong, and a late answer may come after the call was made
  again. A part's content is its range of the body and its tag the range, so a part sent twice
  is the same part, as a retry is. Whatever happens, every Complete sent lists exactly the parts
  of the plan, in order, each with the tag its upload was answered; the flow is done only when
  the store may hold that object, and failed only when no Complete was answered `completed`.
- A browser that puts every part at once, so answers come in any order, puts again a part whose
  answer was lost, and completes, again when that answer is lost: what a read sees is the parts in
  order, and no Complete is answered for another listing.
-/

namespace Tests.MultipartModel

open Lanes Lanes.S3.Multipart

/-- A part's content in the model: its range of the body. -/
abbrev Range := Nat × Nat

def tag (r : Range) : String := s!"\"{r.1}-{r.2}\""

abbrev Store := Multipart.State Unit Range String

abbrev Request := Multipart.Request Unit Range String

abbrev Reply := Rpc.Reply (Multipart.Answer Range String)

def runs (port : Rpc.Port σ Request (Multipart.Answer Range String) Empty) (events : List (Event σ)) :
    Bool :=
  (Rpc.outside port (Multipart.server tag)).allows events

/-! ## Runs written out -/

inductive In where
  | reply (call : Nat) (r : Reply)
  deriving DecidableEq, Repr, Hashable

abbrev runSig : Signature where
  Id := Unit
  Msg _ := In
  In := In
  Out := Rpc.Call Request

def runPort : Rpc.Port runSig Request (Multipart.Answer Range String) Empty where
  called c := some c
  replied | .reply call r => some (call, r)

def call (id : Nat) (r : Request) : Event runSig := .output ⟨id, 1000, r⟩

def ans (id : Nat) (a : Multipart.Answer Range String) : Event runSig := .input (.reply id (.answer a))

def lost (id : Nat) : Event runSig := .input (.reply id .unknown)

def begun : List (Event runSig) := [call 0 (.create ()), ans 0 (.created 7)]

def p1 : Range := (0, 5)
def p2 : Range := (5, 8)

def listing : List (Nat × String) := [(1, tag p1), (2, tag p2)]

def modelTests : List (String × Bool) :=
  let run := runs runPort
  let parts := begun ++ [call 1 (.part 7 2 p2), call 2 (.part 7 1 p1), ans 2 (.stored (tag p1)),
    ans 1 (.stored (tag p2))]
  [ ("multipart model: parts out of order, completed in order, read back in order",
      run (parts ++ [call 3 (.complete () 7 listing), ans 3 .completed, call 4 (.get ()),
          ans 4 (.found [p1, p2])])
        && !run (parts ++ [call 3 (.complete () 7 listing), ans 3 .completed, call 4 (.get ()),
          ans 4 (.found [p2, p1])])),
    ("multipart model: a Complete answered for a part never sent, or out of order, is not allowed",
      !run (begun ++ [call 1 (.part 7 1 p1), call 2 (.complete () 7 listing), ans 2 .completed])
        && !run (parts ++ [call 3 (.complete () 7 listing.reverse), ans 3 .completed])
        && !run (parts ++ [call 3 (.complete () 7 [(1, tag p2)]), ans 3 .completed])),
    ("multipart model: a part whose answer was lost may be there, and a Complete lost may have taken effect",
      run (begun ++ [call 1 (.part 7 1 p1), lost 1, call 2 (.part 7 2 p2), lost 2,
          call 3 (.complete () 7 listing), lost 3, call 4 (.get ()), ans 4 (.found [p1, p2])])
        && run (begun ++ [call 1 (.part 7 1 p1), lost 1, call 2 (.part 7 2 p2), lost 2,
          call 3 (.complete () 7 listing), lost 3, call 4 (.get ()), ans 4 .missing])),
    ("multipart model: complete twice with one listing is answered twice, with another refused",
      run (parts ++ [call 3 (.complete () 7 listing), ans 3 .completed,
          call 4 (.complete () 7 listing), ans 4 .completed])
        && !run (parts ++ [call 3 (.complete () 7 listing), ans 3 .completed,
          call 4 (.complete () 7 [(1, tag p1)]), ans 4 .completed])),
    ("multipart model: once completed a read finds the object, and once aborted nothing completes",
      !run (parts ++ [call 3 (.complete () 7 listing), ans 3 .completed, call 4 (.get ()),
          ans 4 .missing])
        && !run (parts ++ [call 3 (.abort 7), ans 3 .aborted, call 4 (.complete () 7 listing),
          ans 4 .completed])
        && !run (parts ++ [call 3 (.abort 7), ans 3 .aborted, call 4 (.complete () 7 listing),
          lost 4, call 5 (.get ()), ans 5 (.found [p1, p2])])),
    ("multipart model: an upload id is issued once",
      !run (begun ++ [call 1 (.create ()), ans 1 (.created 7)])) ]

/-! ## The server's flow against the model -/

inductive FIn where
  /-- The answer to call `call`; `code` is S3's for a refusal, which the model does not tell
  apart. -/
  | reply (call : Nat) (r : Reply) (code : String := "")
  deriving DecidableEq, Repr, Hashable

inductive FOut where
  | call (c : Rpc.Call Step)
  deriving DecidableEq, Repr, Hashable

abbrev flowSig : Signature where
  Id := Unit
  Msg _ := FIn
  In := FIn
  Out := FOut

instance : flowSig.Inspect := {}

/-- A 12 MiB body in parts of 5 MiB: three parts, the last of 2 MiB. -/
def plan : Plan := ⟨12 * 1024 ^ 2, ⟨5 * 1024 ^ 2, by decide⟩, by decide⟩

def key : S3.Key := ⟨"big", by decide⟩

def flow : Flow := Flow.start key plan (maxAttempts := 2)

/-- What S3's client reads for what the model answers. -/
def toS3 (code : String) : Reply → Option S3.Answer
  | .unknown => none
  | .answer (.created u) => some (.started (toString u))
  | .answer (.stored t) => some (.stored (some t))
  | .answer .completed => some (.completed none)
  | .answer .aborted => some .deleted
  | .answer (.found vs) => some (.found { size := vs.foldl (fun n r => n + (r.2 - r.1)) 0 })
  | .answer .missing => some .missing
  | .answer .refused => some (.refused (if code == "NoSuchUpload" then 404
      else if code == "InvalidPart" then 400 else 500) code)

structure FState where
  flow : Flow := flow
  /-- The call the flow waits on. -/
  call : Nat := 0
  deriving DecidableEq, Repr, Hashable

def emit (s : FState) : FState × List (Effect flowSig ()) :=
  match s.flow.next with
  | some step => ({ s with call := s.call + 1 }, [.emit (.call ⟨s.call + 1, 1000, step⟩)])
  | none => (s, [])

def fstep (s : FState) : FIn → FState × List (Effect flowSig ())
  | .reply id r code =>
    if id != s.call then (s, []) else emit { s with flow := s.flow.answer (toS3 code r) }

abbrev flowSystem : System flowSig where
  State _ := FState
  actor _ := { init := {}, step := fstep, recover := fun s => emit s }
  accept x := ⟨(), x⟩
  boot := [()]

instance : flowSystem.Inspect := {}

def uploadId (s : String) : Nat := s.toNat?.getD 0

def request : Step → Request
  | .create => .create ()
  | .part id n first stop => .part (uploadId id) n.val (first, stop)
  | .complete id m => .complete () (uploadId id) (m.val.map fun (n, t) => (n.val, t))
  | .abort id => .abort (uploadId id)
  | .check => .get ()

def flowPort : Rpc.Port flowSig Request (Multipart.Answer Range String) Empty where
  called | .call c => some ⟨c.id, c.deadline_ms, request c.request⟩
  replied | .reply call r _ => some (call, r)

def store := Rpc.outside flowPort (Multipart.server tag)

/-- The parts of the plan, in order, with their tags. -/
def planned : List (Nat × String) :=
  (List.range plan.count).map fun i => (i + 1, tag (plan.range i))

def objects (d : Store) : List (List Range) :=
  d.completions.map fun (_, _, l) =>
    l.filterMap fun (n, t) => (d.sent.find? fun (_, m, r) => m == n && tag r == t).map (·.2.2)

/-- Every answer the model may give to each open call: created, stored, completed, aborted, what
a read may see, nothing, lost, refused for a moment, refused as gone, refused as wrong. -/
def samples (d : Rpc.State Store) : List FIn :=
  d.pending.eraseDups.flatMap fun call =>
    let lost := [FIn.reply call .unknown, .reply call (.answer .refused) "InternalError"]
    match ((d.server.open_.find? (·.1 == call)).map (·.2) : Option Request) with
    | some (.create _) => .reply call (.answer (.created (d.server.uploads.length + 7))) :: lost
    | some (.part _ _ r) => .reply call (.answer (.stored (tag r))) :: lost
    | some (.complete ..) => .reply call (.answer .completed)
        :: .reply call (.answer .refused) "NoSuchUpload" :: .reply call (.answer .refused) "InvalidPart"
        :: lost
    | some (.abort _) => .reply call (.answer .aborted) :: .reply call (.answer .refused) "NoSuchUpload"
        :: lost
    | some (.get _) => .reply call (.answer .missing)
        :: (objects d.server).map (fun o => .reply call (.answer (.found o))) ++ lost
    | none => []

abbrev FW := World flowSystem (Rpc.State Store)

def phase (w : FW) : Phase := (w.state.state ()).flow.phase

@[never_extract] def flowCheck :=
  Check.system flowSystem { driver := store.driver samples }
    [ .always "every Complete sent lists the plan's parts, in order, with the tags answered" fun w =>
        w.driver.server.completions.all fun (_, _, l) => l == planned,
      .always "done only when the store may hold the planned object" fun w =>
        !(phase w matches .done _) ||
          (w.driver.server.completions.any fun (u, _, l) => l == planned
            && (w.driver.server.completed.any (·.1 == u) || w.driver.server.read.length > 0)),
      .always "failed only when no Complete was answered completed" fun w =>
        !(phase w matches .failed _) || w.driver.server.completed.isEmpty,
      .sometimes "done" fun w => phase w matches .done _,
      .sometimes "done after a lost Complete, by its HEAD" fun w =>
        phase w matches .done _ && w.driver.server.completed.isEmpty,
      .sometimes "a part sent twice" fun w =>
        w.driver.server.sent.length > (w.driver.server.sent.eraseDups).length,
      .sometimes "complete sent twice" fun w => w.driver.server.completions.length ≥ 2,
      .sometimes "aborted" fun w => !w.driver.server.aborted.isEmpty ]

/-! ## A browser that puts every part at once -/

inductive BIn where
  | reply (call : Nat) (r : Reply)
  deriving DecidableEq, Repr, Hashable

abbrev bSig : Signature where
  Id := Unit
  Msg _ := BIn
  In := BIn
  Out := Rpc.Call Request

instance : bSig.Inspect := {}

def bParts : List (Nat × Range) := [(1, (0, 5)), (2, (5, 9))]

structure BState where
  upload : Option Nat := none
  /-- Each open call, and what it was. -/
  open_ : List (Nat × Request) := []
  next : Nat := 1
  stored : List Nat := []
  retried : List Nat := []
  completes : Nat := 0
  deriving DecidableEq, Repr, Hashable

def bsend (s : BState) (reqs : List Request) : BState × List (Effect bSig ()) :=
  let calls := reqs.zipIdx.map fun (r, i) => (s.next + i, r)
  ({ s with open_ := s.open_ ++ calls, next := s.next + reqs.length },
    calls.map fun (id, r) => .emit ⟨id, 1000, r⟩)

def complete (s : BState) (u : Nat) : BState × List (Effect bSig ()) :=
  if s.completes < 2 then
    bsend { s with completes := s.completes + 1 } [.complete () u (bParts.map fun (n, r) => (n, tag r))]
  else (s, [])

def bstep (s : BState) : BIn → BState × List (Effect bSig ())
  | .reply id r =>
    match s.open_.lookup id with
    | none => (s, [])
    | some req =>
      let s := { s with open_ := s.open_.filter (·.1 != id) }
      match req, r, s.upload with
      | .create _, .answer (.created u), _ =>
        bsend { s with upload := some u } (bParts.map fun (n, v) => .part u n v)
      | .part u n _, .answer (.stored _), _ =>
        let s := { s with stored := n :: s.stored }
        if bParts.all (fun (m, _) => m ∈ s.stored) && s.completes == 0 then complete s u else (s, [])
      | .part u n v, _, _ =>
        if n ∈ s.retried then (s, []) else bsend { s with retried := n :: s.retried } [.part u n v]
      | .complete .., .unknown, some u => complete s u
      | _, _, _ => (s, [])

abbrev browser : System bSig where
  State _ := BState
  actor _ := { init := {}, step := bstep, recover := fun s => bsend s [.create ()] }
  accept x := ⟨(), x⟩
  boot := [()]

instance : browser.Inspect := {}

def bPort : Rpc.Port bSig Request (Multipart.Answer Range String) Empty where
  called c := some c
  replied | .reply call r => some (call, r)

def bSamples (d : Rpc.State Store) : List BIn :=
  d.pending.eraseDups.flatMap fun call =>
    let lost := [BIn.reply call .unknown]
    match ((d.server.open_.find? (·.1 == call)).map (·.2) : Option Request) with
    | some (.create _) => .reply call (.answer (.created 7)) :: lost
    | some (.part _ _ r) => .reply call (.answer (.stored (tag r))) :: .reply call (.answer .refused) :: lost
    | some (.complete ..) => .reply call (.answer .completed) :: lost
    | _ => []

abbrev BW := World browser (Rpc.State Store)

@[never_extract] def browserCheck :=
  Check.system browser { driver := (Rpc.outside bPort (Multipart.server tag)).driver bSamples }
    [ .always "every listing answered completed is the parts in order" fun w =>
        w.driver.server.completed.all fun (_, l) => l == bParts.map fun (n, r) => (n, tag r),
      .always "every object the store may hold is the parts in order" fun w =>
        (objects w.driver.server).all (· == bParts.map (·.2)),
      .sometimes "parts answered out of order" fun w =>
        (w.state.state ()).stored == [1, 2],
      .sometimes "a part put again after a lost answer, and completed" fun w =>
        !(w.state.state ()).retried.isEmpty && !w.driver.server.completed.isEmpty,
      .sometimes "complete called twice, the first answer lost, and the second answered" fun w =>
        w.driver.server.completions.length == 2 && w.driver.server.completed.length == 1 ]

def checks : IO (List (String × Bool)) := do
  let f := flowCheck
  let b := browserCheck
  return [
    ("multipart flow: against the model, every Complete lists the plan's parts in order, done and failed only when true",
      f.ok && f.witnesses.length == 5),
    ("multipart browser: parts put at once, lost and put again, completed twice: the object is the parts in order",
      b.ok && b.witnesses.length == 3) ]

def tests : List (String × Bool) := modelTests

end Tests.MultipartModel
