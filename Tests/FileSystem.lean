/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
The file system model: its answers, what a crash may leave, the two proved patterns checked at
every crash point and after every error, a naive rewrite in place that the same check catches,
the model as an outside, and the binding answering as the model does in a temporary directory.
-/

namespace Tests.FileSystem

open Lanes Lanes.FileSystem

def b (s : String) : Bytes := s.toUTF8.toList

/-- The file system after `ops`, and their answers. -/
def answers (s : Fs) (ops : List Op) : Fs × List Answer :=
  ops.foldl (fun (s, as) op => let (s, a) := s.step op; (s, as ++ [a])) (s, [])

/-- Calls that touch every operation and every error the model names. -/
def script : List Op := [
  .mkdir ["d"], .create ["d", "f"], .write ["d", "f"] 0 (b "hello"),
  .append ["d", "f"] (b " world"), .read ["d", "f"],
  .write ["d", "f"] 13 (b "!"), .read ["d", "f"],
  .write ["d", "f"] 0 (b "J"), .truncate ["d", "f"] 5, .read ["d", "f"],
  .truncate ["d", "f"] 7, .read ["d", "f"], .write ["d", "f"] 20 [],
  .rename ["d", "f"] ["d", "g"], .list ["d"], .read ["d", "f"],
  .mkdir ["e"], .mkdir ["d"], .create ["d", "h"], .list ["d"], .list [],
  .rename ["d", "g"] ["d", "h"], .read ["d", "h"], .list ["d"],
  .read ["d"], .read ["nothing"], .write ["nothing"] 0 (b "x"), .append ["d"] (b "x"),
  .truncate ["nothing"] 0, .create ["d"], .create ["d", "h", "x"], .list ["d", "h"],
  .delete ["d"], .delete ["nothing"], .fsync ["nothing"], .rename ["d"] ["d", "sub"],
  .rename ["d", "h"] ["e"], .rename ["e"] ["d", "h"], .mkdir ["e", "inner"], .delete ["e", "inner"],
  .rename ["e"] ["moved"], .list [], .fsync ["d", "h"], .fsync ["d"], .fsync [],
  .delete ["d", "h"], .delete ["d"], .delete ["moved"], .list []]

/-- What the model answers to the first calls of `script`, written by hand. -/
def expected : List Answer := [
  .done, .done, .done, .done, .bytes (b "hello world"),
  .done, .bytes (b "hello world" ++ [0, 0] ++ b "!"),
  .done, .done, .bytes (b "Jello"),
  .done, .bytes (b "Jello" ++ [0, 0]), .done,
  .done, .names ["g"], .failed .notFound,
  .done, .failed .alreadyExists, .done, .names ["g", "h"], .names ["d", "e"],
  .done, .bytes (b "Jello" ++ [0, 0]), .names ["h"],
  .failed .isDir, .failed .notFound, .failed .notFound, .failed .isDir,
  .failed .notFound, .failed .isDir, .failed .notDir, .failed .notDir,
  .failed .notEmpty, .failed .notFound, .failed .notFound, .failed .invalid,
  .failed .isDir, .failed .notDir, .done, .done]

/-- `d/f` holding `old`, everything synced. -/
def settled (old : Bytes) : Fs :=
  ({} : Fs).run [.mkdir ["d"], .fsync [], .create ["d", "f"], .write ["d", "f"] 0 old,
    .fsync ["d", "f"], .fsync ["d"]]

/-- Whether `ok` holds of what every crash of `s` leaves. -/
def everyCrash (s : Fs) (ok : Fs → Bool) : Bool := s.crashes.all ok

/-- Whether `ok` holds after every crash after every prefix of `ops`, and after every crash
after an `io` error that stops them at any step. -/
def everyPoint (s : Fs) (ops : List Op) (ok : Fs → Bool) : Bool :=
  (List.range (ops.length + 1)).all fun k =>
    let before := s.run (ops.take k)
    everyCrash before ok &&
      match ops[k]? with
      | some op => (before.failures op).all (everyCrash · ok)
      | none => true

/-- How many file systems `everyPoint` looks at. -/
def points (s : Fs) (ops : List Op) : Nat :=
  (List.range (ops.length + 1)).foldl (fun n k =>
    let before := s.run (ops.take k)
    n + before.crashes.length + match ops[k]? with
      | some op => ((before.failures op).map (·.crashes.length)).sum
      | none => 0) 0

def oldOrNew (old new : Bytes) (s : Fs) : Bool :=
  s.read ["d", "f"] == some old || s.read ["d", "f"] == some new

def stale : Fs := (settled (b "old")).run [.create ["d", "f.tmp"], .write ["d", "f.tmp"] 0 (b "junk")]

def replacePlan : List Op := Replace.plan ["d"] "f" "f.tmp" (b "brand new")

/-- Rewriting in place: what `Replace.plan` exists to avoid. -/
def inPlace : List Op := [.create ["d", "f"], .write ["d", "f"] 0 (b "brand new"), .fsync ["d", "f"]]

def logSteps : List Log.Step :=
  [.append (b "a1"), .append (b "bb2"), .sync, .append (b "c3"), .append [], .sync,
    .append (b "ddd4"), .append (b "e5")]

/-- Every prefix of `logSteps`: after any crash, and any error that stops it, the log is a
prefix of what was appended and holds what was synced. -/
def logOk (start : Bytes) : Bool :=
  (List.range (logSteps.length + 1)).all fun k =>
    let steps := logSteps.take k
    let ops := steps.map (·.op ["d", "f"])
    let (all, synced) := Log.written steps
    let ok (s : Fs) := match s.read ["d", "f"] with
      | some r => (start ++ synced).isPrefixOf r && r.isPrefixOf (start ++ all
          ++ (match logSteps[k]? with | some (.append bytes) => bytes | _ => []))
      | none => false
    let before := (settled start).run ops
    everyCrash before ok &&
      match logSteps[k]? with
      | some step => (before.failures (step.op ["d", "f"])).all (everyCrash · ok)
      | none => true

def modelTests : List (String × Bool) :=
  let (_, got) := answers {} script
  let created := ({} : Fs).run [.mkdir ["d"], .fsync [], .create ["d", "f"],
    .write ["d", "f"] 0 (b "x"), .fsync ["d", "f"]]
  [ ("file system model: every call answers as written by hand", got.take expected.length == expected),
    ("file system model: the script leaves the root empty", got.getLast? == some (.names [])),
    ("file system model: a file created and synced, its directory not, may vanish in a crash",
      created.crashes.any (·.read ["d", "f"] == none)
        && everyCrash (created.run [.fsync ["d"]]) (·.read ["d", "f"] == some (b "x"))),
    ("file system model: an append not synced may be lost or torn, and is kept once synced",
      let s := (settled (b "ab")).run [.append ["d", "f"] (b "cd")]
      s.crashes.any (·.read ["d", "f"] == some (b "ab"))
        && s.crashes.any (·.read ["d", "f"] == some (b "abc"))
        && everyCrash (s.run [.fsync ["d", "f"]]) (·.read ["d", "f"] == some (b "abcd"))),
    ("file system model: a rename not synced may be undone by a crash, and is not once synced",
      let s := (settled (b "x")).run [.rename ["d", "f"] ["d", "g"]]
      s.crashes.any (·.read ["d", "f"] == some (b "x"))
        && everyCrash (s.run [.fsync ["d"]]) fun s =>
          s.read ["d", "g"] == some (b "x") && s.read ["d", "f"] == none),
    ("file system model: an fsync that failed may leave the file torn, and so it stays",
      let s := (settled (b "ab")).run [.append ["d", "f"] (b "cd")]
      (s.failures (.fsync ["d", "f"])).any fun s' =>
        s'.read ["d", "f"] == some (b "abc") && everyCrash s' (·.read ["d", "f"] == some (b "abc"))) ]

def patternTests : List (String × Bool) :=
  [ (s!"atomic replace: old or new after every crash and every error \
        ({points (settled (b "old")) replacePlan} file systems)",
      everyPoint (settled (b "old")) replacePlan (oldOrNew (b "old") (b "brand new"))),
    ("atomic replace: also over a temporary file left by an earlier run",
      everyPoint stale replacePlan (oldOrNew (b "old") (b "brand new"))),
    ("atomic replace: and of a file that was not there, which is then absent or new",
      let s := ({} : Fs).run [.mkdir ["d"], .fsync [], .fsync ["d"]]
      everyPoint s replacePlan fun s =>
        s.read ["d", "f"] == none || s.read ["d", "f"] == some (b "brand new")),
    ("atomic replace: once done, the new bytes after any crash, and nothing left beside",
      everyCrash ((settled (b "old")).run replacePlan) fun s =>
        s.read ["d", "f"] == some (b "brand new") && s.read ["d", "f.tmp"] == none),
    ("atomic replace: the same check catches a rewrite in place, which a crash may leave empty",
      !everyPoint (settled (b "old")) inPlace (oldOrNew (b "old") (b "brand new"))
        && ((settled (b "old")).run (inPlace.take 1)).crashes.any (·.read ["d", "f"] == some [])),
    ("append-only log: a prefix of what was appended, holding what was synced, after every crash \
        and every error", logOk [] && logOk (b "head")) ]

/-! The model as an outside. -/

inductive In where
  | reply (call : Nat) (reply : Rpc.Reply Answer)
  | powerLost
  deriving DecidableEq, Repr, Hashable

abbrev sig : Signature where
  Id := Unit
  Msg _ := In
  In := In
  Out := Rpc.Call Op

def port : Rpc.Port sig Op Answer Unit where
  called c := some c
  replied
    | .reply call r => some (call, r)
    | .powerLost => none
  notified
    | .powerLost => some ()
    | .reply .. => none

def call (id : Nat) (op : Op) : Event sig := .output ⟨id, 1000, op⟩
def reply (id : Nat) (a : Answer) : Event sig := .input (.reply id (.answer a))

def outsideTests : List (String × Bool) :=
  let calm := Rpc.outside port (server { io := false, power := false })
  let real := Rpc.outside port (server {})
  let run := [call 0 (.create ["f"]), reply 0 .done, call 1 (.append ["f"] (b "ab")), reply 1 .done]
  [ ("file system outside: answers as the model, and no other",
      calm.allows (run ++ [call 2 (.read ["f"]), reply 2 (.bytes (b "ab"))])
        && !calm.allows (run ++ [call 2 (.read ["f"]), reply 2 (.bytes (b "a"))])),
    ("file system outside: an io error hides whether an append took effect",
      let failed := [call 0 (.create ["f"]), reply 0 .done, call 1 (.append ["f"] (b "ab")),
        reply 1 (.failed .io), call 2 (.read ["f"])]
      real.allows (failed ++ [reply 2 (.bytes (b "ab"))])
        && real.allows (failed ++ [reply 2 (.bytes (b "a"))])
        && real.allows (failed ++ [reply 2 (.bytes [])])
        && !calm.allows failed),
    ("file system outside: after a power loss, what was not synced may be gone",
      let lost := run ++ [.input .powerLost, call 2 (.read ["f"])]
      real.allows (lost ++ [reply 2 (.failed .notFound)])
        && real.allows (lost ++ [reply 2 (.bytes (b "ab"))])
        && !calm.allows lost
        && !real.allows (run ++ [call 2 (.fsync ["f"]), reply 2 .done, call 3 (.fsync []),
          reply 3 .done, .input .powerLost, call 4 (.read ["f"]), reply 4 (.failed .notFound)])) ]

def tests : List (String × Bool) := modelTests ++ patternTests ++ outsideTests

/-! The binding, in a temporary directory. -/

def toArray (bytes : Bytes) : ByteArray := ⟨bytes.toArray⟩

def live : IO (List (String × Bool)) := do
  let (_, want) := answers {} script
  let got ← IO.FS.withTempDir fun root =>
    script.mapM fun op => return (← IO.perform root (op.map toArray)).map ByteArray.toList
  let replaced ← IO.FS.withTempDir fun root => do
    let path := root / "state.json"
    File.replace path "first"
    File.replace path "second"
    IO.FS.writeFile (root / "state.json.tmp") "left by a crash"
    File.replace path "third"
    let text ← IO.FS.readFile path
    let left ← (root / "state.json.tmp").pathExists
    IO.FS.createDir (root / "state.json.tmp")
    IO.FS.writeFile (root / "state.json.tmp" / "inside") "x"
    let refused ← (File.replace path "fourth").toBaseIO
    return text == "third" && !left && refused matches .error _
      && (← IO.FS.readFile path) == "third"
  let synced ← IO.FS.withTempDir fun root => do
    IO.FS.writeFile (root / "f") "x"
    File.fsync (root / "f").toString
    File.fsync root.toString
    return (← (File.fsync (root / "missing").toString).toBaseIO) matches .error _
  let mismatches := (script.zip (got.zip want)).filter fun (_, g, w) => g != w
  return [
    (s!"file system binding: answers as the model, call for call{
        if mismatches.isEmpty then "" else s!" (differs: {repr (mismatches.take 3)})"}",
      mismatches.isEmpty && got.length == want.length),
    ("File.replace: over nothing, over a file and over a temporary file left behind; refused, \
        and the file kept, when a directory is in the way", replaced),
    ("File.fsync: a file and its directory are synced, and a path that is not there is an error",
      synced) ]

end Tests.FileSystem
