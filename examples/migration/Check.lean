import Lanes
import Quota

/-!
Run by `lake test`. First the model checks (Lanes rule 5.1): version 2 keeps every user within
its quota and refuses a use that would pass it; every state version 1 reaches migrates within
the quota; and the migration that gives every user the default quota does not, which the
checker shows with a run.

Then the deploy: version 1 runs on a journal, saves and stops; version 2 starts on the same
files, finds every user as version 1 left it with a quota added, takes requests that version 1
could not, stops, and starts again from its own files, which version 1 then refuses. A
migration cut off after its first write is finished by the next start.
-/

open Lanes Quota Std.Async

instance : V1.sig.Inspect := {}
instance : V1.system.Inspect := {}
instance : V2.sig.Inspect := {}
instance : V2.system.Inspect := {}

def users : List V2.User := [0, 1, 2]

def within (state : V2.User → V2.Usage) : Bool :=
  users.all fun u => decide (V2.WithinQuota (state u))

/-! The model checks. -/

def v2Requests : List V2.Request :=
  [.use 1 0 60, .use 2 0 40, .use 3 0 10, .grant 4 0 10, .use 5 1 10]

def v2Props : List (Check.Property (World V2.system (List V2.Request))) :=
  [ .always "every user is within its quota" fun w => within w.state.state,
    .sometimes "a use is refused" fun w =>
      w.state.outbox.any fun | .refused .. => true | _ => false,
    .sometimes "a user is at its quota" fun w =>
      users.any fun u => (w.state.state u).used == (w.state.state u).quota ]

def v1Requests : List V1.Request :=
  [.use 1 0 90, .use 2 0 60, .use 3 1 10]

/-- What a migration that gives every user the default quota would make of a state. -/
def naive (u : V1.Usage) : V2.Usage :=
  { used := u.used, quota := V2.defaultQuota }

def v1Props : List (Check.Property (World V1.system (List V1.Request))) :=
  [ .always "every state migrates within the quota" fun w =>
      users.all fun u => decide (V2.WithinQuota (V2.Usage.migrate (w.state.state u))),
    .sometimes "a user has used more than the default quota" fun w =>
      users.any fun u => (w.state.state u).used > V2.defaultQuota ]

def naiveProps : List (Check.Property (World V1.system (List V1.Request))) :=
  [ .always "every state migrates within the default quota" fun w =>
      users.all fun u => decide (V2.WithinQuota (naive (w.state.state u))) ]

def checks : List (String × Bool) :=
  let v2 := Check.system V2.system { driver := Driver.anyOrder v2Requests } v2Props
  let v1 := Check.system V1.system { driver := Driver.anyOrder v1Requests } v1Props
  let wrong := Check.system V1.system { driver := Driver.anyOrder v1Requests } naiveProps
  [ ("version 2: every user stays within its quota, and both sometimes properties have a witness",
      v2.ok && v2.complete && v2.witnesses.length == 2),
    ("version 1: every state it reaches migrates within the quota, one past the default among them",
      v1.ok && v1.complete && v1.witnesses.length == 1),
    ("the default quota for everyone: a run of version 1 migrates outside the invariant",
      match wrong.failure with
      | some (.violated "every state migrates within the default quota" _) => true
      | _ => false) ]

/-! The deploy, on files. -/

def scratch (name : String) : IO System.FilePath := do
  let dir := (← IO.getEnv "TMPDIR").getD "/tmp"
  return s!"{dir}/lanes-quota-{name}-{← IO.monoNanosNow}.journal"

def remove (path : System.FilePath) : IO Unit := do
  for file in [path, path.addExtension "lock", path.addExtension "cut",
      path.addExtension "snapshot", path.addExtension "snapshot.tmp", path.addExtension "tmp"] do
    if ← file.pathExists then IO.FS.removeFile file

/-- Version 1 at work: user 0 uses 150 in three requests, user 1 uses 30. It saves after every
turn, then starts again and takes one more request without saving, so its files are a snapshot
and a journal that goes on after the snapshot's mark. -/
def runV1 (path : System.FilePath) : Async Unit := do
  let rt ← Runtime.start V1.system { snapshotEvery := 1 }
    (journal := some (← (V1.store path).open))
  for (req, user, amount) in [(1, 0, 100), (2, 1, 30), (3, 0, 40)] do
    rt.input (.use req user amount)
    rt.idle
  rt.stop
  let rt ← Runtime.start V1.system {} (journal := some (← (V1.store path).open))
  rt.input (.use 4 0 10)
  rt.idle
  rt.stop

def startV2 (path : System.FilePath) (replies : IO.Ref (Array V2.Reply)) :
    Async (Runtime V2.system) := do
  Runtime.start V2.system {} (fun reply => replies.modify (·.push reply))
    (journal := some (← (store path).open))

def states (rt : Runtime V2.system) : Async (List V2.Usage) :=
  users.mapM rt.state

def migrated : List V2.Usage :=
  [{ used := 150, quota := 150 }, { used := 30, quota := 100 }, { used := 0, quota := 100 }]

def header (path : System.FilePath) : IO (Option String) := do
  return Journal.named? (← IO.FS.readBinFile path)

def deploy : Async (List (String × Bool)) := do
  let path ← scratch "deploy"
  runV1 path
  let v1Header ← header path
  let saved ← (path.addExtension "snapshot").pathExists
  let tail := (Frame.decode (← IO.FS.readBinFile path)).length - 2
  let replies ← IO.mkRef #[]
  let rt ← startV2 path replies
  let first ← states rt
  rt.input (.use 5 1 80)
  rt.input (.grant 6 1 50)
  rt.input (.use 7 1 80)
  rt.idle
  let later ← states rt
  rt.stop
  let v2Header ← header path
  let again ← startV2 path (← IO.mkRef #[])
  let restarted ← states again
  again.stop
  let rollback ← (V1.store path).open.toBaseIO
  remove path
  let answered ← replies.get
  return [
    ("deploy: version 1's files carry its name and version, and are a snapshot and a journal "
      ++ "that goes on after its mark",
      v1Header == some (Journal.label "quota" 1) && saved && tail > 2),
    ("deploy: version 2 finds every user as version 1 left it, with a quota added",
      first == migrated),
    ("deploy: every user is within its quota after the migration",
      first.all fun u => decide (V2.WithinQuota u)),
    ("deploy: version 2 refuses a use past the quota and takes it after a grant",
      answered.toList == [.refused 5 100, .granted 6 150, .used 7 110]
        && later[1]? == some { used := 110, quota := 150 }),
    ("deploy: version 2 starts again from its own files, which carry its version",
      restarted == later && v2Header == some (Journal.label "quota" 2)),
    ("deploy: version 1 refuses the files of version 2, saying whose they are",
      match rollback with
      | .error e => (toString e).endsWith
          "it is the journal of \"quota, version 2\", not of \"quota, version 1\""
      | .ok _ => false) ]

/-- The process dies after the migration's first write: the snapshot is version 2's and the
journal still version 1's. The next start finishes the migration. -/
def interrupted : Async (List (String × Bool)) := do
  let path ← scratch "interrupted"
  runV1 path
  let disk : Journal.Disk :=
    { journal := ← IO.FS.readBinFile path
      snapshot := some (← IO.FS.readBinFile (path.addExtension "snapshot")) }
  let begun := disk.begin V2.Request.codec (some V2.actors) (Journal.label "quota" 2) true
    [upgrade]
  let some writes := match begun with | .ok (.upgraded up) => some up.writes | _ => none
    | do remove path; return [("interrupted: version 1's files are migrated", false)]
  let cut := disk.crash writes 1 0
  IO.FS.writeBinFile path cut.journal
  if let some snapshot := cut.snapshot then
    IO.FS.writeBinFile (path.addExtension "snapshot") snapshot
  let rt ← startV2 path (← IO.mkRef #[])
  let found ← states rt
  rt.stop
  let v2Header ← header path
  remove path
  return [("interrupted: a migration cut off after its first write is finished by the next start",
    found == migrated && v2Header == some (Journal.label "quota" 2))]

def main : IO UInt32 := do
  let live ← (do return (← deploy) ++ (← interrupted) : Async _).block
  let tests := checks ++ live
  let failed := tests.filter (!·.2)
  for (name, ok) in tests do
    IO.println s!"{if ok then "ok  " else "FAIL"} {name}"
  return if failed.isEmpty then 0 else 1
