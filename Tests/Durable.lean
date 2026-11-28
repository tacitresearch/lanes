/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Tests.Fixtures.Bank

/-!
A durable shard: the bank with a journal. It is stopped and started, its journal is cut short,
and a child process running it is killed with SIGKILL in the middle of its work. Each time the
shard comes back in the state its journal describes, with nothing it had acknowledged missing.
-/

namespace Tests.Durable

open Lanes Std Std.Async Tests.Fixtures.Bank

abbrev Bank3 := bank (Fin 3) 100

def store (path : System.FilePath) : Journal.Store Bank3 :=
  { path, input := Request.codec Codec.fin }

def scratch (name : String) : IO System.FilePath := do
  let dir := (← IO.getEnv "TMPDIR").getD "/tmp"
  return s!"{dir}/lanes-{name}-{← IO.monoNanosNow}.journal"

def remove (path : System.FilePath) : IO Unit := do
  for file in [path, path.addExtension "lock", path.addExtension "cut",
      path.addExtension "snapshot", path.addExtension "id"] do
    if ← file.pathExists then IO.FS.removeFile file

/-! `Journal.open?` on the compiled code: every cut, and every flipped bit, of a small journal. -/

def entries : List (Journal.Entry (sig (Fin 3))) :=
  [.advance 5, .input (.transfer ⟨1, 0, 1, 3⟩), .batch 64, .handed, .advance 9,
    .input (.transfer ⟨2, 1, 2, 300⟩), .batch 64]

def written (entries : List (Journal.Entry (sig (Fin 3)))) : List ByteArray :=
  Journal.write (Request.codec Codec.fin) entries

def opened (system : String) (bytes : ByteArray) :=
  Journal.open? (σ := sig (Fin 3)) (Request.codec Codec.fin) system bytes

def flip (bytes : ByteArray) (bit : Nat) : ByteArray :=
  bytes.set! (bit / 8) (bytes[bit / 8]! ^^^ (1 <<< (bit % 8)).toUInt8)

/-! The model of the two files, `Journal.Disk`, on the compiled code: the files are left in
every state the death of the process can leave them in, and loaded. -/

open Journal (Disk Write) in
/-- Whether `disk` loads as the kernel and the outputs that replaying `history` gives. -/
def loads (disk : Disk) (history : List (Journal.Entry (sig (Fin 3)))) : Bool :=
  let codecs := actors Codec.fin 100
  let expected := Journal.recover Bank3 history
  match disk.load Bank3 (Request.codec Codec.fin) (some codecs) "bank" with
  | .ok (kernel, outputs) =>
    Journal.saved codecs "" 0 kernel.image == Journal.saved codecs "" 0 expected.1.image
      && outputs == expected.2
  | .error _ => false

open Journal (Disk Write) in
def finish (disk : Disk) (writes : List Write) : Disk :=
  disk.crash writes writes.length 0

open Journal (Disk Write) in
/-- Dying anywhere in `writes`, with an append cut at any of its first `bytes` bytes, leaves a
disk that loads as `history done part`, and still does once it is mended. -/
def survives (disk : Disk) (writes : List Write) (bytes : Nat)
    (history : Nat → Nat → List (Journal.Entry (sig (Fin 3)))) : Bool :=
  (List.range (writes.length + 2)).all fun done => (List.range (bytes + 2)).all fun part =>
    let left := disk.crash writes done part
    loads left (history done part)
      && match left.read (sys := Bank3) (Request.codec Codec.fin) none "bank" with
        | .ok found =>
          loads (finish left (left.mend "bank" found.size)) (history done part)
        | .error _ => false

open Journal (Disk Write) in
/-- A save of the kernel that `history` gives, on a disk that holds it: `read` finds the index
of the mark and nothing to cut, and dying anywhere in the save loses nothing. -/
def saveSurvives (disk : Disk) (history : List (Journal.Entry (sig (Fin 3)))) : Bool :=
  let input := Request.codec Codec.fin
  let codecs := actors Codec.fin 100
  let index := history.length
  let mark := Journal.encode input ([.snapshot index] : List (Journal.Entry (sig (Fin 3))))
  (match disk.read (sys := Bank3) input (some codecs) "bank" with
    | .ok found => found.index == index && found.size == disk.journal.size
    | .error _ => false)
  && survives disk (Journal.saveWrites input codecs "bank" index
      (Journal.recover Bank3 history).1.image) mark.size fun done part =>
    if done == 0 && part < mark.size then history else history ++ [.snapshot index]

open Journal (Disk Reading) in
/-- What a start makes of readings that may fail, of every state dying in a save can leave. -/
def readingTests (disk : Disk) (save : List Journal.Write) : List (String × Bool) :=
  let input := Request.codec Codec.fin
  let failed : Reading := .failed "EIO"
  let truthful (d : Disk) : List (Reading × Reading) :=
    [(.bytes d.journal, d.snapshot.elim .absent .bytes)]
  let faulty (d : Disk) : List (Reading × Reading) :=
    [(failed, d.snapshot.elim .absent .bytes), (.bytes d.journal, failed), (failed, failed)]
  /- A start that took a failed read for a file that is not there, as `pathExists` made the
  start before this one do. -/
  let lenient : Reading → Reading
    | .failed _ => .absent
    | r => r
  let begun (d : Disk) : Disk :=
    match d.start (sys := Bank3) input none "bank" true with
    | .ok found => finish d (d.mend "bank" found.size)
    | .error _ => d
  [ ("disk: a start whose read of either file fails refuses, and one whose reads do not loads "
      ++ "what dying anywhere in a save left",
      let mark := Journal.encode input ([.snapshot entries.length] : List (Journal.Entry (sig (Fin 3))))
      (List.range (save.length + 1)).all fun done => (List.range (mark.size + 2)).all fun part =>
        let left := disk.crash save done part
        let history := if done == 0 && part < mark.size then entries
          else entries ++ [.snapshot entries.length]
        (truthful left).all (fun (j, s) => match Disk.ofReadings j s with
            | .ok d => loads d history
            | .error _ => false)
          && (faulty left).all fun (j, s) => (Disk.ofReadings j s).toOption.isNone),
    ("disk: a start that took a failed read for no file would begin a journal over every entry",
      match Disk.ofReadings (lenient failed) (lenient failed) with
      | .ok d => loads disk entries && loads (begun d) [] && (begun d).journal.size < disk.journal.size
      | .error _ => false) ]

def diskTests : List (String × Bool) :=
  let input := Request.codec Codec.fin
  let fresh := finish {} (Journal.Disk.mend "bank" {} 0)
  let turn := Journal.appendWrites input entries
  let disk := finish fresh turn
  let save := Journal.saveWrites input (actors Codec.fin 100) "bank" entries.length
    (Journal.recover Bank3 entries).1.image
  let later : List (Journal.Entry (sig (Fin 3))) :=
    [.advance 12, .input (.transfer ⟨3, 2, 0, 4⟩), .batch 64, .handed]
  [ ("disk: no journal, and a new one, are the journal of nothing",
      survives {} (Journal.Disk.mend "bank" {} 0) 0 fun _ _ => []),
    ("disk: a store that may not begin a journal is refused one that is not there, or has not "
      ++ "its header, and no other",
      let start := fun (create : Bool) (disk : Journal.Disk) =>
        match disk.start (sys := Bank3) input none "bank" create with
        | .ok found => some found.past.length
        | .error .missing => none
        | .error _ => some 0
      let header := (Journal.header "bank").size
      start false {} == none && start true {} == some 0
        && start false { journal := fresh.journal.extract 0 header } == none
        && start false fresh == some 0 && start false disk == some entries.length),
    ("disk: dying at any byte of a turn's append leaves the entries wholly written",
      survives fresh turn (Journal.encode input entries).size fun done part =>
        if done == 0 then entries.take (Frame.whole (written entries) part) else entries),
    ("disk: dying at any byte of the mark or between the steps of a save loses nothing",
      saveSurvives disk entries),
    ("disk: nor does dying in the next save, from each state the first can leave",
      [0, 1, 2, 3].all fun done =>
        saveSurvives (finish (disk.crash save done 1000) (Journal.appendWrites input later))
          (entries ++ [.snapshot entries.length] ++ later)) ] ++ readingTests disk save

def fileTests : List (String × Bool) :=
  let file := Journal.file (Request.codec Codec.fin) "bank" entries
  diskTests ++
  [ ("journal: a file cut at any byte opens and gives a prefix of what was written, and all of "
      ++ "it when nothing is cut",
      (List.range (file.size + 1)).all fun n =>
        match opened "bank" (file.extract 0 n) with
        | .ok (found, size) =>
          size ≤ n && written found == (written entries).take found.length
            && (n < file.size || found.length == entries.length)
        | .error _ => false),
    ("journal: no flipped bit gives an entry that was not written",
      (List.range (file.size * 8)).all fun bit =>
        match opened "bank" (flip file bit) with
        | .ok (found, _) => written found == (written entries).take found.length
        | .error _ => true),
    ("journal: a flipped bit inside an entry is damage, and is refused",
      (opened "bank" (flip file (8 * (file.size - 3)))).toOption.isNone),
    ("journal: another system's journal is refused",
      (match opened "ledger" file with | .error (.foreign (some "bank")) => true | _ => false)),
    ("journal: a journal written with another codec is refused, not cut",
      (match Journal.open? (σ := sig Bool) (Request.codec Codec.bool) "bank" file with
        | .error (.unreadable 5) => true
        | _ => false)) ]

def balances (rt : Runtime Bank3) : Async (List Int) :=
  (List.finRange 3).mapM fun a => return (← rt.state a).balance

def start (path : System.FilePath) (seen : IO.Ref (Array Nat)) : Async (Runtime Bank3) := do
  Runtime.start Bank3 {} (fun out => seen.modify (·.push out.req)) (some (← (store path).open))

def restartTest : Async (List (String × Bool)) := do
  let path ← scratch "restart"
  let first ← IO.mkRef #[]
  let rt ← start path first
  for n in [0:20] do rt.input (.transfer ⟨n, 0, 1, 3⟩)
  rt.idle
  let before ← balances rt
  rt.stop
  let second ← IO.mkRef #[]
  let rt ← start path second
  rt.idle
  let after ← balances rt
  rt.input (.transfer ⟨100, 1, 2, 5⟩)
  rt.idle
  let later ← balances rt
  rt.stop
  remove path
  return [
    ("durable: a shard started again from its journal is in the state it was in",
      before == [40, 160, 100] && after == before),
    ("durable: outputs already handed over are not handed over again",
      (← first.get).size == 20 && (← second.get) == #[100]),
    ("durable: it goes on from there", later == [40, 155, 105]) ]

/-- Cut the journal at `keep` bytes, as a write torn by a crash would, start on it, do one more
transfer, and start once more. -/
def torn (file : ByteArray) (keep : Nat) : Async Bool := do
  let path ← scratch s!"torn{keep}"
  IO.FS.writeBinFile path (file.extract 0 keep)
  let seen ← IO.mkRef #[]
  let rt ← start path seen
  rt.idle
  let recovered ← balances rt
  rt.input (.transfer ⟨500, 2, 0, 7⟩)
  rt.idle
  rt.stop
  let rt ← start path seen
  rt.idle
  let again ← balances rt
  rt.stop
  remove path
  let moved := 100 - recovered[0]!
  return recovered.sum == 300 && moved % 3 == 0 && moved ≤ 60 && recovered[1]! == 100 + moved
    && again == [recovered[0]! + 7, recovered[1]!, recovered[2]! - 7]

def tornTest : Async (List (String × Bool)) := do
  let path ← scratch "whole"
  let seen ← IO.mkRef #[]
  let rt ← start path seen
  for n in [0:20] do rt.input (.transfer ⟨n, 0, 1, 3⟩)
  rt.idle
  rt.stop
  let file ← IO.FS.readBinFile path
  remove path
  let cuts := [0, 1, 9, file.size / 3, file.size / 2, file.size - 9, file.size - 1, file.size]
  let results ← cuts.mapM (torn file)
  return [("durable: a journal cut anywhere recovers a state it passed through, and what is "
    ++ "written after the cut is kept", results.all (·))]

/-- Run by `lanesTest journal-child path`: a bank that works until it is killed, and says on
standard output which requests it has answered. -/
def child (path : System.FilePath) : IO Unit := do
  let out ← IO.getStdout
  let work : Async Unit := do
    let rt ← Runtime.start Bank3 {} (fun response => do
      out.putStrLn (toString response.req)
      out.flush) (some (← (store path).open))
    for n in [0:1000000] do
      rt.input (.transfer ⟨n, Fin.ofNat 3 n, Fin.ofNat 3 (n + 1), 1⟩)
  work.block

def killTest : Async (List (String × Bool)) := do
  let path ← scratch "kill"
  let process ← IO.Process.spawn {
    cmd := (← IO.appPath).toString, args := #["journal-child", path.toString], stdout := .piped }
  let mut acknowledged : Array Nat := #[]
  for _ in [0:300] do
    if let some req := (← process.stdout.getLine).trimAscii.toString.toNat? then
      acknowledged := acknowledged.push req
  process.kill
  discard process.wait
  let log ← (store path).open
  let replayed := (Kernel.boot Bank3).1.exec (Journal.ops log.past)
  let answered := replayed.outputs.map (·.req)
  log.close
  let seen ← IO.mkRef #[]
  let rt ← start path seen
  rt.idle
  let recovered ← balances rt
  rt.stop
  remove path
  return [
    ("durable: after SIGKILL, every request the bank had answered is in its journal",
      acknowledged.size == 300 && acknowledged.all (answered.contains ·)),
    ("durable: after SIGKILL, the bank comes back in the state the journal describes",
      recovered.sum == 300
        && recovered == (List.finRange 3).map fun a => (replayed.kernel.cell a).state.balance) ]

/-- A journal is one process's: the second to open it is refused, whatever it would have read.
And a journal that is refused is left exactly as it was. -/
def refusalTest : Async (List (String × Bool)) := do
  let path ← scratch "refusal"
  let seen ← IO.mkRef #[]
  let rt ← start path seen
  for n in [0:5] do rt.input (.transfer ⟨n, 0, 2, 3⟩)
  rt.idle
  let second ← ((store path).open).toBaseIO
  rt.stop
  let before ← IO.FS.readBinFile path
  let foreign ← ({ store path with system := "another" } : Journal.Store Bank3).open.toBaseIO
  let other : Journal.Store (bank Bool 100) := { path, input := Request.codec Codec.bool }
  let codec ← other.open.toBaseIO
  IO.FS.writeBinFile path (flip before (8 * (before.size / 2)))
  let damaged ← ((store path).open).toBaseIO
  IO.FS.writeBinFile path before
  let again ← ((store path).open).toBaseIO
  let reopened ← match again with
    | .ok log => do log.close; pure (decide (log.past.length > 5))
    | .error _ => pure false
  let after ← IO.FS.readBinFile path
  remove path
  let refused := fun (r : Except IO.Error (Journal.Log _)) => r.toOption.isNone
  return [
    ("durable: a journal in use is refused to a second opener", refused second),
    ("durable: another system's journal, one written with another codec, and a damaged one "
      ++ "are each refused", refused foreign && codec.toOption.isNone && refused damaged),
    ("durable: a refused journal is left as it was, and opens again", reopened && after == before) ]

/-- A shard that has made promises does not come back without its journal. -/
def missingTest : Async (List (String × Bool)) := do
  let path ← scratch "missing"
  let existing : Journal.Store Bank3 := { store path with create := false }
  let refused := fun (r : Except IO.Error (Journal.Log Bank3)) =>
    match r with
    | .ok _ => false
    | .error e => (toString e).endsWith "it is not there, and this store may not begin one"
  let absent ← existing.open.toBaseIO
  let made ← path.pathExists
  IO.FS.writeBinFile path .empty
  let empty ← existing.open.toBaseIO
  let left ← IO.FS.readBinFile path
  let seen ← IO.mkRef #[]
  let rt ← start path seen
  rt.input (.transfer ⟨1, 0, 2, 3⟩)
  rt.idle
  rt.stop
  let back ← existing.open.toBaseIO
  let kept ← match back with
    | .ok log => do log.close; pure (decide (log.past.length > 1))
    | .error _ => pure false
  remove path
  return [
    ("durable: a store that may not begin a journal is refused a path with none, and makes none",
      refused absent && !made),
    ("durable: and an empty file, which it leaves empty", refused empty && left.size == 0),
    ("durable: and opens the journal another start began", kept) ]

/-- A journal whose read fails, here because it is a link to itself, is refused and left as it
was: it is not taken for a journal that is not there, which a start would begin anew. -/
def unreadableTest : Async (List (String × Bool)) := do
  let path ← scratch "unreadable"
  discard <| IO.Process.output { cmd := "ln", args := #["-s", path.toString, path.toString] }
  let opened ← (store path).open.toBaseIO
  let refused := match opened with
    | .ok _ => false
    | .error e => ((toString e).splitOn "cannot be read").length > 1
  let left ← path.symlinkMetadata.toBaseIO
  let still := match left with
    | .ok m => m.type == .symlink
    | .error _ => false
  remove path
  if (← path.symlinkMetadata.toBaseIO) matches .ok _ then IO.FS.removeFile path
  return [("durable: a journal that cannot be read is refused, not begun again over", refused && still)]

/-! What the shard does with its journal, on a journal held in memory. -/

def throws {α : Type} (action : Async α) : Async Bool := do
  try discard action; return false
  catch _ => return true

def within {α : Type} (ms : Nat) (action : Async α) : Async (Option α) :=
  Async.race (some <$> action) (do Async.sleep (.ofNat ms); return none)

/-- A journal in memory. Its `append` fails from call number `failAt` on. -/
def memory (past : List (Journal.Entry (sig (Fin 3)))) (failAt : Option Nat := none) :
    IO (Journal.Log Bank3 × IO.Ref (Array Nat)) := do
  let durable ← IO.mkRef #[]
  let calls ← IO.mkRef 0
  let log : Journal.Log Bank3 := {
    past
    append := fun entries => do
      let call ← calls.modifyGet fun n => (n, n + 1)
      if failAt.any (· ≤ call) then throw (IO.userError "no room on the device")
      for entry in entries do
        if let .input (.transfer t) := entry then durable.modify (·.push t.req)
    note := fun _ => pure ()
    close := pure () }
  return (log, durable)

def orderTest : Async (List (String × Bool)) := do
  let (log, durable) ← memory []
  let checked ← IO.mkRef #[]
  let rt ← Runtime.start Bank3 {} (journal := some log) fun response => do
    checked.modify (·.push ((← durable.get).contains response.req))
  for n in [0:20] do rt.input (.transfer ⟨n, 0, 1, 3⟩)
  rt.idle
  rt.stop
  let checked ← checked.get
  return [("durable: an input is in the journal before any output it caused is handed over",
    checked.size == 20 && checked.all (·))]

def rehandTest : Async (List (String × Bool)) := do
  let past : List (Journal.Entry (sig (Fin 3))) :=
    [.advance 0, .input (.transfer ⟨7, 0, 1, 3⟩), .batch 64, .handed,
      .advance 1, .input (.transfer ⟨8, 0, 1, 3⟩), .batch 64]
  let run := fun (past : List (Journal.Entry (sig (Fin 3)))) => do
    let (log, _) ← memory past
    let seen ← IO.mkRef #[]
    let rt ← Runtime.start Bank3 {} (journal := some log) fun response =>
      seen.modify (·.push response.req)
    rt.idle
    rt.stop
    seen.get
  return [
    ("durable: outputs produced and not marked as handed over are handed over after a restart",
      (← run past) == #[8]),
    ("durable: and those that were marked are not", (← run (past ++ [.handed])) == #[]) ]

/-- A log in memory that keeps every entry written to it. -/
def keeping (past : List (Journal.Entry (sig (Fin 3)))) (written : IO.Ref (Array (Journal.Entry (sig (Fin 3)))))
    (restored : Bool := false) : Journal.Log Bank3 :=
  { past, id := "j", restored
    append := fun entries => written.modify (· ++ entries.toArray)
    note := fun entries => written.modify (· ++ entries.toArray)
    close := pure () }

/-- Each output handed over, with its id, on `log`, given `inputs` one at a time. -/
def handedWith (log : Journal.Log Bank3) (inputs : List Nat) :
    Async (List (Journal.OutputId × Nat)) := do
  let seen ← IO.mkRef #[]
  let rt ← Runtime.startWith Bank3 {} (journal := some log) fun _ id out =>
    seen.modify (·.push (id, out.req))
  rt.idle
  for n in inputs do
    rt.input (.transfer ⟨n, 0, 1, 3⟩)
    rt.idle
  rt.stop
  return (← seen.get).toList

def idsTest : Async (List (String × Bool)) := do
  let written ← IO.mkRef #[]
  let live ← handedWith (keeping [] written) [7, 8]
  let history := (← written.get).toList
  let unmarked := history.dropLast
  let again ← handedWith (keeping unmarked (← IO.mkRef #[])) []
  let restoredWritten ← IO.mkRef #[]
  let restored ← handedWith (keeping unmarked restoredWritten (restored := true)) []
  let path ← scratch "ids"
  let idOf : Journal.Store Bank3 → IO String := fun s => do
    let log ← s.open
    log.close
    return log.id
  let first ← idOf (store path)
  let same ← idOf (store path)
  let copy ← idOf { store path with restored := true }
  let afterCopy ← idOf (store path)
  IO.FS.removeFile path
  let afresh ← idOf (store path)
  remove path
  return [
    ("output ids: each output handed over has an id of its own, its journal's and its place",
      live.map (·.1.origin) == [⟨3, 0⟩, ⟨7, 0⟩] && live.all (·.1.journal == "j")
        && history.getLast? matches some .handed),
    ("output ids: an output handed over again after a restart has the id it had",
      again == live.filter (·.2 == 8)),
    ("output ids: a restored start hands over nothing it owes, and marks it handed",
      restored == [] && (← restoredWritten.get).toList matches [.handed]),
    ("output ids: a journal keeps its id across starts; a restored copy, and a journal begun "
      ++ "afresh, take a new one",
      Journal.journalId (ByteArray.mk #[0, 15, 255]) == "000fff"
        && first.length == 32 && same == first && copy != first && afterCopy == copy
        && afresh != copy) ]

/-- How often a shard saves when it is started on `past`, saves every `every` entries, and is
given nothing to do. -/
def savesAtStart (past : List (Journal.Entry (sig (Fin 3)))) (every : Nat) : Async Nat := do
  let (log, _) ← memory past
  let saves ← IO.mkRef 0
  let rt ← Runtime.start Bank3 { snapshotEvery := every }
    (journal := some { log with save := some fun _ => saves.modify (· + 1) })
  rt.idle
  rt.stop
  saves.get

def overdueTest : Async (List (String × Bool)) := do
  let past : List (Journal.Entry (sig (Fin 3))) :=
    [.advance 0, .input (.transfer ⟨7, 0, 1, 3⟩), .batch 64, .handed]
  return [
    ("durable: a shard started on a journal as long as the distance between two saves saves "
      ++ "at once", (← savesAtStart past past.length) == 1),
    ("durable: and one started on a shorter journal does not",
      (← savesAtStart past (past.length + 8)) == 0) ]

/-- The journal stops taking writes. The shard must end, say so, and leave nobody waiting:
neither those it had heard from nor those whose commands it never took. -/
def failTest : Async (List (String × Bool)) := do
  let (log, durable) ← memory [] (failAt := some 1)
  let seen ← IO.mkRef #[]
  let rt ← Runtime.start Bank3 {} (journal := some log) fun response =>
    seen.modify (·.push response.req)
  rt.input (.transfer ⟨100, 0, 1, 3⟩)
  rt.idle
  let waiters ← (List.range 8).mapM fun n => do
    discard <| rt.tryInput (.transfer ⟨n, 0, 1, 3⟩)
    let done ← IO.Promise.new
    background do done.resolve (← throws rt.idle)
    return done
  let released ← waiters.mapM fun done => within 2000 (await done.result?)
  let error ← within 2000 rt.ended
  rt.stop
  let durable ← durable.get
  return [
    ("durable: when the journal cannot be written the shard ends and says why",
      (error.map (·.isSome)) == some true),
    ("durable: nothing is handed over that is not in the journal",
      (← seen.get) == #[100] && durable == #[100]),
    ("durable: and nobody is left waiting for it", released.all (·.isSome)) ]

/-! Snapshots: a bank that saves its kernel every few entries and cuts its journal. -/

def saving (path : System.FilePath) : Journal.Store Bank3 :=
  { store path with actors := some (actors Codec.fin 100) }

def startSaving (path : System.FilePath) (seen : IO.Ref (Array Nat)) (every : Nat) :
    Async (Runtime Bank3) := do
  Runtime.start Bank3 { snapshotEvery := every } (fun out => seen.modify (·.push out.req))
    (some (← (saving path).open))

def snapshotTest : Async (List (String × Bool)) := do
  let path ← scratch "snapshot"
  let first ← IO.mkRef #[]
  let rt ← startSaving path first 8
  for n in [0:20] do rt.input (.transfer ⟨n, 0, 1, 3⟩)
  rt.idle
  let before ← balances rt
  rt.stop
  let log ← (saving path).open
  let kept := log.past.length
  let savedAt := log.saved.map (·.1)
  log.close
  let second ← IO.mkRef #[]
  let rt ← startSaving path second 8
  rt.idle
  let after ← balances rt
  for n in [20:40] do rt.input (.transfer ⟨n, 1, 2, 1⟩)
  rt.idle
  let later ← balances rt
  rt.stop
  let third ← IO.mkRef #[]
  let rt ← startSaving path third 8
  rt.idle
  let last ← balances rt
  rt.stop
  let saved ← (path.addExtension "snapshot").pathExists
  if saved then IO.FS.removeFile (path.addExtension "snapshot")
  let orphan ← IO.mkRef #[]
  let rt ← startSaving path orphan 8
  let refused ← within 2000 rt.ended
  rt.stop
  remove path
  return [
    ("snapshot: the journal is cut when the kernel is saved",
      saved && kept < 20 && (savedAt.map fun index => decide (index > 20)) == some true),
    ("snapshot: a shard started from a snapshot is in the state it was in",
      before == [40, 160, 100] && after == before),
    ("snapshot: outputs handed over before the save are not handed over again",
      (← first.get).size == 20 && (← second.get) == (Array.range' 20 20)),
    ("snapshot: it goes on from there, and comes back again",
      later == [40, 140, 120] && last == later && (← third.get) == #[]),
    ("snapshot: a cut journal whose snapshot is gone is refused, not replayed from nothing",
      (refused.map (·.isSome)) == some true) ]

/-- The process may die between the three steps of a save. Each state the files can be left in
is built here by hand, and the shard must come back in the same state from each. -/
def windowsTest : Async (List (String × Bool)) := do
  let path ← scratch "windows"
  let seen ← IO.mkRef #[]
  let rt ← startSaving path seen 1000000
  for n in [0:10] do rt.input (.transfer ⟨n, 0, 1, 3⟩)
  rt.idle
  let expected ← balances rt
  rt.stop
  let whole ← IO.FS.readBinFile path
  let log ← (saving path).open
  let index := log.past.length
  let some save := log.save | return [("snapshot: a store with codecs can save", false)]
  let image := ((Journal.recover Bank3 log.past).1.exec [.snapshot]).kernel.image
  save image
  log.close
  let cutJournal ← IO.FS.readBinFile path
  let snapshot ← IO.FS.readBinFile (path.addExtension "snapshot")
  let mark := Journal.encode (Request.codec Codec.fin)
    ([.snapshot index] : List (Journal.Entry (sig (Fin 3))))
  let comesBack := fun (journal : ByteArray) (saved : Option ByteArray) => do
    IO.FS.writeBinFile path journal
    match saved with
    | some bytes => IO.FS.writeBinFile (path.addExtension "snapshot") bytes
    | none => if ← (path.addExtension "snapshot").pathExists then
        IO.FS.removeFile (path.addExtension "snapshot")
    let rt ← startSaving path seen 1000000
    let found ← within 2000 (do rt.idle; balances rt)
    rt.stop
    return found == some expected
  let marked ← comesBack (whole ++ mark) none
  let placed ← comesBack (whole ++ mark) (some snapshot)
  let done ← comesBack cutJournal (some snapshot)
  remove path
  if ← (path.addExtension "snapshot").pathExists then IO.FS.removeFile (path.addExtension "snapshot")
  return [
    ("snapshot: dying after the mark is written and before the snapshot is in place loses nothing",
      marked),
    ("snapshot: dying after the snapshot is in place and before the journal is cut loses nothing",
      placed),
    ("snapshot: and the finished save gives the same state", done) ]

/-- A journal whose last entry was not wholly written: the entries before it are found, the
journal is cut back to them, and the bytes cut off are in the `.cut` file. -/
def cutTest : Async (List (String × Bool)) := do
  let path ← scratch "cut"
  let input := Request.codec Codec.fin
  let file := Journal.file input "" entries
  let whole := Journal.file input "" entries.dropLast
  let torn := file.extract 0 (file.size - 3)
  IO.FS.writeBinFile path torn
  let log ← (store path).open
  log.close
  let journal ← IO.FS.readBinFile path
  let kept := path.addExtension "cut"
  let cut ← if ← kept.pathExists then some <$> IO.FS.readBinFile kept else pure none
  remove path
  IO.FS.writeBinFile path file
  let log' ← (store path).open
  log'.close
  let nothingCut := !(← kept.pathExists)
  remove path
  return [
    ("journal: a last entry not wholly written is cut off and the entries before it are found",
      written log.past == written entries.dropLast && journal == whole
        && whole.size < torn.size),
    ("journal: the bytes cut off are kept beside the journal, all of them and nothing else",
      cut == some (torn.extract whole.size torn.size)),
    ("journal: nothing is kept beside a journal that was whole",
      nothingCut && written log'.past == written entries) ]

/-- The index of a save's mark is the number of entries written before it, whatever was
written: turns, marks of outputs handed over, and the marks of earlier saves. -/
def countTest : Async (List (String × Bool)) := do
  let path ← scratch "count"
  let turn : List (Journal.Entry (sig (Fin 3))) :=
    [.advance 5, .input (.transfer ⟨1, 0, 1, 3⟩), .batch 64]
  let image := (Journal.recover Bank3 []).1.image
  let log ← (saving path).open
  let some save := log.save | return [("journal: a store with codecs can save", false)]
  log.append turn
  log.note [.handed]
  save image
  log.append turn
  log.note [.handed]
  log.append turn
  save image
  log.append turn
  log.close
  let log ← (saving path).open
  log.close
  remove path
  return [
    ("journal: the mark of a save has the index of the entries written before it, the marks "
      ++ "of earlier saves among them",
      log.saved.map (·.1) == some 12 && log.index == 16
        && written log.past == written (.snapshot 12 :: turn)) ]

/-! A system whose state is its own history, so that an input lost or applied twice shows in
it. Each input also arms a timer, so the saved kernel has an agenda. -/

abbrev tapeSig : Signature where
  Id := Unit
  Msg _ := Option Nat
  In := Nat
  Out := Nat

abbrev tape : System tapeSig where
  State _ := List Nat
  actor _ := {
    init := []
    step := fun s msg =>
      match msg with
      | some n => (n :: s, [.emit n, .after 1 none])
      | none => (s, [])
    recover := fun s => (s, []) }
  accept n := ⟨(), some n⟩

def tapeStore (path : System.FilePath) : Journal.Store tape :=
  { path, input := Codec.nat, system := "tape"
    actors := some { id := Codec.unit, state := fun _ => Codec.list Codec.nat,
                     msg := fun _ => Codec.option Codec.nat } }

def perRound : Nat := 1000000

/-- Run by `lanesTest tape-child path round`: records numbers until it is killed, saving its
kernel every forty entries, and says on standard output which it has acknowledged. -/
def tapeChild (path : System.FilePath) (round : Nat) : IO Unit := do
  let out ← IO.getStdout
  let work : Async Unit := do
    let rt ← Runtime.start tape { snapshotEvery := 40 } (fun n => do
      out.putStrLn (toString n)
      out.flush) (some (← (tapeStore path).open))
    for n in [0:perRound] do rt.input (round * perRound + n)
  work.block

def killSavingTest : Async (List (String × Bool)) := do
  let path ← scratch "tape"
  let mut acknowledged : Array Nat := #[]
  for round in [0:4] do
    let process ← IO.Process.spawn {
      cmd := (← IO.appPath).toString
      args := #["tape-child", path.toString, toString round], stdout := .piped }
    for _ in [0:150 + 37 * round] do
      if let some n := (← process.stdout.getLine).trimAscii.toString.toNat? then
        acknowledged := acknowledged.push n
    process.kill
    discard process.wait
  let log ← (tapeStore path).open
  let kept := log.past.length
  let saved := log.saved.isSome
  log.close
  let rt ← Runtime.start tape {} (journal := some (← (tapeStore path).open))
  rt.idle
  let history := (← rt.state ()).reverse
  rt.stop
  remove path
  let rounds := (List.range 4).map fun round => history.filter (· / perRound == round)
  return [
    ("snapshot: killed four times while saving, the shard has every number it acknowledged",
      acknowledged.size ≥ 600 && acknowledged.all (history.contains ·)),
    ("snapshot: and each number once, in the order sent, with none missing before the last",
      history == rounds.flatten
        && (List.range 4).all fun round =>
          rounds[round]! == (List.range rounds[round]!.length).map (round * perRound + ·)),
    ("snapshot: from a snapshot and a journal much shorter than its history",
      saved && kept < 200) ]

/-- `fsync` itself. That the journal calls it no test can see: only a loss of power could. -/
def fsyncTest : Async (List (String × Bool)) := do
  let path ← scratch "fsync"
  IO.FS.writeFile path "synced"
  Journal.fsync path.toString
  Journal.fsync ((path.parent.getD ".").toString)
  let missing ← (Journal.fsync (path.toString ++ ".missing")).toBaseIO
  remove path
  return [("fsync: a file and its directory are synced, and a path that is not there is an error",
    match missing with | .error (.noFileOrDirectory ..) => true | _ => false)]

/-! An upgrade: the bank's files of version 1, read by version 2. The two versions have the same
types here, so the migration changes nothing; what is tested is what the store and the shell do
with an older version's files. `examples/migration` changes a type. -/

def sameBank : Migration Bank3 Bank3 where
  id := id
  injective _ _ h := h
  state _ s := s
  msg _ m := m
  output o := o
  inv _ _ := True
  keeps _ := ⟨trivial, fun _ _ _ => trivial, fun _ _ => trivial⟩
  lands _ _ _ := trivial

def upgradeTest : Async (List (String × Bool)) := do
  let path ← scratch "upgrade"
  let input := Request.codec Codec.fin
  let past : List (Journal.Entry (sig (Fin 3))) :=
    [.advance 0, .input (.transfer ⟨7, 0, 1, 3⟩), .batch 64, .handed,
      .advance 1, .input (.transfer ⟨8, 0, 1, 3⟩), .batch 64]
  IO.FS.writeBinFile path (Journal.file input (Journal.label "bank" 1) past)
  let upgrade : Journal.Upgrade Bank3 :=
    { old := Bank3, system := Journal.label "bank" 1, input, actors := some (actors Codec.fin 100)
      migration := sameBank }
  let v2 : Journal.Store Bank3 :=
    { saving path with system := "bank", version := 2, upgrades := [upgrade] }
  let owed := Journal.Upgrade.owed [upgrade] { journal := ← IO.FS.readBinFile path }
  let origins ← IO.mkRef #[]
  let run : Async (Array Nat × List Int) := do
    let seen ← IO.mkRef #[]
    let rt ← Runtime.startWith Bank3 {} (journal := some (← v2.open)) fun _ id out => do
      seen.modify (·.push out.req)
      origins.modify (·.push id.origin)
    rt.idle
    let balances ← (List.finRange 3).mapM fun a => do return (← rt.state a).balance
    rt.stop
    return (← seen.get, balances)
  let (first, before) ← run
  let header := (Frame.decode (← IO.FS.readBinFile path)).head?
  let (second, after) ← run
  let unsaved ← ({ v2 with actors := none } : Journal.Store Bank3).open.toBaseIO
  remove path
  return [
    ("upgrade: a start on version 1's files hands over the output version 1 had not",
      first == #[8] && before == [94, 106, 100]),
    ("upgrade: with the id version 1's history gave it",
      owed == [⟨7, 0⟩] && (← origins.get) == #[⟨7, 0⟩]),
    ("upgrade: and writes the migration, so the next start reads version 2's files and hands "
      ++ "nothing over again",
      second == #[] && after == before
        && header == some (Journal.header (Journal.label "bank" 2))),
    ("upgrade: a store that reads older versions and cannot save is refused",
      unsaved.toOption.isNone) ]

/-- A test that throws has failed, and the tests after it still run. -/
def safely (name : String) (test : Async (List (String × Bool))) : IO (List (String × Bool)) := do
  try test.block
  catch e => return [(s!"{name}: threw {e}", false)]

def tests : IO (List (String × Bool)) := do
  return (← safely "restart" restartTest) ++ (← safely "torn" tornTest)
    ++ (← safely "refusal" refusalTest) ++ (← safely "missing" missingTest)
    ++ (← safely "unreadable" unreadableTest)
    ++ (← safely "order" orderTest)
    ++ (← safely "rehand" rehandTest) ++ (← safely "ids" idsTest) ++ (← safely "overdue" overdueTest)
    ++ (← safely "fail" failTest) ++ (← safely "cut" cutTest) ++ (← safely "count" countTest)
    ++ (← safely "snapshot" snapshotTest) ++ (← safely "windows" windowsTest)
    ++ (← safely "kill" killTest) ++ (← safely "kill while saving" killSavingTest)
    ++ (← safely "fsync" fsyncTest) ++ (← safely "upgrade" upgradeTest)

end Tests.Durable
