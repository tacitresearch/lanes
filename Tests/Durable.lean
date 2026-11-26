/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Examples.Bank

/-!
A durable shard: the bank with a journal. It is stopped and started, its journal is cut short,
and a child process running it is killed with SIGKILL in the middle of its work. Each time the
shard comes back in the state its journal describes, with nothing it had acknowledged missing.
-/

namespace Tests.Durable

open Lanes Std Std.Async Examples.Bank

abbrev Bank3 := bank (Fin 3) 100

def store (path : System.FilePath) : Journal.Store Bank3 :=
  { path, input := Request.codec Codec.fin }

def scratch (name : String) : IO System.FilePath := do
  let dir := (← IO.getEnv "TMPDIR").getD "/tmp"
  return s!"{dir}/lanes-{name}-{← IO.monoNanosNow}.journal"

def remove (path : System.FilePath) : IO Unit := do
  for file in [path, path.addExtension "lock", path.addExtension "cut",
      path.addExtension "snapshot"] do
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

def fileTests : List (String × Bool) :=
  let file := Journal.file (Request.codec Codec.fin) "bank" entries
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
      (match opened "ledger" file with | .error .foreign => true | _ => false)),
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

/-- The journal stops taking writes. The shard must end, say so, and leave nobody waiting:
neither those it had heard from nor those whose commands it never took. -/
def failTest : Async (List (String × Bool)) := do
  let (log, _) ← memory [] (failAt := some 2)
  let seen ← IO.mkRef #[]
  let rt ← Runtime.start Bank3 {} (journal := some log) fun response =>
    seen.modify (·.push response.req)
  let waiters ← (List.range 8).mapM fun n => do
    discard <| rt.tryInput (.transfer ⟨n, 0, 1, 3⟩)
    let done ← IO.Promise.new
    background do done.resolve (← throws rt.idle)
    return done
  let released ← waiters.mapM fun done => within 2000 (await done.result?)
  let error ← within 2000 rt.ended
  return [
    ("durable: when the journal cannot be written the shard ends and says why",
      (error.map (·.isSome)) == some true),
    ("durable: nothing is handed over that is not in the journal", (← seen.get).size ≤ 2),
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
  IO.FS.removeFile (path.addExtension "snapshot")
  let orphan ← IO.mkRef #[]
  let rt ← startSaving path orphan 8
  let refused ← within 2000 rt.ended
  rt.stop
  remove path
  return [
    ("snapshot: the journal is cut when the kernel is saved",
      kept < 20 && (savedAt.map fun index => decide (index > 20)) == some true),
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

def tests : IO (List (String × Bool)) := do
  return (← restartTest.block) ++ (← tornTest.block) ++ (← refusalTest.block)
    ++ (← orderTest.block) ++ (← rehandTest.block) ++ (← failTest.block)
    ++ (← snapshotTest.block) ++ (← windowsTest.block) ++ (← killTest.block)
    ++ (← killSavingTest.block)

end Tests.Durable
