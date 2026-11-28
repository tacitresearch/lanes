/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Runtime.IO.Shell
public import Lanes.Durable.Upgrade
public import Lanes.Durable.Reading
public import Lanes.Durable.IO.Ship

/-!
The files of a journal. What they mean, which are refused, what a shard writes to them and in
what order are pure functions with their theorems (`Lanes/Durable/Disk.lean`): whenever the
process dies, the files it leaves load as the kernel it had. Trusted here: locking, reading the
two files as `Journal.Reading` says (a read that fails is not a file that is not there), and
that a write does what `Journal.Disk.apply` and `Journal.Disk.crash` say. That is: bytes
appended and flushed stay, an append that did not finish leaves some of its first bytes and
nothing else, and a rename replaces a file at once.

Every write that is flushed is also synced to the disk before the next begins (`fsync`, bound in
`native/lanes.c`): an append, a file written beside its target before it is renamed, and the
directory after the rename. So the files left by a loss of power are files the process could
have left by dying, and the theorems cover both.
-/

public section

namespace Lanes.Journal

variable {σ : Signature}

/-- Where a shard keeps its journal and how its inputs are written. -/
structure Store (sys : System σ) where
  /-- The journal's file. Its snapshot, its lock, its id and a write that did not finish are kept
  beside it, with the extensions `.snapshot`, `.lock`, `.id` and `.cut`, and how far it was
  shipped, when it is, with `.shipped`. -/
  path : System.FilePath
  /-- How the journal writes inputs. A start replays them through the step functions, from
  the last snapshot if there is one. -/
  input : Codec σ.In
  /-- The application's name for the system. A journal written under another name is refused. -/
  system : String := ""
  /-- The version of the system's types and step functions. The files carry it with the name
  (`Journal.label`); a file of version 0 carries the name alone, as every file did before
  there were versions. -/
  version : Nat := 0
  /-- The older versions this store reads, each with its system, its codecs and the migration
  from it (`Journal.Upgrade`). A start that finds the files of one migrates them and saves, so
  the store needs `actors`. -/
  upgrades : List (Upgrade sys) := []
  /-- How the actors are written down. With it the shard saves its kernel from time to time,
  beside the journal as `.snapshot`, and cuts the journal; without it the journal only grows. -/
  actors : Option (Kernel.Image.Codecs sys) := none
  /-- Whether a journal that is not there is begun. Without it a start that finds none is
  refused, which is what a shard that must not come back having forgotten needs. -/
  create : Bool := true
  /-- The files are a copy restored from elsewhere, production into staging: this is a start
  with no effects. The outputs the files owe are not handed over but marked handed, and the
  journal takes a new id, so that no output of the copy has the id of one of the original's.
  Set it for the first start of a copy only: every start with it drops what the shard owes.
  Jobs the copy holds in flight are attempted again when their deadlines pass, by the copy's
  own workers and under new ids. -/
  restored : Bool := false
  /-- Where to ship the journal's segments and snapshots, for backups and restores to a point
  (`Lanes.Journal.Ship`, `Store.restore`). Nothing the shard does waits for it. -/
  ship : Option Ship.Target := none

/-- A label as a person reads it: the name, then the version if there is one. -/
private def shown (label : String) : String :=
  label.replace "\nversion " ", version "

private def Refusal.explain (system : String) (upgrades : Bool) : Refusal → String
  | .foreign (some named) =>
    s!"it is the journal of \"{shown named}\", not of \"{shown system}\""
      ++ if upgrades then ", and no upgrade reads it" else ""
  | .foreign none => "it is not a journal"
  | .unreadable entry =>
    s!"entry {entry} is intact and cannot be read: it holds what this system's inputs do not"
  | .damaged byte => s!"it is damaged at byte {byte}"
  | .snapshot => "its snapshot cannot be read"
  | .apart => "it does not continue its snapshot"
  | .name => "the system's name or the schema of its inputs is too large for a journal"
  | .missing => "it is not there, and this store may not begin one"
  | .format 1 => "it is in format 1, which this Lanes does not read: move the journal and its \
      snapshot aside to begin anew"
  | .format version => s!"it is in format {version}, which this Lanes does not read"
  | .manifest => "its manifest cannot be read, or does not name the schema that follows it"
  | .policy runtime version => s!"it was written by the runtime \"{runtime}\" under policy \
      {version}, not by \"{Journal.runtime}\" under policy {Journal.policy}"
  | .schema error => s!"its schema cannot be read by this system's types: {error}"

/-- Wait until what has been written to the file or directory at `path` is on the disk. -/
@[extern "lanes_fsync"]
opaque fsync (path : @& String) : IO Unit

private def syncDir (path : System.FilePath) : IO Unit :=
  fsync ((path.parent.getD ".").toString)

/-- Only "no such file" is a file not there: any other error is a failure, which the start
refuses (`Disk.ofReadings`). -/
private def reading (path : System.FilePath) : IO Reading := do
  match ← (IO.FS.readBinFile path).toBaseIO with
  | .ok bytes => return .bytes bytes
  | .error (.noFileOrDirectory ..) => return .absent
  | .error e => return .failed s!"{path} cannot be read: {e}"

private def replace (path : System.FilePath) (bytes : ByteArray) : IO Unit := do
  let scratch := path.addExtension "tmp"
  IO.FS.writeBinFile scratch bytes
  fsync scratch.toString
  IO.FS.rename scratch path
  syncDir path

/-- The journal's id, kept beside it. A journal begun now, a restored copy, and a journal from
before there were ids take a new one, which is written before anything else, so that the
journal never has outputs under an id that a start could forget. -/
private def journalIdAt (path : System.FilePath) (fresh : Bool) : IO String := do
  if !fresh then
    match ← reading path with
    | .bytes bytes =>
      if let some id := (String.fromUTF8? bytes).map (·.trimAscii.toString) then
        unless id.isEmpty do return id
    | .absent => pure ()
    | .failed why => throw (IO.userError s!"lanes: {why}")
  let id := journalId (← IO.getRandomBytes 16)
  replace path (id ++ "\n").toUTF8
  return id

/-- How far the segments of the journal `id` that were stored reach, as the file `.shipped`
beside it says. It is a hint, written without a sync: one that is not there, is torn, or names
another journal is `0`, and everything the files hold is shipped again. -/
private def shippedTo (path : System.FilePath) (id : String) : IO Nat := do
  match ← reading path with
  | .bytes bytes =>
    match ((String.fromUTF8? bytes).map (·.trimAscii.toString.splitOn " ")) with
    | some [named, reached] => return if named == id then reached.toNat?.getD 0 else 0
    | _ => return 0
  | _ => return 0

/-- One write, done as `Disk.apply` says. Without `flush` an append may be lost with the
process, and comes before whatever is appended after it. -/
private def perform (path : System.FilePath) (handle : IO.Ref IO.FS.Handle) (flush : Bool) :
    Write → IO Unit
  | .append bytes => do
    (← handle.get).write bytes
    if flush then
      (← handle.get).flush
      fsync path.toString
  | .putSnapshot bytes => replace (path.addExtension "snapshot") bytes
  | .putJournal bytes => do
    replace path bytes
    handle.set (← IO.FS.Handle.mk path .append)

/--
Lock the journal, read it, and open it for appending. The lock is a file beside the journal and
is taken before anything is read, so a second process cannot start on a journal that another is
still writing. It is held until the log is closed.

What the files give and whether they are refused is `Disk.begin`; a refused file is left as it
is. What is then written is `Disk.mend`, and a write that did not finish is kept beside the
journal as `.cut`; or, for the files of an older version, the migration's writes, which the
shard performs once it has handed over the old outputs (`Log.migrate`). A turn writes
`appendWrites` and a save `saveWrites`.
-/
def Store.open {sys : System σ} [Hashable σ.Id] (store : Store sys) : IO (Log sys) := do
  let system := label store.system store.version
  if !store.upgrades.isEmpty && store.actors.isNone then
    throw (IO.userError "lanes: a store that reads older versions needs the codecs of its actors")
  let lock ← IO.FS.Handle.mk (store.path.addExtension "lock") .append
  unless ← lock.tryLock do
    throw (IO.userError s!"lanes: the journal {store.path} is in use by another process")
  try
    let disk ← match Disk.ofReadings (← reading store.path)
        (← reading (store.path.addExtension "snapshot")) with
      | .ok disk => pure disk
      | .error why => throw (IO.userError s!"lanes: the journal {store.path} is refused: {why}")
    let begun ← match disk.begin store.input store.actors system store.create store.upgrades with
      | .ok begun => pure begun
      | .error refusal =>
        throw (IO.userError s!"lanes: the journal {store.path} is refused: \
          {refusal.explain system !store.upgrades.isEmpty}")
    let fresh := match begun with
      | .found found => found.size = 0
      | .upgraded _ => false
    let id ← journalIdAt (store.path.addExtension "id") (fresh || store.restored)
    let handle ← IO.mkRef (← IO.FS.Handle.mk store.path .append)
    let mut migrate : IO Unit := pure ()
    let mut pending : List (Origin × σ.Out) := []
    match begun with
    | .found found =>
      if found.size < disk.journal.size then
        IO.FS.writeBinFile (store.path.addExtension "cut")
          (disk.journal.extract found.size disk.journal.size)
      syncDir store.path
      if !found.current then
        if let some m := manifest? disk.journal then
          IO.eprintln s!"lanes: the journal {store.path} was written by Lanes {m.lanes} with Lean \
            {m.toolchain}, or with another schema of its inputs; it is written again with this \
            one's, Lanes {lanesVersion}"
      unless found.current || found.past.all (Entry.fits store.input) do
        throw (IO.userError s!"lanes: the journal {store.path} cannot be written again with \
          this system's schema: an entry is too large")
      (disk.mend store.input system found).forM (perform store.path handle true)
    | .upgraded upgraded =>
      if let some actors := store.actors then
        unless savedFits actors system upgraded.index upgraded.image
            && Entry.fits store.input (.snapshot upgraded.index) do
          throw (IO.userError "lanes: an actor is too large to save")
      pending := Upgrade.label upgraded.index (Upgrade.owed store.upgrades disk) upgraded.pending
      migrate := upgraded.writes.forM (perform store.path handle true)
    let found := begun.toFound
    let count ← IO.mkRef found.index
    let shipper ← store.ship.mapM fun target => do
      fsync store.path.toString
      let snapshot := match begun with
        | .found _ => disk.snapshot
        | .upgraded up => (Ship.snapshotOf? up.writes).or disk.snapshot
      let hint := store.path.addExtension "shipped"
      let initial := Ship.start (found.index - found.past.length) found.past
        (found.saved.bind fun (index, _) => snapshot.map (index, ·)) (← IO.monoMsNow)
        (← shippedTo hint id)
      Ship.Shipper.start target store.input system id initial fun reached =>
        IO.FS.writeFile hint s!"{id} {reached}\n"
    let tell := fun (e : Ship.Event σ) => (shipper.forM (·.tell e) : IO Unit)
    let write := fun (flush : Bool) (entries : List (Entry σ)) => do
      unless entries.all (Entry.fits store.input) do
        throw (IO.userError "lanes: an input is too large to journal")
      (appendWrites store.input entries).forM (perform store.path handle flush)
      count.modify (· + entries.length)
      tell (.wrote entries flush)
    let save := fun (actors : Kernel.Image.Codecs sys) (image : Kernel.Image sys) => do
      let index ← count.get
      unless savedFits actors system index image
          && Entry.fits store.input (.snapshot index) do
        throw (IO.userError "lanes: an actor is too large to save")
      let writes := saveWrites store.input actors system index image
      writes.forM (perform store.path handle true)
      count.modify (· + 1)
      tell (.wrote [.snapshot index] true)
      if let some bytes := Ship.snapshotOf? writes then tell (.saved index bytes)
    return {
      past := found.past, saved := found.saved, index := found.index, pending, migrate, id
      restored := store.restored
      append := write true
      note := write false
      save := store.actors.map save
      close := do
        (← handle.get).flush
        if let some s := shipper then
          fsync store.path.toString
          s.tell (.wrote [] true)
          s.close
        lock.unlock }
  catch e =>
    lock.unlock
    throw e

/-- What a restore wrote. -/
structure Restored where
  journal : String
  /-- The position of the mark of the snapshot it started from. -/
  snapshot : Option Nat
  segments : Nat
  /-- How many entries of the history it holds. -/
  point : Nat
  deriving Repr

/--
Write the store's files from what `target` holds: the journal `journal`, or the one written last,
at `point` (`Restore.plan`). The objects are checked against the SHA-256 their names carry, and
the segments must be journals of this store's system that join (`Restore.journal`). The journal
written ends with a `handed` mark and the restore leaves no `.id`, so the first start of the
files hands nothing over and takes a new id: a restore is a copy with no effects
(`docs/decisions/D105-output-ids.md`). A journal or a snapshot already at the store's path is
never overwritten: the restore is refused.
-/
def Store.restore {sys : System σ} (store : Store sys) (target : Ship.Target)
    (point : Restore.Point := .latest) (journal : Option String := none) : IO Restored := do
  let system := label store.system store.version
  let refuse := fun {α : Type} (why : String) =>
    (throw (IO.userError s!"lanes: no restore to {store.path}: {why}") : IO α)
  for path in [store.path, store.path.addExtension "snapshot"] do
    if ← path.pathExists then refuse s!"{path} is there; move it aside first"
  let some keys ← target.remote.list target.keyPrefix | refuse "the store's listing failed"
  let objects := keys.filterMap fun (key, modified) => Restore.listed? target.keyPrefix key modified
  let some journal := journal.or (Restore.newest objects)
    | refuse s!"there is no journal under \"{target.keyPrefix}\""
  let some plan := Restore.plan objects journal point
    | refuse s!"the objects of the journal {journal} do not reach that point"
  let base := target.keyPrefix ++ journal ++ "/"
  let fetch := fun (name : String) => do
    let some bytes ← target.remote.get (base ++ name) | refuse s!"{base ++ name} cannot be read"
    let sum := match Restore.Object.parse? name with
      | some (.segment _ _ sum) | some (.snapshot _ sum) => sum
      | none => ""
    unless Ship.sum bytes == sum do
      refuse s!"{base ++ name} does not have the SHA-256 its name gives"
    return bytes
  let snapshot ← plan.snapshot.mapM fun (_, name) => fetch name
  let mut pieces := #[]
  for (name, first, stop) in plan.segments do
    let some piece := Restore.piece? store.input system first (stop - first) (← fetch name)
      | refuse s!"{base ++ name} is not a journal of \"{system}\" with the entries its name gives"
    pieces := pieces.push piece
  let some entries := Restore.journal (plan.snapshot.map (·.1)) plan.point pieces.toList
    | refuse s!"the segments of the journal {journal} do not join"
  if let some bytes := snapshot then replace (store.path.addExtension "snapshot") bytes
  for stale in ["id", "shipped"] do
    try IO.FS.removeFile (store.path.addExtension stale) catch _ => pure ()
  replace store.path (file store.input system entries)
  return { journal, snapshot := plan.snapshot.map (·.1), segments := plan.segments.length
           point := plan.point }

end Lanes.Journal
