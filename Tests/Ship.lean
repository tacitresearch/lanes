/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Lanes.Testing
import Tests.Durable

/-!
Shipping a journal to an object store and restoring it (`Lanes/Durable/Ship.lean`,
`Lanes/Durable/Restore.lean`). The decisions on their own: sealing by size, by age and at a
save, the notes that wait for a sync, retries with their backoff, and what is dropped at the
bound; the names of the objects, the planner's choice of a snapshot and of segments, and the
stitching of segments that overlap or leave a gap. Then live, against the fake S3 of the test
kit: a bank ships its journal, a restore of it at its end and at points before starts in the
state the journal had there and hands nothing over, a restart ships nothing twice, and a store
that refuses for a while is waited out.
-/

namespace Tests.Ship

open Lanes Std Std.Async Tests.Fixtures.Bank Tests.Durable
open Journal (Entry)
open Journal.Ship (Upload Config State)
open Journal.Restore (Object Listed Point Plan Piece)

abbrev E := Entry (sig (Fin 3))

def input : Codec (Request (Fin 3)) := Request.codec Codec.fin

def tx (n : Nat) : E := .input (.transfer ⟨n, 0, 1, 1⟩)

/-- Entries compared by their bytes in a journal. -/
def enc (entries : List E) : Array UInt8 := (Journal.encode input entries).data

def same (a b : Option (List E)) : Bool := a.map enc == b.map enc

def cfg : Config :=
  { segmentEntries := 3, segmentAge_ms := 100, maxPending := 3, retryBase_ms := 10
    retryMax_ms := 40 }

def feed (st : State (sig (Fin 3))) (events : List (Nat × Journal.Ship.Event (sig (Fin 3)))) :
    State (sig (Fin 3)) :=
  events.foldl (fun st (now, e) => Journal.Ship.step cfg now st e) st

def blank : State (sig (Fin 3)) := Journal.Ship.start 0 [] none 0

/-- What is pending, as (first, count) for a segment and the mark's position for a snapshot. -/
def shape (st : State (sig (Fin 3))) : List (Nat × Nat) :=
  st.pending.map fun
    | .segment first entries => (first, entries.length)
    | .snapshot index _ => (index, 0)

def segmentsOf (st : State (sig (Fin 3))) : List (List E) :=
  st.pending.filterMap fun
    | .segment _ entries => some entries
    | .snapshot .. => none

/-- Puts what the shipper chooses, answered by `answers`, until it waits. -/
def drain (st : State (sig (Fin 3))) (now : Nat) (answers : List Journal.Ship.Outcome) :
    State (sig (Fin 3)) × List (Upload (sig (Fin 3))) := Id.run do
  let mut st := st
  let mut now := now
  let mut put := #[]
  let mut answers := answers
  for _ in [0:64] do
    match Journal.Ship.take cfg now st with
    | (next, .put u) =>
      let outcome := answers.headD .stored
      answers := answers.drop 1
      put := put.push u
      st := Journal.Ship.answer cfg now outcome next
    | (next, .wait (some ms)) => st := next; now := now + ms
    | (next, .wait none) => st := next; break
  return (st, put.toList)

def shipperTests : List (String × Bool) :=
  let two := feed blank [(0, .wrote [tx 0, tx 1] true)]
  let three := feed two [(0, .wrote [tx 2] true)]
  let noted := feed blank [(0, .wrote [tx 0] true), (0, .wrote [.handed] false)]
  let synced := feed noted [(1, .wrote [tx 1, tx 2] true)]
  let young := Journal.Ship.take cfg 50 (feed blank [(0, .wrote [tx 0] true)])
  let old := Journal.Ship.take cfg 100 (feed blank [(0, .wrote [tx 0] true)])
  let failing := (List.range 5).foldl (fun (st, waits) (_ : Nat) =>
      match Journal.Ship.take cfg st.retryAt_ms st with
      | (next, .put _) =>
        let after := Journal.Ship.answer cfg st.retryAt_ms .failed next
        (after, waits ++ [after.retryAt_ms - st.retryAt_ms])
      | (next, .wait _) => (next, waits))
    (three, [])
  let full := feed blank ((List.range 12).map fun n => (0, Journal.Ship.Event.wrote [tx n] true))
  let busy := (Journal.Ship.take cfg 0 three).1
  let busyFull := (List.range 9).foldl (fun st (n : Nat) =>
    Journal.Ship.step cfg 0 st (.wrote [tx (n + 3)] true)) busy
  let saved := feed blank [(0, .wrote [tx 0, .snapshot 1] true), (0, .saved 1 "s".toUTF8)]
  let (stored, put) := drain three 0 [.failed]
  [ ("ship: entries wait until a segment's worth has come", shape two == []),
    ("ship: then they are sealed into a segment from their position", shape three == [(0, 3)]
      && (segmentsOf three).map enc == [enc [tx 0, tx 1, tx 2]]),
    ("ship: an entry written without a sync waits for the next that syncs",
      noted.count == 1 && enc noted.noted == enc [.handed]
        && (segmentsOf synced).map enc == [enc [tx 0, .handed, tx 1, tx 2]]),
    ("ship: a segment is sealed by age, once its first entry has waited long enough",
      (match young.2 with | .wait (some 50) => true | _ => false)
        && (match old.2 with | .put (.segment 0 [_]) => true | _ => false)),
    ("ship: a put that fails is tried again, after a wait that doubles up to its bound",
      failing.2 == [10, 20, 40, 40, 40] && failing.1.failures == 5),
    ("ship: at the bound the oldest is dropped, and the newest kept",
      shape full == [(3, 3), (6, 3), (9, 3)] && full.dropped == 1),
    ("ship: the upload being put is never the one dropped",
      shape busyFull == [(0, 3), (6, 3), (9, 3)] && busyFull.busy && busyFull.dropped == 1),
    ("ship: a save seals the segment that ends with its mark, then its snapshot",
      shape saved == [(0, 2), (1, 0)]),
    ("ship: a failed put is retried and the queue empties",
      stored.idle && put.length == 2 && stored.stored == 1 && stored.storedTo == 3),
    ("ship: a start skips what was stored before, and uploads the snapshot again",
      shape (Journal.Ship.start (σ := sig (Fin 3)) 4 [.snapshot 4, tx 5, tx 6]
        (some (4, "s".toUTF8)) 0 6) == [(4, 0)]
        && (Journal.Ship.start (σ := sig (Fin 3)) 4 [.snapshot 4, tx 5, tx 6] none 0 6).next == 6) ]

/-! The names of the objects, and the planner. -/

def segmentName (first : Nat) (entries : List E) : String :=
  ((Upload.segment first entries).object input "bank").1

def listed (name : String) (modified : String := "2026-11-28T10:00:00.000Z") : String × String :=
  ("backups/j1/" ++ name, modified)

def objects (keys : List (String × String)) : List Listed :=
  keys.filterMap fun (k, m) => Journal.Restore.listed? "backups/" k m

def seg (first stop : Nat) (at_ : String := "2026-11-28T10:00:00.000Z") : String × String :=
  listed s!"segment/{Journal.Ship.digits first}-{Journal.Ship.digits stop}-ab" at_

def snap (index : Nat) (at_ : String := "2026-11-28T10:00:00.000Z") : String × String :=
  listed s!"snapshot/{Journal.Ship.digits index}-cd" at_

def spans (p : Option Plan) : Option (Option Nat × List (Nat × Nat) × Nat) :=
  p.map fun p => (p.snapshot.map (·.1), p.segments.map (·.2), p.point)

def planTests : List (String × Bool) :=
  let name := segmentName 5 [tx 0, tx 1]
  let all := objects [seg 0 5, seg 5 10, snap 9, seg 10 12, seg 12 20]
  let gap := objects [seg 0 5, snap 9, seg 10 12, seg 12 20]
  let late := objects [seg 0 5 "2026-11-28T10:00:00Z", snap 9 "2026-11-28T10:00:01Z",
    seg 10 12 "2026-11-28T10:00:02Z", seg 12 20 "2026-11-28T10:00:03.5Z"]
  let instant (s : String) : Int :=
    ((TimeFormat.parseRfc3339 s).map fun t => t.toUnix * 1000000000 + (t.nanos.val : Int)).getD 0
  [ ("ship: a segment's name holds its positions and the SHA-256 of its bytes",
      Object.parse? name == some (.segment 5 7
        (Journal.Ship.sum (Journal.file input "bank" [tx 0, tx 1])))),
    ("ship: positions are written so that names sort as positions do",
      Journal.Ship.digits 9 < Journal.Ship.digits 10
        && (Journal.Ship.digits 123).length == 20),
    ("restore: a name that is not an object is left out",
      (objects [listed "segment/x-1-ab", listed "segment/5-5-ab", listed "other"]).isEmpty),
    ("restore: the latest is the newest snapshot and the segments after it",
      spans (Journal.Restore.plan all "j1" .latest) == some (some 9, [(10, 12), (12, 20)], 20)),
    ("restore: a point before the newest snapshot starts from boot",
      spans (Journal.Restore.plan all "j1" (.position 7)) == some (none, [(0, 5), (5, 10)], 7)),
    ("restore: a point the segments cannot reach is refused",
      spans (Journal.Restore.plan gap "j1" (.position 7)) == none),
    ("restore: a gap before a snapshot loses only the points before it",
      spans (Journal.Restore.plan gap "j1" .latest) == some (some 9, [(10, 12), (12, 20)], 20)
        && spans (Journal.Restore.plan gap "j1" (.position 11)) == some (some 9, [(10, 12)], 11)),
    ("restore: a point in time counts only what was stored by then",
      spans (Journal.Restore.plan late "j1" (.time (instant "2026-11-28T10:00:03Z")))
          == some (some 9, [(10, 12)], 12)
        && spans (Journal.Restore.plan late "j1" (.time (instant "2026-11-28T10:00:00.5Z")))
          == some (none, [(0, 5)], 5)),
    ("restore: another journal's objects are not used",
      spans (Journal.Restore.plan all "j2" .latest) == none),
    ("restore: the journal written last is the one restored by default",
      Journal.Restore.newest (objects [seg 0 5 "2026-11-28T10:00:00Z"]
        ++ [{ journal := "j2", name := "x", object := .snapshot 0 "", modified := some (10 ^ 19) }])
        == some "j2") ]

/-! Stitching segments into the restored journal. -/

def history : List E := [tx 0, tx 1, .snapshot 2, tx 3, tx 4, .handed, tx 6, tx 7]

def piece (first stop : Nat) : Piece (sig (Fin 3)) :=
  ⟨first, (history.drop first).take (stop - first)⟩

def stitchTests : List (String × Bool) :=
  [ ("restore: a journal from a snapshot is its mark, the entries after, and a handed mark",
      same (Journal.Restore.journal (some 2) 7 [piece 3 5, piece 5 8])
        (some [.snapshot 2, tx 3, tx 4, .handed, tx 6, .handed])),
    ("restore: segments that overlap are stitched where the one before stops",
      same (Journal.Restore.journal none 8 [piece 0 4, piece 2 6, piece 5 8])
        (some (history ++ [.handed]))),
    ("restore: segments with a gap between them do not join",
      (Journal.Restore.journal none 8 [piece 0 4, piece 5 8]).isNone),
    ("restore: nor do segments that stop short of the point",
      (Journal.Restore.journal none 8 [piece 0 4, piece 4 6]).isNone),
    ("restore: a segment read back is the piece it was, and one of another system is not",
      same ((Journal.Restore.piece? (σ := sig (Fin 3)) input "bank" 3 2
          (Journal.file input "bank" [tx 3, tx 4])).map (·.entries)) (some [tx 3, tx 4])
        && (Journal.Restore.piece? (σ := sig (Fin 3)) input "other" 3 2
          (Journal.file input "bank" [tx 3, tx 4])).isNone
        && (Journal.Restore.piece? (σ := sig (Fin 3)) input "bank" 3 3
          (Journal.file input "bank" [tx 3, tx 4])).isNone),
    ("restore: an S3 answer of 412 to a conditional put is an object already there",
      S3.shipped (some (.refused 412 "PreconditionFailed")) == .present
        && S3.shipped (some (.stored none)) == .stored
        && S3.shipped (some (.refused 503 "SlowDown")) == .failed && S3.shipped none == .failed),
    ("restore: a page of a listing is its keys, when they were written, and the next token",
      S3.listedPage (some (.listed
          ⟨[{ key := "a", size := 1, lastModified := "t" }], [], some "n"⟩))
        == some ([("a", "t")], some "n")
        && S3.listedPage (some .missing) == none),
    ("ship: the snapshot uploaded is the one a save puts in place",
      (Journal.Ship.snapshotOf? [.append "j".toUTF8, .putSnapshot "s".toUTF8,
        .putJournal "k".toUTF8]).map (·.data) == some "s".toUTF8.data) ]

def tests : List (String × Bool) := shipperTests ++ planTests ++ stitchTests

/-! ## Live, against the fake S3 -/

def creds : SigV4.Credentials :=
  { accessKeyId := "AKIDEXAMPLE", secretAccessKey := ⟨"wJalrXUtnFEMI/K7MDENG+bPxRfiCYEXAMPLEKEY"⟩ }

def shipping : Config := { segmentEntries := 4, segmentAge_ms := 20, retryBase_ms := 5 }

def target (b : S3.Bucket) : Journal.Ship.Target :=
  S3.backup b creds "backups/" shipping { timeout_ms := 3000 }

def shipped (path : System.FilePath) (b : S3.Bucket) (saves : Bool) : Journal.Store Bank3 :=
  let s := if saves then saving path else store path
  { s with ship := some (target b) }

def run (s : Journal.Store Bank3) (every : Nat) (from_ to : Nat) (seen : IO.Ref (Array Nat)) :
    Async (List Int) := do
  let rt ← Runtime.start Bank3 { snapshotEvery := every } (fun out => seen.modify (·.push out.req))
    (some (← s.open))
  for n in [from_:to] do rt.input (.transfer ⟨n, ⟨n % 3, Nat.mod_lt _ (by decide)⟩,
    ⟨(n + 1) % 3, Nat.mod_lt _ (by decide)⟩, n⟩)
  rt.idle
  let b ← balances rt
  rt.stop
  return b

/-- The segments' ranges, from their names. -/
def ranges (keys : List String) : List (Nat × Nat) :=
  keys.filterMap fun k =>
    match (Journal.Restore.listed? "backups/" k "").map (·.object) with
    | some (Object.segment first stop _) => some (first, stop)
    | _ => none

def disjoint (rs : List (Nat × Nat)) : Bool :=
  rs.all fun a => rs.all fun b => a == b || a.2 ≤ b.1 || b.2 ≤ a.1

def readId (path : System.FilePath) : IO String :=
  return (← IO.FS.readFile (path.addExtension "id")).trimAscii.toString

/-- A bank that saves ships its journal; a restore of it is the bank, with a new id, and owes
nothing. A restart ships nothing twice. -/
def restoreTest : Async (List (String × Bool)) := do
  let fake ← Testing.S3.Fake.start creds "backups" "us-east-2"
  let path ← scratch "ship"
  let seen ← IO.mkRef #[]
  let before ← run (shipped path fake.bucket true) 8 0 30 seen
  let id ← readId path
  let keys ← fake.keys
  let again ← run (shipped path fake.bucket true) 8 0 0 seen
  let keysAgain ← fake.keys
  let copy ← scratch "ship-copy"
  let restored ← (saving copy).restore (target fake.bucket)
  let copySeen ← IO.mkRef #[]
  let after ← run (saving copy) 8 0 0 copySeen
  let copyId ← readId copy
  let refused ← try discard ((saving copy).restore (target fake.bucket)); pure false
    catch _ => pure true
  fake.stop
  remove path; remove copy
  for p in [path, copy] do
    if ← (p.addExtension "shipped").pathExists then IO.FS.removeFile (p.addExtension "shipped")
  return [
    ("ship live: the journal's segments and snapshots are in the store under its id",
      keys.any (·.startsWith s!"backups/{id}/segment/")
        && keys.any (·.startsWith s!"backups/{id}/snapshot/")),
    ("ship live: no two segments hold the same position, a restart included",
      disjoint (ranges keysAgain) && again == before && keys.all keysAgain.contains),
    ("ship live: a restore of the latest starts in the state the journal was in",
      after == before && restored.journal == id && restored.point ≥ 30
        && restored.snapshot.isSome),
    ("ship live: the restored copy hands nothing over and takes a new id",
      (← copySeen.get).isEmpty && copyId != id && !copyId.isEmpty),
    ("ship live: a restore never writes over a journal that is there", refused) ]

open Journal (Disk) in
/-- A bank that never saves: its journal holds its whole history, and a restore at each of
several points loads as what replaying the history's entries up to there gives. -/
def pointsTest : Async (List (String × Bool)) := do
  let fake ← Testing.S3.Fake.start creds "backups" "us-east-2"
  let path ← scratch "ship-points"
  let seen ← IO.mkRef #[]
  discard <| run (shipped path fake.bucket false) 65536 0 12 seen
  let history := match Disk.read (sys := Bank3) input none "" { journal := ← IO.FS.readBinFile path } with
    | .ok found => found.past
    | .error _ => []
  let codecs := actors Codec.fin 100
  let mut good := true
  let mut tried := 0
  for point in [1, 5, history.length / 2, history.length] do
    let copy ← scratch "ship-point"
    let restored ← (store copy).restore (target fake.bucket) (.position point)
    let disk : Disk := { journal := ← IO.FS.readBinFile copy }
    let expected := (Journal.recover Bank3 (history.take point)).1
    let ok := restored.point == point && match disk.load Bank3 input none "" with
      | .ok (kernel, owed) =>
        Journal.saved codecs "" 0 kernel.image == Journal.saved codecs "" 0 expected.image
          && owed.isEmpty
      | .error _ => false
    good := good && ok
    tried := tried + 1
    remove copy
  fake.stop
  remove path
  if ← (path.addExtension "shipped").pathExists then IO.FS.removeFile (path.addExtension "shipped")
  return [("ship live: a restore at a point loads as the journal's entries up to that point",
    good && tried == 4 && history.length > 12)]

/-- A store that refuses for a while is waited out, and nothing is lost. -/
def refusingTest : Async (List (String × Bool)) := do
  let fake ← Testing.S3.Fake.start creds "backups" "us-east-2"
  fake.refuse 6
  let path ← scratch "ship-refused"
  let seen ← IO.mkRef #[]
  let before ← run (shipped path fake.bucket true) 8 0 10 seen
  let left ← fake.refusing
  let copy ← scratch "ship-refused-copy"
  let restored ← (saving copy).restore (target fake.bucket)
  let after ← run (saving copy) 8 0 0 (← IO.mkRef #[])
  fake.stop
  remove path; remove copy
  for p in [path, copy] do
    if ← (p.addExtension "shipped").pathExists then IO.FS.removeFile (p.addExtension "shipped")
  return [("ship live: puts refused for a while are tried again until they are stored",
    left == 0 && after == before && restored.point > 10)]

def live : Async (List (String × Bool)) := do
  return (← restoreTest) ++ (← pointsTest) ++ (← refusingTest)

end Tests.Ship
