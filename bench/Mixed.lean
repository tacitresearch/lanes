/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-! Mixed step costs at p99: `benchMixed [workers] [runs] [requests] [workload…]`.

`clients` (64) clients each keep one request outstanding, closed loop, as connections do: a
request goes to one of 64 counters, chosen by a fixed hash of the client and its number, and its
step mixes a hash for as many microseconds as the workload draws for it; the client sends its
next request when the answer comes. Latency is from the request's sending to its answer's
handing over; throughput is answers a second. The first tenth of each client's requests is a
warm-up and not counted.

Five ways run each workload, taking turns, `runs` times, a fresh shard or threads each time:

- `serial`: the shell with `parallel := .off`, every step on the shard's thread;
- `waves`: `parallel := .on`, every wave of two actors or more on `workers` threads;
- `auto`: `parallel := .auto`, the default, which chooses each batch (D73);
- two prototypes of free-running actors, without the kernel, a journal or any order between
  actors, each handing an answer over as soon as its step is done. In `free, one run queue` each
  counter has a mailbox, an actor with mail is put on one run queue under one lock, and
  `workers` threads each take the next actor and step it on one message. In `free, a queue a
  thread` each of `workers` threads owns the counters whose number it is modulo `workers`, and
  takes all the mail in its queue at once. They bound what an actor runtime without waves could
  give on this workload, whose actors never message each other.

The table gives, for each way, the medians over the runs of p50 and p99 in µs, of the p99 of the
cheap steps alone, and of answers a second, and the spread of each, (highest − lowest) / median.
-/

open Lanes Std.Async

def spin : Nat → UInt64 → UInt64
  | 0, h => h
  | n + 1, h => spin n (mixHash h n.toUInt64)

/-- A request: the counter, the client, its number, the rounds of hashing and when it was sent. -/
structure Req where
  actor : Fin 64
  client : Nat
  seq : Nat
  rounds : Nat
  sent_ns : Nat
  deriving DecidableEq

abbrev sig : Signature where
  Id := Fin 64
  Msg _ := Req
  In := Req
  Out := Req × UInt64

structure Count where
  count : Nat := 0
  hash : UInt64 := 0

def Count.step (s : Count) (r : Req) : Count × UInt64 :=
  let hash := spin r.rounds (s.hash + s.count.toUInt64)
  ({ count := s.count + 1, hash }, hash)

abbrev counters : System sig where
  State _ := Count
  actor _ := {
    init := {}
    step := fun s r => match s.step r with | (s, h) => (s, [.emit (r, h)])
    recover := fun s => (s, []) }
  accept r := ⟨r.actor, r⟩

/-- How a workload draws a step's cost: `heavy_us` with chance `heavyPerMille`, else `cheap_us`. -/
structure Workload where
  name : String
  cheap_us : Nat
  heavy_us : Nat
  heavyPerMille : Nat

def workloads : List Workload :=
  [ { name := "uniform, 2 µs", cheap_us := 2, heavy_us := 2, heavyPerMille := 0 },
    { name := "1 in 50 at 500 µs, else 2 µs", cheap_us := 2, heavy_us := 500, heavyPerMille := 20 },
    { name := "1 in 5 at 50 µs, else 1 µs", cheap_us := 1, heavy_us := 50, heavyPerMille := 200 },
    { name := "uniform, 50 µs", cheap_us := 50, heavy_us := 50, heavyPerMille := 0 } ]

def mix (a b : Nat) : Nat := (mixHash (mixHash 0x9e3779b97f4a7c15 a.toUInt64) b.toUInt64).toNat

structure Setup where
  clients : Nat := 64
  perClient : Nat
  warm : Nat
  roundsPerUs : Nat
  w : Workload

/-- Request `seq` of `client`, sent at `now`. -/
def Setup.req (s : Setup) (client seq now : Nat) : Req :=
  let h := mix client seq
  let us := if (h / 64) % 1000 < s.w.heavyPerMille then s.w.heavy_us else s.w.cheap_us
  { actor := Fin.ofNat 64 h, client, seq, rounds := us * s.roundsPerUs, sent_ns := now }

/-- What a run measured: the latencies counted, those of the cheap steps apart, and the time from
the first request sent to the last answer. -/
structure Result where
  lat_ns : Array Nat
  cheap_ns : Array Nat
  total_ns : Nat
  answers : Nat

/-- What each way keeps while it runs: each client's latencies, the answers, and the promise the
last answer resolves. The latencies are lists, a cell added at a time: a value another thread
has seen is never updated in place, so an array would be copied at every push. -/
structure Tally where
  lat : Array (IO.Ref (List (Nat × Bool)))
  answered : IO.Ref Nat
  last_ns : IO.Ref Nat
  done : IO.Promise Unit

def Tally.new (clients : Nat) : IO Tally :=
  return { lat := ← (List.range clients).toArray.mapM fun _ => IO.mkRef []
           answered := ← IO.mkRef 0, last_ns := ← IO.mkRef 0, done := ← IO.Promise.new }

/-- Count an answer to `r`; the next request of its client, if there is one. -/
def Tally.answer (t : Tally) (s : Setup) (r : Req) : BaseIO (Option Req) := do
  let now ← IO.monoNanosNow
  if s.warm ≤ r.seq then
    let cheap := r.rounds == s.w.cheap_us * s.roundsPerUs
    if let some l := t.lat[r.client]? then l.modify ((now - r.sent_ns, cheap) :: ·)
  let n ← t.answered.modifyGet fun n => (n + 1, n + 1)
  if n == s.clients * s.perClient then
    t.last_ns.set now
    t.done.resolve ()
  if r.seq + 1 < s.perClient then return some (s.req r.client (r.seq + 1) (← IO.monoNanosNow))
  else return none

def Tally.result (t : Tally) (start : Nat) : IO Result := do
  let mut lat := #[]
  for l in t.lat do lat := lat ++ (← l.get).toArray
  return { lat_ns := lat.map (·.1), cheap_ns := (lat.filter (·.2)).map (·.1), total_ns := (← t.last_ns.get) - start, answers := ← t.answered.get }

def runShell (s : Setup) (config : Runtime.Config) : IO Result := do
  let t ← Tally.new s.clients
  let rt ← Lanes.block <| Runtime.startWith counters config fun rt _ out => do
    if let some next ← t.answer s out.1 then discard (rt.tryInput next)
  let start ← IO.monoNanosNow
  for c in [0:s.clients] do Lanes.block (rt.input (s.req c 0 (← IO.monoNanosNow)))
  Parker.wait t.done.result!
  Lanes.block rt.stop
  t.result start

/-- What the free-running prototype's threads share, under one lock: each actor's mailbox and
whether it is on the run queue or being stepped, and the run queue. -/
structure Sched where
  boxes : Array (Array Req × Bool)
  ready : Std.Queue (Fin 64) := .empty
  stop : Bool := false

def Sched.post (q : Sched) (r : Req) : Sched :=
  let (ms, on) := q.boxes.getD r.actor.val (#[], false)
  let boxes := q.boxes.set! r.actor.val (ms.push r, true)
  { q with boxes, ready := if on then q.ready else q.ready.enqueue r.actor }

/-- The next actor on the run queue and its first message. -/
def Sched.next (q : Sched) : Option (Fin 64 × Req) × Sched :=
  match q.ready.dequeue? with
  | none => (none, q)
  | some (a, ready) =>
    let (ms, on) := q.boxes.getD a.val (#[], false)
    if h : 0 < ms.size then
      (some (a, ms[0]), { q with ready, boxes := q.boxes.set! a.val (ms.extract 1 ms.size, on) })
    else (none, { q with ready, boxes := q.boxes.set! a.val (ms, false) })

/-- After a step of `a`: back on the run queue if it has mail, else off it. -/
def Sched.after (q : Sched) (a : Fin 64) : Sched :=
  let (ms, _) := q.boxes.getD a.val (#[], false)
  if ms.isEmpty then { q with boxes := q.boxes.set! a.val (ms, false) }
  else { q with ready := q.ready.enqueue a }

/-- The free-running prototype: `workers` threads, each taking the next actor off the run queue,
stepping it on one message outside the lock, and handing its answer over at once. An actor is
stepped by one thread at a time, since it is on the run queue at most once. -/
structure Free where
  sched : Std.Mutex Sched
  wake : Std.Condvar
  states : Array (IO.Ref Count)

def Free.loop (f : Free) (t : Tally) (s : Setup) : IO Unit := do
  repeat
    let job ← f.sched.atomically do
      f.wake.waitUntil f.sched.mutex do
        let q ← get
        return q.stop || !q.ready.isEmpty
      modifyGet fun q => if q.stop then (none, q) else
        match q.next with | (job, q) => (some job, q)
    match job with
    | none => break
    | some none => pure ()
    | some (some (a, r)) =>
      if let some cell := f.states[a.val]? then cell.modify fun c => (c.step r).1
      let next ← t.answer s r
      f.sched.atomically <| modify fun q =>
        match next with | some n => (q.after a).post n | none => q.after a
      f.wake.notifyOne

def runFree (s : Setup) (workers : Nat) : IO Result := do
  let t ← Tally.new s.clients
  let f : Free := {
    sched := ← Std.Mutex.new { boxes := Array.replicate 64 (#[], false) }
    wake := ← Std.Condvar.new
    states := ← (List.range 64).toArray.mapM fun _ => IO.mkRef {} }
  let threads ← (List.range workers).mapM fun _ => IO.asTask (prio := .dedicated) (f.loop t s)
  let start ← IO.monoNanosNow
  for c in [0:s.clients] do
    let r := s.req c 0 (← IO.monoNanosNow)
    f.sched.atomically (modify (·.post r))
  f.wake.notifyAll
  Parker.wait t.done.result!
  f.sched.atomically (modify ({ · with stop := true }))
  f.wake.notifyAll
  for th in threads do discard <| IO.wait th
  t.result start

/-- A thread of the second prototype: the actors `a` with `a % workers` its number are its own,
and their mail waits in its queue, taken all at once. -/
structure Owner where
  queue : Std.Mutex (Array Req × Bool)
  wake : Std.Condvar

def Owner.post (owners : Array Owner) (r : Req) : BaseIO Unit := do
  let some o := owners[r.actor.val % owners.size]? | return
  o.queue.atomically (modify fun (q, stop) => (q.push r, stop))
  o.wake.notifyOne

def Owner.loop (owners : Array Owner) (me : Owner) (states : Array (IO.Ref Count)) (t : Tally)
    (s : Setup) : IO Unit := do
  repeat
    let (jobs, stop) ← me.queue.atomically do
      me.wake.waitUntil me.queue.mutex do
        let (q, stop) ← get
        return stop || !q.isEmpty
      modifyGet fun (q, stop) => ((q, stop), (#[], stop))
    if stop then break
    for r in jobs do
      if let some cell := states[r.actor.val]? then cell.modify fun c => (c.step r).1
      if let some next ← t.answer s r then Owner.post owners next

def runOwned (s : Setup) (workers : Nat) : IO Result := do
  let t ← Tally.new s.clients
  let owners ← (List.range (max 1 workers)).toArray.mapM fun _ => do
    return { queue := ← Std.Mutex.new (#[], false), wake := ← Std.Condvar.new : Owner }
  let states ← (List.range 64).toArray.mapM fun _ => IO.mkRef {}
  let threads ← owners.mapM fun o =>
    IO.asTask (prio := .dedicated) (Owner.loop owners o states t s)
  let start ← IO.monoNanosNow
  for c in [0:s.clients] do Owner.post owners (s.req c 0 (← IO.monoNanosNow))
  Parker.wait t.done.result!
  for o in owners do
    o.queue.atomically (modify fun (q, _) => (q, true))
    o.wake.notifyOne
  for th in threads do discard <| IO.wait th
  t.result start

def percentile (sorted : Array Nat) (perMille : Nat) : Nat :=
  if sorted.isEmpty then 0 else sorted[min (sorted.size - 1) (sorted.size * perMille / 1000)]!

def median (xs : Array Nat) : Nat :=
  let s := xs.qsort (· < ·)
  s[s.size / 2]!

def spreadPct (xs : Array Nat) : Nat :=
  (xs.foldl max 0 - xs.foldl min xs[0]!) * 100 / max 1 (median xs)

/-- Rounds of `spin` a microsecond on this machine, the fastest of five timings. -/
def calibrate : IO Nat := do
  let mut best := 0
  for i in [0:5] do
    let n := 1000000
    let start ← IO.monoNanosNow
    let h := spin n (start + i).toUInt64
    let ns := (← IO.monoNanosNow) - start
    if h == 1 then IO.println ""
    best := max best (n * 1000 / max 1 ns)
  return best

def main (args : List String) : IO Unit := do
  let arg (i : Nat) (d : Nat) := (args[i]? >>= String.toNat?).getD d
  let workers := arg 0 4
  let runs := max 1 (arg 1 5)
  let requests := max 640 (arg 2 32000)
  let only := (args.drop 3).filterMap String.toNat?
  let roundsPerUs ← calibrate
  IO.println s!"{roundsPerUs} rounds of hashing a µs; {workers} workers, {runs} runs, \
    {requests} requests a run from 64 clients"
  let ways : List (String × (Setup → IO Result)) :=
    [("serial", fun s => runShell s { workers, parallel := .off }),
     ("waves", fun s => runShell s { workers, parallel := .on }),
     ("auto", fun s => runShell s { workers, parallel := .auto }),
     ("free, one run queue", fun s => runFree s workers),
     ("free, a queue a thread", fun s => runOwned s workers)]
  IO.println "| workload | way | p50 µs | p99 µs | p99 of cheap steps µs | answers/s |"
  IO.println "| --- | --- | ---: | ---: | ---: | ---: |"
  for (w, index) in workloads.zipIdx do
    unless only.isEmpty || only.contains index do continue
    let perClient := requests / 64
    let s : Setup := { perClient, warm := perClient / 10, roundsPerUs, w }
    let mut p50s : Array (Array Nat) := Array.replicate ways.length #[]
    let mut p99s : Array (Array Nat) := Array.replicate ways.length #[]
    let mut cheap99s : Array (Array Nat) := Array.replicate ways.length #[]
    let mut rates : Array (Array Nat) := Array.replicate ways.length #[]
    for r in [0:runs] do
      for j in [0:ways.length] do
        let m := (j + r) % ways.length
        let res ← (ways[m]!).2 s
        let sorted := res.lat_ns.qsort (· < ·)
        p50s := p50s.modify m (·.push (percentile sorted 500 / 1000))
        p99s := p99s.modify m (·.push (percentile sorted 990 / 1000))
        cheap99s := cheap99s.modify m
          (·.push (percentile (res.cheap_ns.qsort (· < ·)) 990 / 1000))
        rates := rates.modify m (·.push (res.answers * 1000000000 / max 1 res.total_ns))
    for (way, m) in ways.zipIdx do
      let cell := fun (xs : Array Nat) => s!"{median xs} ({spreadPct xs}%)"
      IO.println s!"| {w.name} | {way.1} | {cell p50s[m]!} | {cell p99s[m]!} | \
        {cell cheap99s[m]!} | {cell rates[m]!} |"
