# D97. A data format that outlives its version: one schema per file, values read by name

Status: Superseded by D110-volatile-actors.md

The owner set the direction; the details of section 8 are settled as stated
there. This decision moves no code; the order of work (section 7) does.

What Lanes writes to disk and sends between processes is the most expensive thing to change
later. Code can be rewritten in an afternoon. A file written by version 1 must be read by every
version after it, for as long as the file exists. Today one codec writes the journal, the
snapshot and the parcels between peers (`Lanes/Data/Codec.lean`). This decision proposes the
format that replaces it, before anything depends on the current one: 0.1.0 is not released
(`CHANGELOG.md`), and no deployment has run on AWS (`docs/DEPLOY.md`, "What has not been
checked").

Lanes means to be the one dependency for building software in Lean, as Erlang/OTP is for Erlang.
So the codec is a general serialization library of Lanes, used alike for journals, snapshots,
messages between peers and files. It is built on Lean's primitives where they serve
(`ByteArray`, `Std`, the module system), and it gives mechanism, not policy: a reader says what
it found, and the caller decides what to do about it.

Every claim in section 1 was checked against the code at `4ab888c`. Where code was run, the
section says so. The runs were a scratch Lean file run with `lake env lean` against the built
library, and a compiled benchmark built as a temporary `lean_exe`. Neither is committed.

## 1. What is wrong today

### 1.1 The codec is positional

`Codec.struct%` writes a structure's fields as nested pairs in declaration order, with no names.
`Codec.sum%` writes an inductive type as nested binary sums: constructor `k` of `n` is `k` tags
`1` and then a `0`, and the last constructor is `n - 1` tags `1` and no `0` (`Codec.sum`,
`Codec.inject`). `lanes_data … deriving Codable` derives both (`Lanes/Data/Declare.lean`). A
`Nat` is its decimal text, a `Bool` the `Nat` `0` or `1`, an `Option` a sum with `Unit`. The
law `Codec.sound` holds within one version. Nothing relates two versions, and `Entry.ofBytes`
asks only that every record is used.

What an ordinary edit does to old data. Each row was run:

| Edit | What old data does | What was run |
| --- | --- | --- |
| Append a constructor | The old last constructor's bytes now start a longer one. Usually refused as `unreadable`; sometimes read silently as something else | `Method` with `options` appended: an old `DELETE` with a host header is refused; an old `DELETE /0` with no header reads back as `OPTIONS /`; a list `[b 0, b 0]` of `a \| b (n : Nat)` reads back as `[b 1, a]` once `\| c` is appended |
| Insert a constructor | Silent: every later constructor moves | `head` inserted after `get`: an old `POST` reads as `HEAD` |
| Reorder constructors | Silent | `post` moved first: an old `POST` reads as `GET` |
| Swap two fields of the same type | Silent: the values swap | `{ x := 1, y := 2 }` reads as `{ y := 1, x := 2 }` |
| Add a field with a default | Refused: the default is not used when reading | `z : Nat := 7` added: `none` |
| Change a field's type between types written alike | Silent | a `Nat` 5 reads as the `String` `"5"`; a `Nat` 1 as `true` |

Three more facts:

- Lanes' own records are written the same way. `Journal.Entry.codec` is nested sums by hand, and
  the snapshot's image is a tuple (`Kernel.Image.Codecs.image`, `Lanes/Durable/Snapshot.lean`).
  Lanes cannot add an entry kind or an image field without the same break.
- Each record inside an entry is framed again, with its own length and checksum
  (`Journal.Entry.bytes`). A record costs 8 bytes before its content. Measured: a `handed` mark
  is 44 bytes on disk, `advance 1234567` 41, `batch 64` 45, and a typical `POST` 378 (section 6).
- A count is not checked against what is left. `Codec.readMany` loops as many times as a list's
  count says, and for a type written as no records (`Codec.unit`) each turn reads nothing. A
  damaged or hostile count then costs that many turns. Rule 2.6 asks for a bound.

### 1.2 Lanes' own types are inside every application's files

- A web application's journal is written with `Codec.pair Codec.nat Request.codec`
  (`Http.serve`, `Lanes/Web/IO/Server.lean`): Lanes' `Http.Request` and `Method.codec`
  (`Lanes/Web/Http/Basic.lean`), not the application's types.
- Its snapshot holds the gate's waiting list (`Codec.list Codec.nat`) and its messages,
  `Codec.sum% GateMsg { arrive, answer, expire }` (`Http.frontedActors`,
  `Lanes/Web/Http/Front.lean`), inside a `Kernel.Image`.
- `Schedule.attach` and `Jobs.attach` join Lanes' actor on the left
  (`Lanes/Behaviours/Schedule/Basic.lean`, `Lanes/Behaviours/Jobs/Basic.lean`). The scheduler's
  `Job`, `State` and `Msg` are then in the snapshot, and every application identity `.inr i`
  becomes `.inr (.inr i)`. Adding the scheduler to an application changes the encoding of all
  of its identities.
- This has broken application files once already: "The encoding of `Auth.Sessions` changes, so
  a journal of a state that holds them does not read back" (`CHANGELOG.md`). The application's
  label did not change.

A Lanes release can make every application's files unreadable, or read differently, and nothing
in the files says why.

### 1.3 Raw requests are decoded again at every replay

The journal of a web application holds each prepared `Http.Request`. `Gate.step` calls
`bridge.decode` when it handles `arrive` (`Lanes/Web/Http/Gate.lean`), inside the system, so a
replay decodes every request again with whatever `decode` the new binary has. A renamed route, a
fixed form parser or a new default changes what the journal's tail means. Nothing refuses it,
because the label names only the application's version, which nobody bumps for a route.

The gate's own decisions are replayed too. A request that found `maxPending` waiting was answered
`503`; replayed under a larger bound, it is passed on, and the system applies a request its client
was told was refused. That is why `Http.journalName` puts the gate's settings in the journal's
name, and why `Http.regateUpgrade` exists (`Lanes/Web/Http/JournalName.lean`, and the decision "A
served journal is versioned by the application's name", `docs/decisions/new-journal-version.md`).
Identity reaches the system as a header that `prepare` writes and must also strip (D44).

One consequence is the reverse of what one might expect. The tutorial inserts `decrement` in the
middle of the application's `Request` (`docs/TUTORIAL.md`, `Tests/Tutorial/Counter.lean`). The
journal is not refused: it holds HTTP requests, which still decode, and its tail is replayed
through the new step function without a word. Only a snapshot with an old `Request` still queued
would misread. (The docstring in `Tests/Tutorial/Counter.lean` says `lanes_data` derives "the
codec that writes requests and responses to the journal". For a served application, it writes
the snapshot.)

### 1.4 No manifest

A journal starts `"lanes journal 1\n"` and its label (`Journal.header`); a snapshot
`"lanes snapshot 1\n"` and its label (`Journal.savedHeader`). The label is the application's name
and version (`Journal.label`) and, for `Http.serve`, the gate's settings. Nothing records which
Lanes wrote the file, with which toolchain, which runtime, which scheduling policy or which
types. The toolchain does reach some replays: `Schedule.hashJitter` is Lean's `mixHash` of Lean's
`hash`, and `examples/reminders` and `examples/videos` use it in their step functions. A mismatch
shows up as "entry N is intact and cannot be read" (`Journal.Refusal.unreadable`), or not at all.

### 1.5 Kernel-private terms in the journal and the snapshot

- `Journal.Entry.batch fuel` means "run the kernel's scheduler for `fuel` steps". Its meaning is
  `Kernel.runBatch` and `Kernel.step`: the FIFO queue, the alternation of timers and messages
  (`timerTurn`), and the order of `Due.token`s (`Lanes/Runtime/Kernel.lean`).
- A snapshot is a `Kernel.Image`: cells with `up` and timers as `(msg, Due)`, the queue, the
  agenda, `nextToken`, `clock_ms` and `timerTurn`. Only the states, `up` and the messages are in
  the model's `SysState` (`Lanes/Core/World.lean`).
- A `Migration` maps `Kernel.Cell` and `Kernel.Image` (`Lanes/Durable/Migration.lean`).

Another runtime cannot read these files. A change to the kernel's scheduling changes what an old
tail replays to, silently.

### 1.6 Migrations cannot run the new `boot` or `recover`

`Migration.state` is a total function from old state to new state, with no effects.
`Migration.cell` keeps the old timers, mapped; `Migration.image` keeps the queue, the agenda,
`nextToken` and `timerTurn`. An upgrade starts the new shard from the migrated kernel
(`Upgrade.lean`), so `Kernel.boot` of the new system never runs: an actor added to `boot` in
version 2 does not start until a message reaches it. A migrated actor that was up goes on
without its new `recover`, so version 2 cannot arm a timer for state that version 1 left. (An
actor that was down, or released at rest by D51, does run the new `recover`, at its next message:
`Kernel.run1` calls `Kernel.startActor`.) A `Migration` also has no map of inputs, so a message
in flight that carries one cannot change type.

Running the new `recover` would cost no new proof. `Actor.Inductive` already has a `recover`
case (`Lanes/Core/Actor.lean`), and `Migration.keeps` is `Actor.Inductive`.

### 1.7 `Http.serve` takes no upgrades of the application

D66, "Not done", still holds for the application's own types. Since then `serve` reads a journal
written behind a gate of other settings, through the one upgrade it makes itself
(`Http.regateUpgrade`). It takes no `Journal.Upgrade` from the application. So no web
application can migrate: `examples/videos` renames its journal `videos 3` and starts empty
(`CHANGELOG.md`).

### 1.8 A 32-bit FNV-1a checksum

`Frame.checksum` is FNV-1a over 32 bits (`Lanes/Durable/Frame.lean`). Its module says a checksum
"makes it unlikely, not impossible" that damage passes. Random damage passes about once in 2^32
frames, and FNV gives no guarantee for bursts. Records inside an entry are checksummed a second
time, which costs as much again and adds nothing.

## 2. Options

### Positional, with a version (Lean's `.olean`)

An `.olean` starts with `olean`, a format byte, Lean's version and the toolchain's commit (the
first bytes of `Init/Prelude.olean` in the pinned toolchain), then a memory image. Lean refuses an
`.olean` of another build and rebuilds it from source.

- *For:* the smallest and fastest; today's proofs.
- *Against:* it works because an `.olean` is a cache. A journal cannot be rebuilt from source.
  Every change is a refusal or, as in 1.1, a silent misread, and the version is bumped by hand.

### Numbered fields (Protocol Buffers, Cap'n Proto)

Each field and constructor carries a number that never changes. Protocol Buffers writes a tag
per field and skips tags it does not know; Cap'n Proto lays fields out by their ordinals.

- *For:* renames and reorders are free; unknown fields are skipped; widely known.
- *Against:* the number is a second name, kept by hand beside every field and constructor. Lean's
  `structure` and `inductive` have no place for it, so it would sit in an attribute or a side
  table. Reusing or renumbering a number is the silent corruption of 1.1 again. A dump without
  the schema shows numbers, not names. Protocol Buffers pays a tag in every value.

### Names, with the schema stored once (Go's `gob`, Avro)

A stream or a file begins with the description of its types, names included. Values follow
without names, and a reader matches the writer's types to its own by name. Avro also takes
defaults and aliases for renames.

- *For:* source stays ordinary Lean. Lean's own `deriving ToJson, FromJson` already match by
  name: fields by name, constructors by name, and errors name `Type.field`
  (`Lean/Elab/Deriving/FromToJson.lean` in the toolchain). The body is compact. Reorders, new
  constructors and new defaulted fields are free. A dump needs no application code.
- *Against:* a rename needs an alias, and agents rename freely, so CI must catch it (3.9). A
  reader needs the writer's schema, so a value is readable only after the start of its stream.
  Every use here has a start: a file's header, a connection's handshake, or a blob that carries
  its schema. The matching code must be proved.

**Proposed: names, with the schema stored once.**

### Migrations: transform the state, or upcast entries as they are read

- *Transform the state on upgrade* (Erlang/OTP's `code_change`). A `gen_server` is given its old
  state and the old version during a release upgrade, returns the new state, and runs new code
  from then on. D66 is this shape already.
- *Upcast old entries as they are read* (Akka Persistence's event adapters, the upcasters of
  event-sourcing libraries). Old events are converted to the new type and applied by new code.

A Lanes journal holds inputs, not events. Applying old inputs with new step functions changes
history: an answer already given may disagree with the state rebuilt (D66's first alternative,
rejected for this reason). So upcasting fits *values* (a state or a message in a snapshot, read
by name with defaults), and not a *tail of inputs*.

**Proposed: transform the state; match values by name; replay a tail with the version that
wrote it.**

## 3. The proposal

### 3.1 The library: a schema, a value, a body

- **A schema** describes a type: the primitives (`Nat`, `Int`, `String`, `ByteArray`, `Unit`,
  fixed-width integers), a record of named fields, a sum of named constructors each with named
  fields, `List`, maps, a reference to a named type (so recursive and parameterised types work),
  and one reserved kind, `sealed` (section 4). `deriving Codable` derives it from the
  declaration: the type's, constructors' and fields' names, the fields' types, declared defaults
  and aliases. A schema in a file is of the types as instantiated (`Entry Name Cmd`, not
  `Entry N C`).
- **The schema is written once,** at the start of a file or a stream, for every type the stream
  holds, with a digest of it. Peers exchange schemas when they connect (3.11).
- **The body has no names.** A constructor is its index in the writer's schema; fields come in
  the writer's order; a `Nat` is LEB128, an `Int` a sign and a magnitude, a string or bytes a
  length and then the bytes, a list a count and then its items. A value has exactly one encoding
  (no padded integers), so equal values give equal bytes, which a checksum and a hash of state
  need.
- **Proofs.** A dynamic `Value` (a constructor and its fields, as `Lanes.Json` is for JSON) is
  proved once against the body: reading what was written gives back any value that fits its
  schema. Each type gets `toValue` and `ofValue` from the derive, with the law
  `ofValue (toValue a) = some a` proved by the macro, as today (`cases x <;> rfl`). A direct
  encoder can come later, with a theorem that it equals the `Value` path, if measurement asks for
  it.
- **Limits are parameters** (rule 2.6): the largest record, the longest list, the deepest nesting,
  the longest string. A reader refuses past a limit and names it. A count is checked against the
  bytes left, and against the list limit for a type of no bytes.
- **Errors are data.** A `Codec.Error` names the type, the constructor, the field and the byte
  offset, with a `toString` for messages. Lean's `FromJson` returns `Except String` with a path;
  structured errors keep the path and let the caller decide.
- **Hand-written codecs stay possible.** `Codec.pair` and `Codec.map` give anonymous schemas, so
  they stay positional. Every type Lanes persists is declared with `lanes_data` instead
  (`Journal.Entry`, the image, the gate's messages).
- **Std only, as the rest of the runtime** (rule 1.6). `Lanes.Json` is the second format over the
  same schema later, so one declaration gives both (3.7).

### 3.2 Matching by name when a file is opened

Opening a file computes a plan, once, from the writer's schema (in the file) and the reader's (in
the binary). Reading a value is then lookups by index. The journal and the snapshot are read
whole at a start (`Journal.Store.open`), so in practice every refusal below happens at the start.

| Change between writer and reader | What the reader does |
| --- | --- |
| A constructor added | Accepted: old data never has it |
| A constructor removed, absent from the data | Accepted |
| A constructor in the data, missing from the type | Refused when met, with a message naming it: "the data has `Method.head`, which `Http.Method` does not" |
| A field added with a declared default | Accepted: the default is used |
| A field added without a default | Refused at open, naming the field |
| A field removed | Skipped: the writer's schema says how |
| Fields or constructors reordered | Accepted |
| A rename with a declared alias | Accepted |
| A rename without one | Read as a removal and an addition: refused unless the new name has a default. CI flags it (3.9) |
| A field's type changed | Refused at open, naming the field and both types, unless the type declares a migration (`from Old := f`) |

To prove: with the same schema, the plan reads back what was written. When the reader's schema
grows the writer's only by the accepted rows, reading old bytes gives the old value with the
defaults filled in, and nothing else.

How an alias is written in `lanes_data` is open (question 3).

### 3.3 A manifest

A frame after the header, itself a value of a declared type:

- the format's version (2);
- the Lanes version that wrote it, and its commit when known;
- the application's name and version (today's `system` and `version`);
- the toolchain (`Lean.versionString` and `Lean.githash`, both in `Init`);
- the runtime and the version of its policy (for the kernel: its scheduling and its entries);
- the digest of the schema frame.

The store hands the manifest to a check the application can replace. The default is today's rule,
said better: a journal's tail is refused when the application's version or the runtime's policy
differs, with a message naming both; a snapshot is read when its schema matches by name.

### 3.4 The journal stores the decoded input, not raw HTTP

*Parse, don't validate* (rule 2.2), applied to the journal. `decode` moves before the journal: it
runs on the request's own task, after `arrive` and `prepare`, as `prepare` does now, and it stays
a pure function of the bridge. A served journal then holds `(ReqId, σ.In)`, the application's own
type with its own schema.

The gate's decisions are recorded, not made again. The rule: **a choice whose inputs are not in
the journal is recorded as its outcome.** `advance now_ms` already does this for the clock.

- *`decode` refuses* (a 404, a 400, a page answered at once): answered there; nothing is
  journalled. It changes no state: `Gate.step`'s `.error` case returns the waiting list as it was.
- *`503`, the gate full:* decided at arrival against the waiting list the shard holds; answered;
  nothing is journalled. It changes no state either. The inbox's `503` (`tryInput`) is unchanged.
- *Admitted:* an entry `admit id x`.
- *`504`:* when a request's deadline passes, an entry `expire id`. The gate's answer, and the
  dropping of a later answer to that request, follow from it at replay.

The waiting list is then rebuilt from admissions, answers and expiries. A replay reads neither
`maxPending` nor `requestTimeout_ms`: the gate's settings leave the journal's name, and
`Http.regateUpgrade` is no longer needed. This is the "journal the gate's decisions" alternative
the served-journal decision set aside because it changes the format; here the format changes
anyway. It is also the runtime contract's "gate off the hot path" (branch
`claude/runtime-contract`, `docs/decisions/new-runtime-contract.md`).

What else follows:

- Routes and parsers can change without changing history.
- A secret reaches the journal only if the input type has a field for it. The signed-in user is a
  typed field of `σ.In`, not a header that `prepare` writes and must also strip.
- A change to `Http.Request` touches no file.
- A dump of the journal reads as the application's domain.

To restate and prove again: `Gate.step_bounded`, `Http.served_answered_le_arrived` and
`Http.served_pending_answered` over the new gate, with the answers given at the front counted;
and a new lemma that a refusal leaves the waiting list unchanged. Newly trusted: that the server
sends what `decode` returned, one line in the server's row of `TRUSTED.md`, as for `prepare`.

### 3.5 A neutral snapshot image, defined by the model

An `Image` in Layer 1, the same for every runtime:

- each actor's state and whether it is up;
- its timers, each a message and a deadline in the image's clock, in the order they fire;
- the messages in flight, in order;
- the outputs not yet handed over;
- the clock and the index in the history.

To prove: it abstracts to a `SysState` (drop the deadlines; the model has no time, D42), and the
kernel saves and loads it with the abstraction unchanged, as `Kernel.abs_image_kernel` says now.

Beside it, an optional *runtime section*: bytes named by the runtime and its policy version (for
the kernel: `nextToken` and `timerTurn`), read only by the same runtime. A start of the same
runtime uses both and replays its own tail. Another runtime, or a migration, uses the neutral
part only, and only with an empty tail.

Journal entries stay the runtime's own: `batch fuel` keeps its meaning, now named by the
manifest's policy. A journal in the model's own terms (`Event.deliver`, `Event.timeout`) would be
readable by any runtime but costs an entry per step instead of per batch. It is not proposed now
(question 8).

*Reserved, not designed: actors one at a time.* Durable Objects keeps a store per object and
reloads an idle object from it. The kernel already drops an actor at rest from memory (D51), but
only one equal to its initial state, and only in memory. Loading an actor on demand, or saving
one actor's state alone, would need the image split into sections per actor with an index from
identity to section, and an entry kind that points at an actor's saved state. The format
reserves both: a section kind in the image and an entry kind, with no meaning yet.

### 3.6 Migrations: a state transform that may run the new `boot` and `recover`

- A `Migration` maps the neutral image: identities (injective), states, messages, outputs, and
  inputs, for messages in flight that carry one.
- After the transform, the new runtime starts the new system as a start does: each actor in the
  new `boot` that has no state yet is started, and each migrated actor that was up runs its new
  `recover`, whose effects are performed. Version 2 can then arm timers for state version 1 left.
  No new obligation: `Migration.keeps` is `Actor.Inductive`, which covers `recover` (1.6).
- A change the schema absorbs (a new constructor, a new field with a default, a rename with an
  alias) needs no `Migration`: the new types read the old snapshot by name. A `Migration` is for
  a change of meaning. `lanes_data … from Old := f` stays for that.
- A journal tail written by another version is replayed by the version that wrote it. Either the
  old system stays in the binary, as D66 does it, or the old release runs once in a mode that
  replays, saves and exits, after which the new binary reads a snapshot only. The second needs no
  frozen code in the new binary (question 5).
- `Http.serve` takes upgrades: an application's `Migration` lifted through the gate's join, with
  the inputs and outputs in flight mapped.

### 3.7 `lanes journal`

- `lanes journal dump <file>`: the entries as JSON lines (`Lanes.Json`), from the file's own
  schema, with no application code. A sealed value prints as its key id.
- `lanes journal verify <file>`: checksums, the manifest, the schema, the count of entries.
- `lanes journal schema <file>`: the schema as text.

The same for snapshots. The same schema later drives `ToJson` and `FromJson`, so one declaration
gives both formats, with the same rules for adding a field.

### 3.8 A corpus of old journals in CI

`Tests/Journals/<application>/<release>/`: a journal and a snapshot written by each release,
with the digest of the neutral image they load to. `lake test` loads each with the current code
and compares. It catches what no type checker sees: a change of the kernel's policy, of a Lanes
type, or of the toolchain (`Schedule.hashJitter`). It starts at 0.1.0; before that the format may
still change.

### 3.9 A schema diff in CI

The schema of every persisted type is committed as text, one file per application. A `lanes lint`
check (`schema`, which reads the built modules as `inventory` does) compares it with the schema
the build derives:

- an accepted change (3.2) passes, and `lint --fix` writes the new file;
- a removal, a rename without an alias, or a type change without `from` fails, naming the type,
  the constructor and the field;
- a reorder is reported. It is harmless to the format, but it often comes with a rename, and
  hand-written codecs are still positional.

Agents rename freely. This is where a rename is caught, in review, not in production.

### 3.10 A strong checksum

A frame becomes its length (4 bytes), a 128-bit checksum (the first 16 bytes of SHA-256), then the
payload. SHA-256 is `Sha256.hash`, OpenSSL's, already bound and trusted, with `Sha256.reference`
for the proofs (`Lanes/Lib/Crypto/Native.lean`). An entry is one frame whose payload is one
record: the inner frames go. Measured in section 6: SHA-256 costs about what FNV-1a in Lean costs
now. A frame grows by 12 bytes; an entry loses 8 bytes for every record it had.

TigerBeetle, whose style guide these rules adapt, assumes that disks corrupt and misdirect
writes, and checksums every header and body with 128 bits. It also chains its log, each header
holding the previous one's checksum, so that a frame lost or misplaced in the middle is found.
A chain is an option here (question 2).

### 3.11 Peers

A connection begins with each side's manifest and schema digest; a side sends its schema only
when the digests differ, as `gob` sends a type once per stream. Two builds whose schemas do not
match by name refuse each other, saying which type and field, instead of misreading parcels
(`Lanes/Net/IO/Peers.lean`, `Lanes/Runtime/Shard.lean`).

## 4. Erasure (GDPR): mechanism, not policy, and opt-in

**The requirement: an application that does not use erasure pays nothing.** No byte per value, no
cost at run time, no new concept to learn, and replay exactly as today. The one shared cost is a
reserved kind, `sealed`, in the schema's vocabulary. The format meets it:

- A type with no `Sealed` field has no `sealed` in its schema, and its bytes are what they would
  be without the reservation.
- No store, runtime or server takes a key provider. It is an argument only of the adapters that
  seal and open.
- Retention defaults to keeping everything: nothing is deleted beyond what a save already deletes
  today (it replaces the journal by one that starts at its mark, `Disk.saveWrites`). With
  segments, the default keeps every segment.
- Replay never opens a sealed value, so a journal with sealed values replays as any other.

### Retention: the default story

1. *An erase input, handled by the application.* Its step removes the person's data from its
   state (`forget user`, say). What "forgotten" means for that state is the application's spec,
   proved as any other property.
2. *A snapshot.* The runtime takes a request to save now. Today saves come by count
   (`Runtime.Config.snapshotEvery`, 65,536 entries); an application that wants a bound also saves
   by age.
3. *Deletion of journal segments older than the snapshot.* A save already replaces the journal
   today. If segments and archives come, an application's retention rule deletes those before
   the snapshot that follows an erasure.
4. *Backups expiring.* The stack keeps `SnapshotRetainCount` (7) daily snapshots of the volume
   (`infra/app/lanes-app.yaml`).

So forgotten data leaves the live files at the next save, and the backups one retention period
later. Logs are outside the format and have a retention of their own (`LogRetentionDays`).

### Sealed values: reserved in the format, a library later

- A sealed value is opaque bytes, a key id and an algorithm id. A step can hold it, copy it,
  compare its bytes and put it in an effect. It cannot open it: steps are pure (rule 2.4).
- A `KeyProvider` interface: seal under a key id, and open (which fails once the key is gone).
  There is no key manager, no key service client, and no rule for which key covers which person.
- Values are sealed at the edge, before the journal (in `prepare` or `decode`), and opened in an
  adapter's IO, such as the email adapter that needs an address.
- Crypto-shredding, deleting a person's key, is then a library, with no format change.
- Limits: a step cannot compute on a sealed value (search, sort, check). What must be checked is
  checked before sealing. An identity cannot be sealed: the kernel hashes and compares
  identities. So personal data stays out of identities (`examples/ledger` names its actors by user
  name, `Id.user (name : N)`).

### The hard truth

- After an erasure, the journal before it cannot be replayed from the start. Its segments are
  gone, or must be. Where the data was sealed, the bytes remain and a replay runs, but what it
  rebuilds holds values nobody can open.
- Point-in-time recovery to before the erasure returns redacted values: sealed values whose key is
  gone. A backup older than the erasure holds unsealed data in the clear until it expires; a
  restore from it must have the erasures applied again.

## 5. Perspectives

- **Rob Pike, `gob`** ("Gobs of data", the Go blog, 2011). A stream sends each type's description
  once, then values that refer to it. The receiver matches struct fields by name; a field the
  receiver lacks is ignored, and one the sender lacks keeps its zero value. There are no version
  numbers. This proposal takes types-once and by-name. It does not take zero values: a missing
  field needs a declared default, because a zero that means "no limit" or "user 0" is a silent
  change.
- **Rich Hickey** ("Spec-ulation", Clojure/conj 2016). Grow by accretion: provide more, require
  less, and never break; a change that would break deserves a new name. The rules of 3.2 are
  this: accretion is read, a break is refused or needs a declared migration.
- **Pat Helland**, *Data on the Outside versus Data on the Inside* (CIDR 2005). Inside a service,
  data lives in the current schema. Data sent outside is immutable, has an identity, and must
  carry or point to its schema, because another program reads it at another time. A journal and a
  snapshot are messages to a later version of the application: outside data. Today they are
  written as inside data.
- **Martin Kleppmann**, *Designing Data-Intensive Applications*, chapter 4, "Encoding and
  Evolution", and his comparison of Avro, Protocol Buffers and Thrift: backward and forward
  compatibility, and a reader's schema resolved against a writer's. On logs, the same book
  discusses that an immutable log must still let data be removed, for legal reasons among
  others, and that truly deleting data is hard because copies live in many places. Section 4
  states which copies, and for how long.
- **TigerStyle**, TigerBeetle's style guide, which `AGENTS.md` adapts: put a limit on everything.
  Hence the reader's limits (3.1). TigerBeetle's storage design: checksum everything with 128 bits,
  and assume the disk lies. Hence 3.10.

## 6. Costs

### Proofs to redo

- *The codec* (`Lanes/Data/Codec.lean`, 293 lines): the law of each combinator gives way to one
  round trip of `Value` against the body, and a law per type that the macro proves. New: the plan
  of 3.2 is the identity for equal schemas, and fills defaults for an accretion.
- *The frame* (`Lanes/Durable/Frame.lean`, 45 theorems): the private lemmas about the layout
  (`u32At_u32`, the `frameAt_…` lemmas) change with the checksum's width. The public statements
  (`Frame.decode_encode`, `Frame.decode_take_eq`, `Frame.unfinished_take`) keep their form, so
  `Lanes/Durable/Disk.lean` (34 theorems) mostly does not move.
- *The journal and the snapshot*: an entry is one record, so `Journal.Entry.ofBytes_bytes`,
  `Journal.read_write` and `Journal.read_prefix` keep their statements. The header becomes header,
  manifest and schema, so `Journal.open?`, `Journal.open?_cut`, `Journal.open?_file`,
  `Journal.saved?_saved`, `Journal.saved?_other` and the lemmas of `Disk.lean` and
  `Lanes/Durable/Upgrade.lean` that name `header` are redone.
- *The image and migrations*: `Kernel.abs_image_kernel` and `Journal.resume_eq_recover` restated
  for the neutral image; `Lanes/Durable/Migration.lean` (8 theorems) restated over it, with the
  new start (boot and `recover`).
- *The gate*: the three theorems of 3.4, and `Lanes/Web/Http/JournalName.lean` removed.
- *Applications*: `lanes_data` keeps its syntax, so its 164 declarations in the library, the
  tests and the examples do not change. Codecs the examples build by hand with
  `Codec.pair` and `Codec.map` become derived ones, so that they match by name.

### Size and speed

Measured in this container (4 cores, Intel Xeon at 2.1 GHz with SHA extensions), compiled, the
best of three runs of 100,000 entries. The request is a `POST /todos/n` with six ordinary headers
(host, content type and length, user agent, accept, a user) and 26 bytes of body. "Compact" is a
hand-written prototype of the proposed body (indices and lengths as LEB128, one frame per entry),
without schema resolution: the derived code will be somewhat slower than the prototype.

| | Today | Compact |
| --- | --- | --- |
| A `POST` entry on disk | 378 bytes | 216 bytes |
| `handed` mark | 44 bytes | about 10 |
| `advance 1234567` | 41 bytes | about 12 |
| Encoding 100,000 entries | 467–526 ms (about 5 µs each) | 74–80 ms |
| Decoding 100,000 entries | 442–480 ms | not measured |
| FNV-1a in Lean, the 38 MB file | 47–48 ms | |
| SHA-256 by OpenSSL, the 38 MB file | | 29–31 ms |
| Per entry, 100,000 payloads | FNV-1a 21–22 ms | SHA-256 36–51 ms |

The request's own content is about 187 bytes. Today's encoding adds about 190 bytes to it, the
prototype about 30. The 16-byte checksum is in neither figure above; it adds 12 bytes per entry to
the compact one. With decoded inputs (3.4) a served entry is the application's input, smaller
still. A schema is written once per file: a few hundred bytes for a web application's types,
estimated from their names. Replay is dominated by decoding and by the step functions, so a
smaller body should replay faster; the derived decoder has to show it.

### Trusted code

None for the codec: it is pure and proved. SHA-256 is already bound and trusted. New trusted IO:
the server sends what `decode` returned (3.4), a few lines to save on request and by age, the
deletion of segments when segments exist, and `lanes journal`, which reads files. A key provider
is an interface; each implementation will be a row of `TRUSTED.md` of its own.

### Existing journals

No deployment has run on AWS, and 0.1.0 is not released. The journals that exist are written by
tests and examples as they run. A file of format 1 is refused with a message that names format 1
and says to move the files aside. No converter is written (question 9). `Tests/Durable.lean` and
`examples/migration/Check.lean` build their files again in format 2.

## 7. The order of work

Each step is a pull request of its own, and each builds and passes the checks.

1. This decision.
2. `Schema` and `Value`, derived by `lanes_data`, with `lanes journal schema`. No format changes.
3. The body: encoder and decoder from a schema, with limits and structured errors, proved. Not
   used on disk yet.
4. Matching by name (3.2): the plan, defaults, aliases and refusals, with its theorems.
5. Format 2 of the files: header, manifest, schema; one record per entry; the 128-bit frame;
   format 1 refused. The proofs of the journal, the snapshot and the disk redone.
6. `lanes journal dump` and `verify`.
7. The schema diff in `lanes lint`, and the corpus of journals with its first files.
8. Decoded inputs in the served journal (3.4): the gate's decisions recorded, its theorems
   restated, its settings out of the journal's name.
9. The neutral image (3.5), its theorems, and the snapshot as neutral image and runtime section.
10. `Migration` over the neutral image, with the new start's `boot` and `recover` (3.6).
11. `Http.serve` with upgrades.
12. Peers: the handshake with manifests and schemas (3.11).
13. Erasure: save on request and by age, the retention rule, the reserved `sealed` kind and
    `KeyProvider` interface, and a page in the docs on what an application must do.

Steps 2 to 7 come before 0.1.0. The corpus is frozen at 0.1.0.

## 8. Details settled

1. **Names.** Keep `Codec` and `Codable`, adding `Schema` and `Value`.
2. **The checksum.** The first 16 bytes of SHA-256, through the binding already trusted; no chain
   of frames, so a journal can still be cut at a save.
3. **Aliases and defaults** in `lanes_data`: the first implementation PR proposes the syntax.
4. **Zero values.** None: an added `Option` field needs a declared default, as every added field
   does.
5. **Tails written by another version.** D66's old system stays in the binary; no "replay, save
   and exit" start for now.
6. **The default check on a manifest.** Refuse a tail when the application's version differs;
   when only Lanes' version differs, warn, and the application may make that strict.
7. **Decoded inputs (3.4)** supersede D44's one `Request` type in the journal, and land before the
   gate leaves the hot path.
8. **A journal in the model's terms.** Not now.
9. **Format 1 files** are refused with a message that names the format.
10. **Personal data in identities.** A note in the docs; no lint.
11. **Deadlines in the image** are data the model ignores, until the step context gives the model
    a clock (the decision on the step's shape).
