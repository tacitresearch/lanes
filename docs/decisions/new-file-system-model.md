# D?. A file system that may lose power, as a platform model

Status: Accepted

`docs/decisions/D110-volatile-actors.md` puts platform models in core, the file system among
them, "with crash semantics (unsynced writes lost, torn writes, atomic rename)"; issue #245 lists
it as missing, with only a binding of `fsync` and `File.replace` in `Lanes/Lib/File.lean`. Almost
every program touches files, a file updated in place is a classic way to lose data in a crash,
and a SQLite driver or a Raft library will stand on this. This decision is that model, two
patterns proved on it, and the binding.

## The model

A file system is a value (`Fs`, `Lanes/Outside/FileSystem/Basic.lean`): every inode by number,
the root `0`. A file is what is on the disk for sure (`synced`) and the changes made since its
last `fsync` (`pending`), each a write at an offset or a truncation; an append is a write at the
end the file has when it is made. A directory is the same for its entries: each create, rename
or delete is a batch of entries set or removed at once. Paths are resolved through the entries.

The calls (`Op`) are read, write at an offset, append, create (or empty), truncate, mkdir,
rename, delete, list and `fsync`, which syncs a file's contents or a directory's entries, as the
system call does. `Fs.step` is what a call does and answers; a call the model refuses (`notFound`,
`isDir`, …) changes nothing.

**What a crash leaves** (`Fs.crash`, every outcome listed by `Fs.crashes`, proved complete by
`Fs.crash_mem_crashes` so a test can check them all). These are the model's assumptions, and
they are trusted (`TRUSTED.md`): Linux's ext4 gives them, with its default `data=ordered`, and
POSIX does not promise them.

- An `fsync` of a file puts its contents and size on the disk, and an `fsync` of a directory its
  entries; nothing else does, so a crash may lose anything not synced.
- Of a file's changes since its last `fsync`, a crash keeps the first few, in order, and may tear
  the next to any prefix of its bytes.
- Of a directory's changes since its last `fsync`, a crash keeps the first few, in order, each
  whole: a rename is atomic, and durable once its directory is synced; a file created in a
  directory not yet synced may vanish, contents and all.
- Directories do not keep each other's order.

**What an `io` error leaves** (`Fs.failures`): the call not made, made, or between. A write may
be done in part; a create, rename, delete or truncation is done or not. An `fsync` that failed
may leave the inode as a crash would, on the disk: Linux may drop the pages it could not write
and report it once, so a second `fsync` that succeeds proves nothing, and the model lets that
file be torn from then on.

The model is pure and imports nothing of Lanes, so it is homed in the lowest package
(`LanesCli/Layers.lean`): the standard library (`Lanes/Lib/File.lean`) and an application's
proofs use it without actors. As an outside (`FileSystem.server` in `Lanes/Outside/FileSystem.lean`,
through `Rpc.outside`) it takes effect when a call is sent, keeps every way the file system may
be with the answer each owes, adds `io` faults and a power loss as an event, each one switched
by `Faults`, and is a function of the calls without them (`FileSystem.server_same`).

## The patterns

Both are proved for a file whose directory, and every directory on the way to it, has nothing
a crash could lose (`SettledDir`), at every crash point and after an `io` error at any step that
stops the program there.

- **Atomic replace** (`Replace.plan`, `Lanes/Outside/FileSystem/Replace.lean`): unlink a
  temporary file an earlier crash left, create it, write the new bytes, `fsync` it, rename it over
  the target, `fsync` the directory. The file holds the old bytes or the new, never a mix
  (`Replace.crash`, `Replace.failed`); once done, the new ones through any crash, and the plan may
  run again (`Replace.done`). Unlinking the temporary file first means the plan never writes into
  an inode another name could share.
- **A durable append-only log** (`Log`, `Lanes/Outside/FileSystem/Log.lean`): appends and
  `fsync`s in any order. The log reads as a prefix of everything appended and holds everything
  appended before the last `fsync` (`Log.crash`, `Log.failed`). The last entry may be torn, so a
  reader frames entries with a length and a checksum.

## The binding

`FileSystem.IO.perform` (`Lanes/Outside/IO/FileSystem.lean`) makes each call with Lean's `IO.FS`
and reads an error back as the model's. Lean has no positional write, no append that does not
create the file, and no truncation to a size, so these are bound in `native/lanes.c` beside
`fsync`, which already syncs a directory as well as a file. The bytes are a `ByteArray` there and
a list in the model: `Op` takes the type of its bytes, the binding performs `Op.map
ByteArray.toList` of its call, and `Replace.plan_map` says the plan it runs is the plan proved.
`File.replace` is now `FileSystem.IO.replace`, which runs `Replace.plan` and stops at the first
error. Every `lake test` runs a script of calls, errors included, in a temporary directory and
checks each answer against the model's.

## Reach, cost and coupling

Reach: files, configuration, logs and caches are in most programs, and the two patterns are what
a journal, SQLite or Raft is built on. Cost: a pure model and its proofs, which a program that
does not import them does not build; about forty lines of C and one binding file, both trusted
and listed; `File.replace` now unlinks a temporary file first, one more system call. Coupling:
the model forces nothing on the core; the binding decides nothing.

Not modelled: links, permissions, file times, a full disk, other file systems' crash rules (XFS
may leave zeros where an append did not land; pages written in place may reach the disk in any
order), and writers in other processes.
