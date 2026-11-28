# D107. The waves' premise, measured on the video site: the work spreads once reads leave the journal

Status: Partly superseded by new-volatile-actors.md (waves as the default: it stands as a measurement)

`Lanes/Runtime/WavePlan.lean`, `examples/videos/Videos/Waves.lean`, `examples/videos/Waves.lean`.
D96 makes waves the default runtime only if real applications spread their work over many
actors, and asks first that `examples/videos` be split into one actor per user to see whether it
does. This measures how wide the waves of the site's journal would be, as the site runs and under
several splits, before the split is built.

## How it is measured

- *The conflict rule.* Two journal entries conflict when they touch an actor in common; an entry
  touches every actor that one of its messages reaches before the kernel is quiet again.
  `WavePlan.split` puts each entry of a batch in the earliest wave after every earlier entry it
  conflicts with. The entries of a wave touch no actor in common (`WavePlan.disjoint_of_split`),
  and each actor's entries are in waves in the journal's order (`WavePlan.levels_lt`). This is
  stricter than the kernel's waves (`Kernel.mail`), which take each message on its own.
- *The workload.* `lake exe videosWaves` runs the real system on a kernel: a thousand members
  sign in, videos are made, checked, transcoded and reported, and then 20,000 entries are logged
  of the mix `Videos.Waves.Mix` gives: views most, then likes, the feed, channel pages, comments,
  sign-ins, uploads and deletes, with the store's and the worker's answers as entries a few
  entries after their call. Views pick videos by popularity, about `1 / (rank + 1)`, or
  uniformly. The generator is fixed, so the numbers below are what the program prints until the
  site, the mix or the layouts change.
- *The splits are projected, not built.* Each unit of work of the run is mapped to the actors it
  would touch in the split (`Split.touches`): a member's own request goes to their actor; a
  request about another member's video to the viewer's actor, which checks the session, and then
  to the owner's; a job's word to the owner of the video its key names. A `catalog` holds who is
  which member and the feed's cards, told of every change to a listed card (a like, a delete, a
  video made ready). The flags of `Split` take these away one at a time: a scheduler per member,
  reads (watches, the feed, channel pages) answered from the state and not journalled, the feed
  read from the members' states instead of the catalog, member actors named by the identity
  that signs in, and likes and comments held by the member who makes them.

## The numbers

Views by popularity. "Per wave" is the mean entries in a wave, the speedup a batch could have
with a core for each; "2+" and "8+" are the shares of entries in waves of at least two and at
least eight, for batches of 64 (D88's wave).

| Layout | Entries | Per wave, batch 64 | Per wave, batch 256 | 2+ | 8+ | The actor most entries touch |
| --- | --- | --- | --- | --- | --- | --- |
| As it runs: the site beside the scheduler | 20,000 | 1.00 | 1.00 | 0.0% | 0.0% | the site, 100% |
| By member, a catalog, one scheduler | 20,000 | 3.71 | 3.74 | 86.8% | 53.7% | the catalog, 26.4% |
| The same, a scheduler per member | 20,000 | 3.76 | 3.78 | 84.9% | 57.4% | the catalog, 26.4% |
| By member, a catalog, one scheduler, reads from state | 6,804 | 2.09 | 2.12 | 76.6% | 24.5% | the catalog, 44.2% |
| The same, a scheduler per member | 6,804 | 2.25 | 2.26 | 68.2% | 35.4% | the catalog, 44.2% |
| A scheduler per member, reads and the feed from state | 6,804 | 6.94 | 7.18 | 94.3% | 71.1% | the catalog (sign-in), 13.9% |
| The same, members named by their identity | 6,804 | 11.17 | 15.36 | 98.8% | 79.0% | the owner of the most popular video, 6.3% |
| The same, likes and comments held by who makes them | 6,804 | 12.77 | 41.74 | 99.4% | 79.1% | one member, 0.4% |

Views uniform, entries per wave for batches of 64 and 256, in the same order: 1.00 and 1.00;
3.69 and 3.71; 3.74 and 3.74; 2.06 and 2.09; 2.20 and 2.21; 7.07 and 7.18; 12.33 and 35.07;
12.77 and 41.74.

## What they mean

- **As it runs, waves give nothing.** Every entry is the site's actor's, so every wave is one
  entry. Waves as the default do not speed up an application of one actor.
- **A split by member alone gives about four.** Whatever is shared bounds the waves: a batch
  has at least as many waves as entries that touch its busiest actor. Here that is the
  catalog, which a quarter of the entries touch: every feed, every sign-in, every like of a
  public video.
- **Reads from state alone make it worse while the catalog is an actor.** Without the reads,
  two thirds of the entries go, and what is left is writes, more of which touch the catalog and
  the scheduler.
- **The work spreads when every hot path is partitioned.** With the reads, the feed's among
  them, answered from the members' states, a scheduler per member and member actors named by
  their identity, waves are eleven to fifteen wide with popular videos and twelve to thirty-five
  with uniform views. Then two limits are left. An upload is four entries in a row on its
  member's actor (uploaded, the check's answer, the job's, the report), so a batch has at least
  about five waves. And the owner of a popular video takes its likes: one member in sixteen
  entries, which bounds a batch of 256 at about sixteen wide. Likes held by the members who make
  them, their count a read over the members, remove that.

So the premise holds for an application partitioned all the way, and not for one with a shared
index or a shared scheduler. The guidance D96 leaves to this test follows: an actor per entity,
and no actor that most writes touch, so no index told of every change, no directory asked at
every sign-in and no single scheduler. What it changes in the order of #106:

1. **Reads from state, over several actors, before the split.** The feed is a read over every
   member; journalled, it touches every member or an index actor that every like must tell.
   Splitting videos before such reads exist buys about four, and its proofs (one atomic owner
   today) would have to be redone again when the feed moves.
2. **A scheduler per entity.** `Schedule.attach` gives one scheduler actor, which every upload
   and every delete touches several times. The site's jobs are keyed by video (`Videos.Key`),
   so they can be held beside the video's owner.
3. **Actors named by what names them outside.** A sign-in that asks a directory for the member's
   number puts every sign-in on one actor; an actor named by the identity needs no directory.
4. **Then split videos,** with the claims proved again over the split: a delete no longer
   vanishes from the feed and the watch page in one step, so `Videos.Site.deleted_never_served`
   becomes a claim about reads at batch boundaries.
5. **Waves as the default** keeps its place after these. For an application of one actor they
   change nothing that can be observed (`Kernel.runWaves_eq`), `Pace` keeps cheap work on the
   shard's thread, and they give nothing.

## Not measured

Time. The widths say how many cores a batch could use, not that steps are costly enough to gain
from them (D73, D88 measure that). The kernel's waves take each message on its own, not each
entry whole with every actor its messages reach; how their widths compare with these is not
measured. Nor is a split with videos as actors of their own.
