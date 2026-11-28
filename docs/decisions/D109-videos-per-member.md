# D109. The video site split into an actor per member, and a scheduler per entity

Status: Partly superseded by new-volatile-actors.md (the video site, which leaves the main branch, and the waves it was split for)

`Lanes/Behaviours/Schedule/Basic.lean`, `Lanes/Behaviours/Schedule/Sound.lean`,
`Lanes/Semantics/Schedule.lean`, `Lanes/Runtime/Batch.lean`, `Lanes/Web/Http/View.lean`,
`examples/videos/Videos/Spec.lean`, `examples/videos/Videos/System.lean`,
`examples/videos/Videos/Web.lean`, `examples/videos/Videos/Proofs/`,
`examples/videos/Videos/Check.lean`, `examples/videos/Videos/Waves.lean`. Issue #106, the
scheduler per entity and the split of the video site. D107 measured, on a projection, that the
work of the video site spreads over many actors a wave only when every hot path is partitioned;
D108 made reads from the state. This builds the split D107 projected, but for one step, and
measures it.

## What changed

- **A scheduler per entity.** `Schedule.attachBy sys config use owner` is `Schedule.attach` with
  a scheduler for each entity of a type `E`: `Schedule.systemBy` routes each scheduling, cancel
  and reply to the scheduler of `owner key`, and each scheduler runs the scheduler's own actor.
  What one scheduler proves, each does: it holds at most `maxJobs` jobs and no key twice
  (`Schedule.attachBy_within`), its timers are armed while it is up (`Schedule.armedBy`), and in
  a fair run in which it does not crash every job it holds that is not periodic ends
  (`Schedule.attachBy_held_leaves`, by `System.LeadsTo.join_left` from
  `Schedule.held_leavesBy`). The proofs of the step are the scheduler's, unchanged; those about
  runs are the single scheduler's, with the scheduler's id a variable.
- **A read over every member.** A peek takes, beside its ids, a predicate (`every`), and reads
  the states of every actor the kernel has started that the predicate holds of
  (`Batch.Peek.others`). An actor the predicate holds of that is not among them was never
  started and has its initial state (`Batch.Peek.init_of_not_others`); each state among them is
  that actor's in the kernel read (`Batch.Peek.others_of`), and over the whole history in the
  world the semantics reaches (`Batch.chain_peek_after`). `Http.View` has `every`, and its
  `answer` is given the others. The feed needs it: its actors are not known from the request.
- **Actors named by the identity that signs in.** A member is `Who`, the issuer and the subject
  the provider vouched for, and is the id of the member's actor and scheduler. A sign-in goes to
  that actor: no actor is asked who is who. A video is `VideoId`, its owner and a number the
  owner gives, so a video's actor is in its id and no number is given twice. Links carry them as
  path segments (`Web.whoPath`, `Web.videoPath`), the session cookie as its payload.
- **The site split.** Each member's actor holds the member's `Site`, their channel and videos,
  and runs `Site.handle` and `Site.recover` on it: the spec's functions, as before, now of one
  member. An input goes to the member it is about (`Input.member`): a request to whoever makes
  it, a report and a job's word to the video's owner. A like, a comment and the taking out of a
  comment are let in by the visitor's actor, by its session, and sent on to the owner's as a
  `Visit`, which holds the video and its likes and comments. An actor given an input about
  another member does nothing with it (`handleAt`).
- **Reads over the members' sites.** The feed, watch pages and channel pages are a `Read` of the
  spec, `Site.read`, of the members' sites put together (`Site.union`, which takes from each site
  only its member's channel and videos). A watch page reads the owner's actor and the viewer's,
  a channel page the channel's member's and the viewer's, and the feed every member's actor
  started. They are no command: the bridge answers them only through `Web.view`. The feed is
  newest first by when each video was made, then by id (`Cursor`), since ids are no longer one
  sequence.

## What is proved, and how the claims changed

Every claim the site proved is proved again. Where the old argument was "one atomic owner",
the claim is stated for the split system.

- **No output of the system shows a video** (`Site.quiet_handle`): only reads do. So
  `Videos.private_to_owner` holds of every run as before, and what was proved of the outputs that
  show videos is now proved of reads.
- **Private videos.** A read shows a private video only in answer to a session of its owner
  that the owner's site lets in at the read's time (`Site.read_private`); a read sees each
  member's sessions in that member's site only.
- **A deleted video is never served again** (`Site.deleted_never_served`): once a delete is
  answered, no later output of the owner's actor shows the video, and no read of the owner's
  site after it, beside any other members' sites, does. The delete is one step of the owner's
  actor, and a read sees the owner's site at one boundary between entries
  (`Batch.run_peeks`), so the video leaves the feed, its channel page and its watch page at the
  same boundary: the one after the delete's entry. This is the "one step" D107 said the split
  would lose; it holds of reads at boundaries because the owner holds the record every read
  needs.
- **Shown only once confirmed and transcoded** (`Site.listed_confirmed`,
  `Site.listed_transcoded`): a read of the sites of members' runs shows a video only if the run
  of the site it is in has the scheduler's `found` for its upload and the worker's signed report.
- **Likes** are held by the video's owner, so `Videos.likes_distinct` holds of every member's
  site in every reachable state, and `count_distinct` as before.
- **Jobs**: each member's scheduler holds at most `maxJobs` and no key twice
  (`Videos.jobs_bounded`), and every job ends in a fair run in which that scheduler does not
  crash (`Videos.job_ends`). Every key of a member's video goes to that member's scheduler by
  `Schedule.systemBy`'s routing, so no other scheduler is given it; that one key is never held by
  two schedulers is that routing, not a theorem.
- **Reports**: `Videos.report_settles` is about the actor of the owner of the round's video.
- **Views** (`Videos.Web.view_answers`): from any kernel of the shard, the view's response is
  the spec's read of the sites of the members it reads, each that actor's state in the kernel,
  and for the feed every member's actor not read has the empty site.

## What is no longer true

- **The number of members is not bounded.** `maxMembers` is gone: no actor counts the members,
  since that actor would be asked at every first sign-in. A member's own state is bounded as
  before; the kernel holds an actor and a scheduler for every member who signed in. The site's
  `maxVideos` and the scheduler's `maxJobs` are each member's.
- **A read over several members is not a quiet point.** A like let in by the liker's actor and
  not yet taken by the owner's is not seen by a read at that boundary: the read answers as if the
  like came after it. A read never sees half a step of one actor.
- **A comment shows its author's name as it was when it was written**: the author's actor puts
  it in the visit, and the owner's keeps it.
- **A sign-in names its member by what the provider says.** An identity whose issuer or subject
  is empty, `.` or `..`, or has a line break, cannot sign in (`Name.valid`).

## The numbers

`lake exe videosWaves`, on the real split, with the workload, the generator and the counting of
D107 (20,000 entries and reads, of which 6,805 entries: reads are not journalled). Entries per
wave, beside D107's projection of this layout, "the same, members named by their identity", in
which likes and comments are the owner's, as here:

| Views | Batch | Measured | D107's projection | 2+ | 8+ |
| --- | --- | --- | --- | --- | --- |
| By popularity | 64 | 11.38 | 11.17 | 98.8% | 81.2% |
| By popularity | 256 | 15.43 | 15.36 | 98.0% | 90.3% |
| Uniform | 64 | 12.72 | 12.33 | 98.9% | 84.5% |
| Uniform | 256 | 35.08 | 35.07 | 99.7% | 97.6% |

The actor most entries touch: with views by popularity, the owner of the most popular video, in
6.4% of the entries (D107: 6.3%); uniform, a member in 0.6%. So the projection holds. The small
differences are the protocol's: a visit is the visitor's actor, then the owner's, where the
projection counted the same two actors; a scheduler is touched by a member's jobs only.

D107's last layout, likes and comments held by whoever makes them (12.77 and 41.74 by
popularity), is not built: a like would then be one actor, but every watch page and every card
of the feed a read over every member to count its likes.

## Checked

`Videos.Check` runs the system's own actors, named by two members (`Check.checked`): the checker
enumerates the actors, and a member is any identity, so the check maps the two members it has
to the system's actors and sends no message to one it has not; the scripts name no other. Each
read of a scenario is judged at every state, which is every boundary a read may fall at, not at
one point of the script: no private video to another, nothing after its delete was answered,
nothing the store or the worker did not first confirm, no session past its lifetime. In the
checks the actors are started with the system, which a start of an empty site does
not change; in the small scenarios the actor and scheduler of `a` crash, `b` taking part only in visits
and reads; the large ones crash every actor their scenario uses. The small bounds take about
25 seconds; `lake test` in `examples/videos` about 30.

## What remains

- Likes and comments held by whoever makes them, which D107 measures at 12.77 and 41.74 per wave:
  it needs a count over every member that a read of every member gives (the feed's), or an index
  view tied to the members' states by a theorem.
- A bound on the members, if one is needed: an actor told once per new member, at its first
  sign-in only.
- The theorem that turns a run of the system into the runs of the spec its members' actors
  performed is not written, as before.
