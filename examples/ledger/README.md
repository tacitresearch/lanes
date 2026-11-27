# ledger

A multi-user double-entry ledger as a web application: users sign up and log in, open accounts
in a currency, move money between their own accounts and to other users' accounts, and see
their own accounts and the transfers that touch them; an administrator issues money and reads
the audit of every entry. It is phase D's stress test (`docs/ROADMAP.md`): its value is what it
found missing or broken in Lanes, which is the friction log at the end.

```bash
cd examples/ledger
mkdir -p .lake && ln -s ../../../.lake/packages .lake/packages   # share the fetched dependencies
lake build            # the system, the proofs, the server and the tests
lake test             # model checks and the bridge's tests, under a second
lake exe ledgerLive   # three users over HTTP, the server killed with SIGKILL and started again
lake exe ledger 8080 ledger.journal ledger.secrets admin   # serves http://127.0.0.1:8080
```

Sign up as `admin` first: the administrator is whoever holds that name, and its accounts are
the only ones that may go below zero, which is where money comes from.

## The spec

`Ledger/Spec.lean`, written before the actors. A `Service` whose state is, for each name, at
most one user (`Profile`: a credential, failed attempts, sessions) and one book
(`Ledger/Book.lean`: accounts and entries). One request at a time: the user it names decides it
(`User.decide`: sign up, log in, act with a live session), and what a logged-in user asks is
served by the book (`Book.serve`). A transfer is two entries, `-x` on the source and `+x` on the
destination, made in one step.

The safety properties are written over the book, as `Bool`s the checker evaluates and the
proofs state:

| Property | Definition |
| --- | --- |
| Money is conserved in each currency | `Book.conserved` |
| No account below zero unless it may be | `Book.noOverdraft` |
| The entries of a transfer sum to zero | `Book.paired` |
| Each balance is the sum of its account's entries | `Book.cached` |
| A reply to a user shows only that user's records (the audit aside) | `Reply.onlyOf` |
| Sessions and failed attempts stay within their bounds | `Auth.Sessions`, `Auth.Attempts.Bounded` |

Time passes in the spec as deadlines (`Deadline`): a locked account's lock lifting and a live
session ending, armed while the account is locked and the session live, read from the user's
record. The user's timers `unlock` and `expire` lift the lock or end the session in its record
and tell the ledger (`unlocked`, `ended`), and the ledger serving that notice is the deadline
passing (`Ledger.delivered`, `docs/decisions/D56-a-deadline-passes-where-it-is-served.md`), so
the checker sees a lock lift or a session end at that moment and holds the spec to it: before
the lock's deadline the account refuses even the right credential, and after a session's it
serves the session nothing. How long a lock or a session
lasts is the timer's delay (`Config.lockout_ms`, `session_ms`), which the semantics does not
model, so that is not checked.

## The actors, and why

One actor per user name (`user n`) and one actor for the book (`ledger`), in
`Ledger/System.lean`. A request goes to the user it names, which decides it and tells the
ledger either the reply or the operation to serve as that user; the ledger answers every
request.

- **The book is one actor** because a transfer between two users is atomic in the spec, and
  rule 3.6 leaves two ways to make an operation on two actors atomic: a protocol with locks, or
  one owner. The bank's design (debit here, credit in flight, credit there) is not linearizable:
  a view of the recipient asked after a view of the sender can miss money the sender has lost.
  With one owner the checker explores no interleaving inside a transfer, and every property of
  the book is a property of one actor, proved with the per-actor tools and lifted to every
  environment by `System.invariant_of_actor`. The kernel runs a step in well under a
  microsecond, so one actor is not the limit of a web front; the limit is that the whole book is
  one value (friction log).
- **A user is an actor** so that the credential, the counter of failures and the sessions of
  one user are decided in one place, journaled and checked, and so that a name is taken once
  by identity: `user n` is either vacant or not.
- **The ledger answers even what the user decided** (a refused log-in, a log-out, a request
  with no session). The link from `user n` to `ledger` is ordered, so the ledger sees each
  user's decisions in the order they were made, and every request takes effect, as the spec
  has it, when the ledger handles it. `Answering.fromUser` builds the system in which the user
  answers itself, and the checker finds its stale view in 42 steps: a log-out returns while a
  transfer of the same session is on its way, and a view asked afterwards misses it. The same
  run appears when the links reorder, so the design needs one shard or an ordered transport.
- **A deadline passes where requests are served.** The notice of a session's end goes to the
  ledger on the same ordered link as the user's decisions, so the ledger serves the requests the
  user decided while the session was live before the end, and those it decided after, which it
  refused, after it. A deadline that passed at the user's timer (`Ending.atUser`) let a view
  decided before a session's end be served after a payment asked after the end, and show it;
  the checker finds that run in 43 steps. A notice lost is a deadline that never passes though
  the user acted on it, so the links from the users to the ledger must lose nothing and the
  ledger must not crash on its own: the checker finds a lost end in 16 steps on a lossy link
  and in 17 with the ledger crashing. Deployed, the ledger and its users are one shard, which
  restarts whole from its journal.
- **The user id comes from the cookie.** The bridge verifies the session cookie, a signed
  token of the session id and the name, and makes `Request.act req name session op`; nothing in
  a request body names a user. The system then trusts no name either: `user n` serves its
  session's operations as `n` only, and that the ledger is asked to serve `n` only by `user n`
  is a theorem.

## What is checked

`Check.lean`, run by `lake test`, on two users (`0` the administrator, `1`), two accounts each,
two currencies, a right credential and a wrong one. Each scenario is a script of requests, each
sent once the requests it names are answered (`Driver.after`), the rest racing; every response
and every lock lifting or session ending is checked against the spec by the monitor and every
state against every property, with a `sometimes` witness for each case of interest. The seeded
lockout decides a log-in as if the account were open, though it counts the failures and arms
the lock's timer: the checker finds it when the session it opened ends, a deadline the spec
does not have armed.

| Scenario | States | Result |
| --- | --- | --- |
| Transfers between two users, racing, with views and the audit | 2,792 | pass |
| The same with any actor crashing once | 16,478 | pass |
| A log-out racing a transfer, then a view by the other user | 1,727 | pass |
| The same with a crash anywhere | 10,238 | pass |
| The same with requests lost and reordered on the way in and a crash anywhere | 12,264 | pass |
| Transfers between two users, with links to the ledger that lose messages | 3,904 | pass |
| The same, answered by the user actor | | stale view found in 42 steps |
| The same with links that reorder | | stale view found in 47 steps |
| Locks, evictions, a session used for another user, refusals | 199 | pass |
| The same with timers that fire at any moment (`ledgerCheck timed`, 19 s) | 108,105 | pass |
| The same with a user crashing anywhere (`ledgerCheck timed`, 75 s) | 527,757 | pass |
| The same with a lockout that does not lock | | found in 27 steps |
| A lock, then a session, with timers that fire at any moment | 71 | pass |
| A payment to `1` and a view by `1` racing the end of `1`'s session | 22,109 | pass |
| The same with a user crashing anywhere | 95,966 | pass |
| The same with the end at the user's timer (`Ending.atUser`) | | not the spec: found in 43 steps |
| The same with the ledger crashing | | a session's end lost: found in 17 steps |
| The same with links to the ledger that lose messages | | a session's end lost: found in 16 steps |

Also tested, without a socket: a session cookie makes an act of its user whatever the form
says; a cookie whose payload is changed does not verify; a form token of another session is
refused; a password enters the system only as its digest; a short password is refused before
it does; what enters the system holds no password and no cookie; and a session or a digest a
client sends in the headers `prepare` writes is dropped.

## What is proved

`Ledger/Proofs/`, for every configuration, every run and every environment model, with an
axiom gate:

- `book_invariant`: conservation in each currency, no overdraft, paired entries and cached
  balances, the properties the checker checks, as written there;
- `serve_onlyOf`: the ledger's reply to `n` shows only `n`'s records, unless it is the audit;
- `serve_from_owner`: every request on its way to the ledger to serve `n` was sent by
  `user n` (`System.Monotone`, five cases);
- `user_bounded`: at most `maxSessions` sessions, at most `maxFailures` failures counted, and
  locked at that many;
- `implements`: without timers (`Untimed`), the system implements its spec, for every
  configuration and every environment in which each user's link to the ledger is ordered and
  does not duplicate, and no request is handed to a user twice: messages may be lost on every
  link and reordered on the way in, and any actor may crash (`Ledger/Proofs/Refines.lean`, with
  `Lanes.Account`). A request takes effect when the ledger serves it; the user has decided it,
  and moved its record, before. So the witness of the simulation is the list of requests
  decided and not served, each marked with whether its message is still on the link, and the
  spec's record of a user, with that user's requests decided in order, is the user's record
  and the messages on its link to the ledger (`Lanes.linkMsgs`). A request whose message was
  lost, in a loss or a crash of the ledger, takes effect when the ledger serves the next
  message on the link if the user answered it, and never if the book was to serve it.
- `implements_timed`: with timers, the system implements its spec with its deadlines, each
  passing as the ledger serves the user's notice of it, for every configuration and every
  environment in which each user's link to the ledger is ordered and neither loses nor
  duplicates, no request is handed to a user twice and the ledger does not crash: requests may
  be lost and reordered on the way in, and users may crash (`Ledger/Proofs/Timed.lean`). The
  witness is what each user has decided and the ledger has not served, requests and deadlines
  alike, and the spec's record of a user, with those applied in order, is the user's record and
  the messages on its link. A timer that finds its deadline no longer armed tells nothing, so
  every notice the ledger serves is of a deadline armed in the spec.

The links from the users to the ledger must be ordered (a
reordering link gives a stale view, above). That libsodium's SHA-256, HMAC and comparison
compute what their Lean references do is tested, and that the references are SHA-256 and HMAC
is tested against published vectors (`TRUSTED.md`). Not proved: that the gate in front
(`Http.served`) keeps the refinement, and that a request is ever answered beyond what the
gate's own theorems say.

## The web front

`Ledger/Web.lean`. Pages are server-rendered with the template syntax; forms that change
something post with htmx and show their errors inline; the transfers page asks for its list
every three seconds and whenever a transfer of the user's is answered. Pages that need no
records (log-in, and the shells of the others, which carry the form tokens) are answered by
the bridge; the records come into them as fragments through the system.

- Passwords: Argon2id from libsodium, two passes over 19 MiB by default (OWASP's figure),
  salted with an HMAC of the name under a pepper of the deployment; a random salt per user is
  not possible here (friction log). The digest is computed by the bridge's `prepare`, on the
  request's own task, not on the shard's thread, and never again at a replay.
- Sessions: a cookie `ledger_session` holding an HMAC-signed token of the session id (the id of
  the log-in request, never reused) and the name; `HttpOnly`, `SameSite=Lax`, `Secure` behind
  TLS. The session itself lives in the user's actor: at most four, the oldest closed by a fifth
  log-in, each ended by log-out or after a day.
- Log-in attempts: five failures lock the account for five minutes; a locked account refuses
  even the right password.
- Forms: each carries a token that is an HMAC of the session's token, and must come from this
  origin (`Origin`, `Sec-Fetch-Site`). Bodies are limited to 4 KB.

## Friction log

What the ledger needed from Lanes, what was broken, and what was clumsy, concretely. The next
round of framework work is planned from this.

### Missing, and added

- **SHA-256, HMAC-SHA-256, PBKDF2**: `Lanes/Lib/Crypto/Sha256.lean`, `Lanes/Lib/Crypto/Hmac.lean`, pure
  Lean, Std only, tested against FIPS 180-4, RFC 4231 and RFC 7914 (`Tests/Crypto.lean`).
  Proved: digest and tag lengths, hex round trip, `Bytes.same a b = true ↔ a = b`. About 2 µs a
  block, so a PBKDF2 iteration is about 4 µs.
- **Cookies**: `Lanes/Web/Http/Cookie.lean`. Reading `Cookie` headers; `Set-Cookie` from a
  `Cookie` with every attribute named and safe defaults; a value that could add an attribute is
  not set. Also the origin check for forms, a per-route body limit and `Cache-Control:
  no-store`.
- **Signed tokens and form tokens**: `Lanes/Web/Auth/Token.lean`, with a purpose so that a session
  token is no form token; `Auth.verify_sign` proved.
- **Login state**: `Lanes/Web/Auth/Login.lean`: a password `Digest` whose `DecidableEq` compares in
  constant time (so `if c = stored` in a step leaks nothing), `Password.digest`, `Attempts`
  (failures that lock, `bounded_fail`), `Sessions` (bounded, the oldest closed).
- **Clients that wait**: `Driver.after` (`Lanes/Check/Clients.lean`). Neither `anyOrder` nor
  `script` gives real-time order, which is what makes a stale read a violation; it also keeps
  the state space small. Tested on the key-value store (`Tests/Clients.lean`).
- **A list lemma**: `Lanes.sum_map_set` in `Lanes/Proof/List/Basic.lean`.
- **Releasing idle actors**: an actor declares the states a start gives it (`Actor.fresh`), and
  the kernel drops one that is in such a state with no timers once it has handled a message,
  proved to change nothing anyone can see (`Kernel.exec_visible`,
  `docs/decisions/D51-release-actors-at-rest.md`). `user n` declares its vacant state, which a
  log-in for an unknown name leaves as it is, so twenty thousand guesses leave the kernel
  holding the ledger alone (`Release.lean`, checked when it is built).

### Broken

1. **The journal held passwords and session cookies in plain text. Fixed
   (`docs/decisions/D44-request-prepared-before-journal.md`).** `Http.serve`
   journalled the raw `(ReqId × Request)` the gate receives, so every log-in's form body and
   every request's `Cookie` header was on disk until a snapshot cut the journal, and a lawful
   codec cannot scrub them: its law is that what is read is what was written. The same placement
   made two more defects: the bridge's PBKDF2 ran inside the gate's step, on the shard's one
   thread, so every log-in stopped every other request for 84 ms; and a restart replayed every
   log-in since the last snapshot through PBKDF2 again. Now the server applies the pure
   `Bridge.prepare` to a request on the handler's task, before it has an id, and the system and
   its journal see only the prepared request. The ledger's `prepare` replaces the `password`
   field by its digest and the `Cookie` header by the name and session it verifies, and drops
   any header of those names a client sends; `ledgerLive` checks that the journal holds neither
   a password nor a session cookie.
2. Fixed (D38). `lanes_data` refused a constructor named by a keyword (`Op.open`, renamed
   `openAccount`) with a parse error at the constructor, and an argument named like its
   constructor (`ask (ask : Ask C)`) with `Invalid pattern: Not enough arguments to 'ask'`.
   Both are accepted now, and `UserMsg.ask` names its argument `ask` again. `Op.openAccount`
   keeps its name until `Ledger/Web.lean`, which builds it, can be edited.
3. Fixed (D38). `lanes_data` took no default field values, so `{}` built no `Attempts`,
   `Sessions` or `Book`, and each had a constant (`Attempts.none`, `Sessions.none`,
   `Book.empty`). It takes them now, and the constants are gone.
4. **With deadlines the system was not its spec. Fixed
   (`docs/decisions/D56-a-deadline-passes-where-it-is-served.md`).** A view that `user 1`
   decided while its session was live reached the ledger after a payment the administrator
   asked once the session had ended, and showed it: the spec puts the view before the
   session's end and the payment after (found in 43 steps). The user decided at one moment and
   the ledger served at a later one, and the deadline passed between them, at the user. Now a
   deadline may be the delivery of a message (`Event.timed`'s `delivered`), the user's timer
   tells the ledger, and the session ends as the ledger serves that notice, in order with the
   user's requests; the timed refinement is checked and proved (`implements_timed`).
5. `omega` did not close `e.account < b.accounts.length, ¬ k < b.accounts.length ⊢ ¬ e.account
   = k` where `k : AccountId` and `abbrev AccountId := Nat` (`Ledger/Proofs/Book.lean`,
   `openAccount_sound`); a term did.

### Clumsy

- ~~**A `Service` needs the system's signature**~~, though it reads only `In` and `Out`.
  Fixed: `Service In Out S` (`docs/decisions/D42-a-spec-names-its-inputs-and.md`), and `Ledger.spec` is in `Ledger/Spec.lean`, before the
  actors.
- ~~**A `Service` has no time.**~~ Lockouts and session ends could not be specified, so
  refinement was checked with them off and the timed system only against properties. Fixed: a
  `Service` has deadlines, and the timed system is checked against them (`docs/decisions/D42-a-spec-names-its-inputs-and.md`). What is still
  not checked is how long a lock or a session lasts.
- **The bridge's `encode` sees only the output.** Forms carry a token bound to the session, so
  only `decode`, which has the request, can render them; the system's replies render data
  without forms. The transfer form therefore cannot offer the user's accounts in a list, and an
  answer cannot choose between a redirect (plain form) and `HX-Redirect` (htmx), so
  `notLoggedIn` sends both. A gate that kept a little of the request with the pending id for
  `encode` would fix both.
- **`decode` returns `.error response` for pages it answers itself**: the log-in page and every
  page shell are the normal path, and are spelled as errors (`Ledger.Web.shell`).
- **htmx swaps only `2xx` answers**, so a form's inline error is a `200`; nothing in `Lanes.Hx`
  says so or helps.
- **Real-time order and state space.** The first version of the transfers scenario, with four
  requests from two users racing, did not finish in two minutes with the refinement monitor;
  two racing at a time take 2,792 states. Scripts must be mostly sequential, and the ones here
  were cut to fit.
- **No randomness in a step.** A session's id is the id of the request that opened it (unique
  because the server never reuses one), and a salt is derived from the name, because the
  digest has to be computed before the system sees the request.
- **Conservation across actors would not cover real names.** The bank proves conservation
  over a `Fintype` of accounts; `String` names are not one. With the book in one actor the
  question did not arise, but sharding the book needs sums over the actors that have started.
- **A user actor for every name ever tried.** A log-in for a name nobody has created the cell
  `user n`, and the runtime never released an actor, so a stranger could grow the kernel
  without bound by guessing names. Fixed (above): a vacant user is released. A user who signed
  up stays in memory for good, since releasing it needs its record saved elsewhere. The
  journal's name (`Main.lean`) should change with this, since the kernel now replays an old
  journal differently.
- **Unbounded state.** Entries grow forever (rule 2.6 has nothing to say to a ledger), accounts
  are a `List` looked up by index, every snapshot writes the whole book, and the transfers page
  lists every entry of the user.
- Fixed in Lanes (D38): **a subtype had no `lanes_data`**. `lanes_data` takes a field
  `{s : String // Name.valid s}` and derives its codec, and `Subtype` has `DecidableEq`,
  `Hashable` and `Repr`. `Name` (in `Ledger/Web.lean`) still has its instances and codec by
  hand until that file can be edited; declared as a structure with a proof field, as it is,
  `lanes_data` refuses it and says to use a subtype.
- **No HTTP client for tests.** `Live.lean` speaks HTTP over a socket with `Request.wire` and
  `Response.parse`, which are good, but each test of a server will write the same twenty lines.
- **Secrets on disk** are written with default permissions: Lean's `IO` has no `chmod`.
- **The origin of the pages** must be configured, since the bridge is built before the server
  knows its port, and a page reached as `localhost` instead of `127.0.0.1` fails the origin
  check.

### What the ledger would want next

- ~~**Background jobs**~~: added in Lanes as the jobs actor (`Lanes/Behaviours/Jobs/Basic.lean`): a
  job named by its requester's key, attempts that carry the key, retries after a backoff, a
  deadline per attempt and a bound on jobs in flight, with a pool of workers as its adapter and
  every job admitted proved answered in a fair run. The password's Argon2id stays in
  `Bridge.prepare`: what a job is asked is journalled, and a password must never be (D44);
  `prepare` already runs on the request's own task, off the shard's thread, once. Interest,
  statements, mail and ending sessions in bulk are jobs or timers when the ledger has them.
- **Server push**: the transfers page polls every three seconds; a stream of events per
  session (SSE first) as outputs the gate keeps open would let a transfer show the moment it
  is booked.
- **A database adapter**: the book outgrows memory and its snapshot; it wants entries by
  account as a derived index with a theorem tying it to the entries (rule 1.1), paged queries,
  and the actors of users who signed up released to storage when idle and read back on their
  next request.
- **A sharded book**: transfers across shards need locks or two-phase commit to stay
  linearizable; the checker already shows what goes wrong without them.

### What I would change in the API

1. `Bridge.prepare`, as above: the most important change, and a security one. Done
   (`docs/decisions/D44-request-prepared-before-journal.md`).
2. Let `encode` see what `decode` chose to keep of the request.
3. ~~`Service In Out S` over inputs and outputs alone, so a spec can come first.~~ Done (`docs/decisions/D42-a-spec-names-its-inputs-and.md`).
4. ~~Specs with time, or with internal steps, so sessions and lockouts can be specified.~~ Done:
   deadlines (`docs/decisions/D42-a-spec-names-its-inputs-and.md`).
5. A bridge result that says what it means: answered here, or entered as an input.
6. Sums over the actors a state has started, for invariants across actors with infinitely
   many identities.
