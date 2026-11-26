# D44. A request is prepared before it is journalled

`Lanes/Http/Gate.lean` (`Bridge.prepare`), `Lanes/Env/Http.lean`, `systems/ledger/Ledger/Web.lean`.
The ledger found that `serve` journalled the request as it came: every log-in's password and
every session cookie was on disk in plain text until a snapshot cut the journal. A lawful codec
cannot scrub them, since what it reads back must be what was written. The bridge's PBKDF2 also
ran in the gate's step, on the shard's one thread (84 ms a log-in, during which nothing else is
served), and again for every log-in at a replay.

- *The shape.* `Bridge.prepare : Request → Request`, `id` unless the bridge says otherwise, is
  applied by the server to each request it reads, on that request's task, before the request
  has an id; what enters the shard, and so the journal, is the prepared request. A prepared
  request is still a `Request`, so the system, its signature, the journal's codec and every
  theorem about `served sys` and `fronted sys` are unchanged: they quantify over every input,
  so they hold of prepared ones for every bridge, `prepare` included. Splitting `decode` into an
  IO-side half that returns a typed value and a step-side half that reads it was the other
  shape. It would type the prepared form, but it makes the gate's message, the served system's
  input and the journal's codec depend on a type each bridge chooses, and it would let the IO
  side answer a request itself, which is the gate's decision. `prepare` cannot answer: what it
  finds wrong it writes down, and `decode` answers (the ledger writes `short` for a password
  too short to digest).
- *What is trusted.* That the server applies `prepare` to every request before it journals it is
  part of the trusted IO of `Lanes/Env/Http.lean` (`TRUSTED.md`), tested over a socket in
  `Tests/Web.lean`. That a given `prepare` removes what it should is the application's, and is
  pure: the ledger tests it without a socket and checks the journal of a live run.
- *A prepared request must not be forgeable.* What `prepare` writes, a client could send. The
  ledger's `prepare` drops every header of the names it writes before it writes them, and
  replaces the cookie by the name and session of a token that verifies; `decode` signs the token
  again from them (`sessionToken`), an HMAC, which is cheap, to check form tokens and draw
  pages. A digest a client sends instead of a password is dropped the same way.
- *Not done.* Work too slow for the shard that is not a function of one request, or that must be
  retried, still has no place: that is a job effect with a response message (the ledger's
  friction log).
