# D54. Raft acts once on a command its client names, and an answer it no longer keeps is not handed over

Status: Accepted

`examples/raft-kv/RaftKV/Once.lean`, `examples/raft-kv/RaftKVProofs/Once.lean`,
`examples/raft-kv/RaftKVProofs.lean`, `examples/raft-kv/Check.lean`, `Lanes/Semantics/Once.lean`.
`RaftKV.implementsMachine` holds in every environment whose links from clients do not hand a
request to a node twice. A client retries, and a retry is that. D48 gave the answer for the
key-value store, `Service.once`, and named the place for Raft: the replicated machine. This
takes it: `RaftKV.implementsMachine_once` has no premise on the environment.

- *The memo is in the machine.* A command is `Named Cl C`: its client, the client's number for
  it, and the command. `Machine.once machine Cl` keeps `Once.Memo` beside the machine's state,
  one entry per client (rule 2.6, as in D48): a fresh number is acted on, the last one again is
  answered as before, an older one gets `none`. The memo is replicated with the state, so an
  entry a leader appended twice, from a retry or a link that repeats, takes effect once and is
  answered twice. The protocol and every proof in `RaftKV/Proofs/` are generic over the machine
  and are used as they are.
- *An answer is named as its command.* A node answers an entry with the `req` of the request it
  took, and a retry through another node may carry another `req`, which the machine never sees.
  So the spec, `named N Cl machine`, answers with the client, the number and the result
  (`Named Cl R`), and the cluster's answer is read from its result. `req` stays what a node
  matches answers to its own waiters by.
- *An answer the memo no longer keeps is hidden, not allowed.* A node answers every entry it
  took when it applies it, so a command overtaken by a later one of its client is answered,
  with `none`. No state of `once` allows an answer to a command that may never have taken
  effect. Changing the protocol was refused (it is frozen and generic), and so was letting
  `once` allow an empty answer to any request that arrived, which would weaken the spec that
  the key-value store is proved against too. The empty answer is hidden: `onceCluster` is the
  cluster behind `System.filterMapIO id Response.res`. `System.Refines.filterMapIO` carries a
  refinement through such a filter: what a system refines with the hidden outputs allowed at
  any time (`Spec.showing`, a step that changes nothing), the system behind the filter refines
  without them. It is forty lines on `SysState.step_under`. A front end that serves the cluster
  would answer such a request as superseded, which says nothing of its effect.
- *Membership, not counting.* `OnceSim` keeps `Logged`, the committed list of
  `RaftKV/Proofs/Applied.lean`, and replaces the multisets of `RaftKVProofs/Refines.lean` by
  sets: every request in flight to a node has arrived, the request of every entry in a log or
  an `append` in flight has arrived, the machine run over the list is the spec's value and a
  memo that agrees with the keys taken (`Once.Memo.Agrees`), and every answer along the list and
  every answer waiting is empty or given. There is no `Finset` of live entries, no sum of
  answers owed over nodes and no `FromClients`: the duplicate case is the delivery case
  (`System.Refines.of_handles`). It is 457 lines; `Refines.lean` is 552.
- *Checked first.* `Check.lean`, on three nodes, one client, one key and two values: with links
  from clients repeating and reordering, the cluster refines `once` of the named map, an answer
  is waiting twice and a command overtaken by a later one is applied; a write sent again through
  another node takes effect once; and the map spec without `once` is broken by an answer handed
  over twice. Among the deep checks, links from clients losing, reordering and repeating with a
  crash (189,686 states). Every link of `Link.network` with a crash is more than the ten
  million states the checker stores.
- *The standard simulation is not used.* `Account` (D52) bounds the spec's pending requests and
  outbox by multisets and concludes `Implements` of `Service.spec`; `once` is membership
  against `Service.once`, with no counts to bound.
  `System.traced` would replace `FromClients`, which this proof does not need, and `linkMsgs`
  reads ordered links, which membership ignores. `OnceSim` and `Once.Server.Sim` have the same
  shape, requests held have arrived and answers held are given; an `Account` for `once` would
  be that, and waits for a third proof.
- *What stays.* `RaftKV.implementsMachine` and its premise are unchanged, for the machine
  without the memo; the check outside that premise still shows the premise is needed there.
