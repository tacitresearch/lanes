### Key-value store

Where: `examples/kv-cache/KV.lean`.

Checked:

- A client that retries an old write gets one effect, behind `Once.actor`; without the memo that retry takes effect again and a read duplicated to the store is answered with two values.
- A stale-read bug of a read cache found, with one front end already.
- Refines the map spec on one key, two values and two front ends, also with links that lose and reorder messages and a crash; a duplicating link breaks it, whichever of the three it uses.
- With the store behind `Once.actor` (`onceSystem`) it refines `once` of the map spec with every link duplicating, and with every link losing, reordering and duplicating and a crash.

Proved:

- Behind `Once.actor` it implements `once` of the map spec in every environment, with no assumption on links or crashes (`KV.implements_once`; all in `examples/kv-cache/KV/Proofs.lean`).
- With caching it does not, in any environment, for any instance with a key, a value and a front end: the checker's run replays in every one (by the standard simulation `Lanes.Account`).
- Without caching it implements the map spec for all keys, values and front ends in every environment whose links do not duplicate.
