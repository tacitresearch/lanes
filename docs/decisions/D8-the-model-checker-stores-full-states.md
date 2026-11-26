# D8. The model checker stores full states

`Check.search` keeps every state and compares exactly, where Veil stores 63-bit fingerprints.

Why: state counts are then exact and comparable with TLC, and a hash collision cannot silently
drop states. Fingerprinting and parallel search come with the v2 engine, with an exact mode kept
for validation.
