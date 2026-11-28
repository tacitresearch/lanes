### Added

- A proposal, for the owner to decide (`docs/decisions/D98-proof-surface.md`): a small, named proof surface with the semantics' bodies hidden and every module experimental unless marked stable; each property written once as a `Prop`, with its check derived through `Decidable`; a standard check that every input is answered once nothing is enabled, and `System.ImplementsLive`; specs that may answer "unavailable" or "may have taken effect"; named sets of environment assumptions shared with the runtime contract; and timers' delays as an opt-in constraint on runs. No code changes.
