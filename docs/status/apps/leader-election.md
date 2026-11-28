### Leader election

Where: `examples/election/Election.lean`.

Checked:

- A split-brain bug found.
- At most one leader per term on 3 nodes with reordering and a crash (165k states).

Proved:

- At most one leader per term for any number of nodes and terms under every environment model: loss, duplication, reordering, crashes (`examples/election/Election/Proofs.lean`).
