/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Videos.Proofs.Shows
import Videos.Proofs.Run
import Videos.Proofs.Gone
import Videos.Proofs.Confirmed
import Videos.Proofs.Likes
import Videos.Proofs.Private
import Videos.Proofs.Jobs
import Videos.Proofs.Ready
import Videos.Proofs.Members
import Videos.Proofs.Reads
import Videos.Proofs.Axioms

/-!
# What is proved

For every configuration (the seeded bugs off where it matters) and every site, input, start of
a member's actor and read (`Shows`, `Run`), and so for every run of the spec's functions and
every read of the members' sites (`Gone`, `Confirmed`), every run of the members beside their
schedulers under every environment model (`Members`, `Likes`, `Private`, `Jobs`), and every
fair run of them (`Jobs`, `Ready`), and every view (`Reads`). The README lists each claim with
its theorem.
-/
