/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Videos.Spec

/-!
# The site as an actor, beside the scheduler

One actor holds the whole `Site` and runs the spec's own functions: an input is
`Site.handle`, a start `Site.recover`. Why one actor: every claim is about one atomic owner (a
delete must vanish from the feed, the channel and the watch page at once; a like counts each
member once), as in `examples/rookery`.

The scheduler (`Lanes.Schedule`) is beside it (`Schedule.attach`): the site's `schedule` and
`cancel` go to it, and its word on each job comes back as `Input.job`. Its attempts leave the
system for the S3 client, whose answers come back to it. The answers to requests and the objects
given up on leave the system too.
-/

namespace Videos

open Lanes

abbrev sig : Signature where
  Id := Unit
  Msg _ := Input
  In := Input
  Out := Out

def site (config : Config) : sig.Actor () Site where
  init := {}
  step s i := let (s', outs) := s.handle config i; (s', outs.map .emit)
  recover s := let (s', outs) := s.recover; (s', outs.map .emit)

/-- The site alone. -/
abbrev alone (config : Config) : System sig where
  State _ := Site
  actor _ := site config
  accept i := ⟨(), i⟩
  boot := [()]

/-- How the site uses the scheduler. -/
def use : Schedule.Use sig Key Unit StoreAnswer where
  scheduled
    | .schedule now_ms spec => some (now_ms, spec)
    | _ => none
  cancelled
    | .cancel key => some key
    | _ => none
  notice key _ _ := .noticed key
  answer := .job

abbrev SchedIn := Schedule.Input Key Unit StoreAnswer
abbrev SchedOut := Schedule.Output Key Unit StoreAnswer
abbrev fullSig := joinSig (Schedule.sig Key Unit StoreAnswer) sig

/-- The site with the scheduler beside it: what runs. -/
abbrev system (config : Config) : System fullSig :=
  Schedule.attach (alone config) config.scheduler use

end Videos
