/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Videos.Spec

/-!
# The site as an actor

One actor holds the whole `Site` and runs the spec's own functions: an input is
`Site.handle`, a start `Site.recover`. Its outputs are the spec's: answers to requests, calls to
the store, and objects given up on. Why one actor: every claim is about one atomic owner (a
delete must vanish from the feed, the channel and the watch page at once; a like counts each
member once), as in `examples/rookery`.
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
  recover s := let (s', outs) := s.recover config; (s', outs.map .emit)

abbrev system (config : Config) : System sig where
  State _ := Site
  actor _ := site config
  accept i := ⟨(), i⟩
  boot := [()]

end Videos
