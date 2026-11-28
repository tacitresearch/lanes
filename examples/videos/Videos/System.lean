/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Videos.Spec

/-!
# The site as an actor for each member, each beside its scheduler

Each member has an actor, named by the identity that signs in (`Who`), which holds the member's
`Site`, their channel and their videos, and runs the spec's own functions on it: an input is
`Site.handle`, a start `Site.recover`. An input goes to the actor of the member it is about
(`Input.member`): a request to the member who makes it, a report and the scheduler's word to
the owner of the video. So the work of two members touches no actor in common, but for a visit:
a like, a comment or the taking out of a comment, which the visitor's actor lets in by its
session and sends on to the owner's as a message (`Out.visit`). An actor given an input about
another member does nothing with it, so each holds only its own member's channel and videos
(`Videos.owned`).

Each member has a scheduler too (`Schedule.attachBy`), which holds the jobs of the member's
videos (`Key.owner`): the member's `schedule` and `cancel` go to it, and its word on each job
comes back as `Input.job`. Its attempts leave the system for the S3 client, whose answers come
back to it. The answers to requests and the objects given up on leave the system too.
-/

namespace Videos

open Lanes

abbrev sig : Signature where
  Id := Member
  Msg _ := Input
  In := Input
  Out := Out

/-- The member whose video a job is about. -/
def Key.video : Key → VideoId
  | .check v _ | .expire v | .delete v => v
  | .transcode r => r.video

def Key.owner (key : Key) : Member := key.video.owner

def Command.member : Command → Member
  | .signIn _ who _ => who
  | .signOut _ m _ | .create _ m .. | .uploaded _ m .. | .like _ m .. | .comment _ m ..
  | .uncomment _ m .. | .delete _ m .. | .retry _ m .. => m
  | .report _ r _ => r.round.video.owner

/-- The member whose actor takes an input. -/
def Input.member : Input → Member
  | .request c _ => c.member
  | .job key _ | .noticed key => key.owner
  | .visit v => v.video.owner

/-- What an output is to member `m`'s actor: a visit is a message to the owner's, and any other
output leaves. -/
def Out.effect (m : Member) : Out → Effect sig m
  | .visit to v => .send to (.visit v)
  | o => .emit o

/-- What member `m`'s actor does with an input: the spec's step, if the input is about `m`. -/
def handleAt (config : Config) (m : Member) (s : Site) (i : Input) : Site × List Out :=
  if i.member = m then s.handle config i else (s, [])

def site (config : Config) (m : Member) : sig.Actor m Site where
  init := {}
  step s i := let (s', outs) := handleAt config m s i; (s', outs.map (Out.effect m))
  recover s := let (s', outs) := s.recover; (s', outs.map (Out.effect m))

/-- The members alone. None is booted: each starts on its first input. -/
abbrev members (config : Config) : System sig where
  State _ := Site
  actor m := site config m
  accept i := ⟨i.member, i⟩

/-- How the site uses the scheduler. -/
def use : Schedule.Use sig Key Unit Answer where
  scheduled
    | .schedule now_ms spec => some (now_ms, spec)
    | _ => none
  cancelled
    | .cancel key => some key
    | _ => none
  notice key _ _ := .noticed key
  answer := .job

abbrev SchedIn := Schedule.Input Key Unit Answer
abbrev SchedOut := Schedule.Output Key Unit Answer
abbrev fullSig := joinSig (Schedule.sigBy Member Key Unit Answer) sig

/-- The members, each with its scheduler beside it: what runs. -/
abbrev system (config : Config) : System fullSig :=
  Schedule.attachBy (members config) config.scheduler use Key.owner

end Videos
