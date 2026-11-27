/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Tests.TutorialWeb.Files

/-!
Step 5 of `docs/TUTORIAL-WEB.md`: the model check of the shelf, run on the shelf and on the shelf
with the step's bug.
-/

namespace Tests.TutorialWeb

open Lanes Shelf

instance : sig.Inspect := {}
instance (svc : Service sig.In sig.Out State) : (Server.system svc).Inspect := {}

def requests : List Request :=
  [.begin 1 "alice" 0, .seen 2 "alice" 0 (some 5), .delete 3 "bob" 0, .delete 4 "alice" 0,
    .begin 5 "alice" 0]

/-- The bug the tutorial seeds: a delete takes the file off whoever asks. -/
def buggy (config : Config) : Service sig.In sig.Out State where
  init := {}
  step s
    | .delete req _ file =>
      ({ s with uploads := s.uploads.filter (·.id != file) }, [⟨req, .deleted file⟩])
    | r => (service config).step s r

def report (service : Config → Service sig.In sig.Out State) :=
  Check.system (Server.system (service { maxFiles := 1 }))
    { driver := Driver.anyOrder requests
      env := { mayCrash := fun _ => true }
      maxCrashes := 1 }
    [ .always "the shelf holds at most one upload" fun w => (w.state.state ()).uploads.length ≤ 1,
      .sometimes "the shelf is full" fun w => w.state.outbox.any (·.answer == .full),
      .sometimes "a file is listed" fun w => (w.state.state ()).uploads.any (·.size.isSome),
      .always "only its uploader deletes a file" fun w =>
        (w.state.state ()).holds "alice" 0 || (w.state.state ()).next == 0
          || !w.driver.contains (.delete 4 "alice" 0),
      .sometimes "a file is deleted" fun w =>
        (w.state.state ()).next == 1 && !(w.state.state ()).holds "alice" 0 ]

end Tests.TutorialWeb
