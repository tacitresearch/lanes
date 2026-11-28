### Videos

Where: `examples/videos`, a package of its own.

Lanes' V1 acceptance application: a video site whose members sign in with Google or GitHub, upload from the browser to S3 with a form whose signed policy bounds the size (2 GiB by default), and watch, like, comment and delete.

Checked:

- A pipeline: a confirmed upload is given to a transcode worker outside the site (`Lanes.Transcode`, a JSON job over HTTP and a signed webhook back), and the video is ready only once the worker reports, signed, a playable rendition and a thumbnail, which its page plays and shows; a failed transcode is shown to its owner with a retry.
- Bounds on one member's videos and comments far below the site's, so that one member cannot fill them.
- Model-checked beside the worker's and the object store's models with their timeouts, late, repeated and forged reports and crashes, four seeded bugs found (the browser's word taken for an upload, a timed-out check taken as found, sessions that never end, a report taken unsigned).
- One actor that runs the spec's functions, on `Http.serveFronted` with a journal and snapshots, its calls to the store and the worker jobs of the scheduler beside it (`Lanes.Schedule`), retried with a backoff, kept on the journal and bounded by `maxJobs`: a check, the last check of an upload a day after it was begun, which confirms it or takes it out, the start of a round of a transcode, and the delete of a deleted video's objects, reported if given up.
- Public, unlisted and private videos, a feed by pages, channels.
- Tested over HTTP against the test kit's fake S3, worker, provider and browser (`Lanes.Testing`) through a restart on the journal.

Proved:

- A deleted video never shown again, and a video shown only after the scheduler said a check of it succeeded with `found`, which it says only of the store's answer, and after the worker reported it done with its signature, in every run of the spec's functions (`Videos.Site.deleted_never_served`, `Videos.Site.listed_confirmed`, `Videos.Site.listed_transcoded`, `Schedule.succeeded_replied`).
- A private video shown only to its owner in every run of the system (`Videos.private_to_owner`), and only in answer to a session of the owner's that let the request in when it arrived (`Videos.Site.handle_private`).
- A report changes only the video it names (`Videos.Site.report_names`), and in a fair run a report the worker signed is handled and ends its round, ready or failed (`Videos.report_settles`).
- Each like counted once in every reachable state (`Videos.likes_distinct`).
- The scheduler within `maxJobs` (`Videos.jobs_bounded`), and every job ending in a fair run in which it does not crash (`Videos.job_ends`).

Not proved yet:

- That a deleted video's object is deleted or reported, and that the worker reports, so that a confirmed upload ends ready or failed (checked, with no crash).
- The bridge (tested).
- The proved properties of the spec's functions as statements about the system's traces.

Known limits:

- Not run against AWS or a real provider; `videosLive` runs the flow against a bucket the environment names. Links handed out before a delete last until they expire. Every page view is journalled. No search or mail (its README). No worker that speaks the transcode format but the test kit's, and a round under way has no deadline. A journal of before the pipeline (`videos 2`) is refused, not upgraded.
