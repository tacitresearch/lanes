| Sign-in (`examples/sign-in/Videos.lean`) | The start of a video site: members sign in with Google or GitHub through Lanes' sign-in and get a session, signed out with a form token; what the bridge and the steps make of requests is tested without a socket | The same identity signing in again is the same member (`Videos.register_again`, `Videos.register_lookup`); the sign-in's own guarantees are Lanes' |

- Sessions are signed with a key made at start, so they end with the process, and the members
  are not journalled; neither the example nor its presets has been run against Google or GitHub.
