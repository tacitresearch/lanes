### Watchdog

Where: `examples/watchdog/Watchdog.lean`.

Checked:

- Under the fair scheduler a dog whose keeper keeps pinging never barks, and one whose keeper rests barks.

Proved:

- In every run that fires each timer that stays pending, it barks (`examples/watchdog/Watchdog/Proofs.lean`).
- There is a fair run in which the keeper pings forever, the dog's timer is pending at every position and the dog never barks.
