"""A real client against a Lanes server, for `Tests/WebSocket.lean`'s live test.

Connects to `ws://127.0.0.1:<port>/chat` with websockets' own client, which checks the server's
handshake, pings and the close handshake as RFC 6455 says, says `py`, reads it back from the
room, sends a message long enough to come back in fragments, and closes. Prints `ok` when all
of that went as it should, else what did not.
"""

import sys

from websockets.sync.client import connect


def main(port):
    with connect(f"ws://127.0.0.1:{port}/chat", open_timeout=5, close_timeout=5) as ws:
        ws.send("py")
        if ws.recv(timeout=5) != "py":
            return "the room did not send back what was said"
        ws.ping(b"p").wait(timeout=5)
        long = "z" * 300000
        ws.send(long)
        if ws.recv(timeout=5) != long:
            return "a long message did not come back whole"
    if ws.close_code != 1000:
        return f"closed with {ws.close_code}"
    return "ok"


if __name__ == "__main__":
    print(main(int(sys.argv[1])))
