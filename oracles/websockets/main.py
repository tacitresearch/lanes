"""A WebSocket server's side as the websockets library's Sans-I/O protocol runs it, for
`Tests/Oracle/WebSocket.lean`.

Reads the cases `lanesOracle` writes, one JSON object per line ({"id", "op", "in": hex}), and
answers one per line ({"id", "ok", "out"}). Op: server. The input is the bytes a client sends
after the opening handshake. A `ServerProtocol` with `max_size` 1024 takes RFC 6455's example
handshake, accepts it, then the input. The answer is the messages its frames make, put together
from their fragments (a text's bytes in hex, marked when they are not UTF-8, which the Sans-I/O
layer leaves to the layer above), the payloads of the pongs it sends, and the code of the close
it sends: a number, -1 for a close with no code, or null for none.
"""

import json
import sys

from websockets.frames import Opcode
from websockets.server import ServerProtocol

MAX_SIZE = 1024

HANDSHAKE = (
    b"GET /chat HTTP/1.1\r\nHost: server.example.com\r\nUpgrade: websocket\r\n"
    b"Connection: Upgrade\r\nSec-WebSocket-Key: dGhlIHNhbXBsZSBub25jZQ==\r\n"
    b"Sec-WebSocket-Version: 13\r\n\r\n"
)


def frames_sent(data):
    """The frames of a server's bytes, which are not masked: (opcode, payload)."""
    out = []
    i = 0
    while i + 2 <= len(data):
        opcode = data[i] & 0x0F
        n = data[i + 1] & 0x7F
        i += 2
        if n == 126:
            n = int.from_bytes(data[i:i + 2], "big")
            i += 2
        elif n == 127:
            n = int.from_bytes(data[i:i + 8], "big")
            i += 8
        out.append((opcode, data[i:i + n]))
        i += n
    return out


def message(kind, data):
    if kind == "text":
        try:
            data.decode("utf-8")
        except UnicodeDecodeError:
            return ["text-invalid", data.hex()]
    return [kind, data.hex()]


def server(data):
    protocol = ServerProtocol(max_size=MAX_SIZE)
    protocol.receive_data(HANDSHAKE)
    [request] = protocol.events_received()
    protocol.send_response(protocol.accept(request))
    protocol.data_to_send()
    protocol.receive_data(data)
    messages = []
    current = None
    for frame in protocol.events_received():
        if frame.opcode in (Opcode.TEXT, Opcode.BINARY):
            kind = "text" if frame.opcode is Opcode.TEXT else "binary"
            if frame.fin:
                messages.append(message(kind, frame.data))
            else:
                current = (kind, frame.data)
        elif frame.opcode is Opcode.CONT and current is not None:
            current = (current[0], current[1] + frame.data)
            if frame.fin:
                messages.append(message(*current))
                current = None
    pongs = []
    close = None
    for opcode, payload in frames_sent(b"".join(protocol.data_to_send())):
        if opcode == 0xA:
            pongs.append(payload.hex())
        elif opcode == 0x8:
            close = int.from_bytes(payload[:2], "big") if len(payload) >= 2 else -1
    return {"messages": messages, "pongs": pongs, "close": close}


def main():
    out = sys.stdout
    with open(sys.argv[1], encoding="utf-8") as cases:
        for line in cases:
            if not line.strip():
                continue
            c = json.loads(line)
            if c["op"] != "server":
                raise SystemExit("unknown op " + c["op"])
            answer = {"id": c["id"], "ok": True, "out": server(bytes.fromhex(c["in"]))}
            out.write(json.dumps(answer) + "\n")


if __name__ == "__main__":
    main()
