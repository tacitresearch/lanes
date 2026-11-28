# D?. Peers open every connection with a versioned handshake and a shared key

Status: Accepted

Peers talked plain TCP: a process took parcels from whoever connected, read them with the
positional codec, and had no way to tell a peer of another version, of another system, or
without the right to send. Issue #104 asked for a handshake before any deployment depends on
the wire format.

## What is decided

- **Each side writes a hello first**: the magic `LANESNET`, then frames holding the version of
  the handshake, the system's name (`Peers.Config.system`), the SHA-256 of a description of the
  message codecs (`Peers.Config.schema`) and a nonce of 32 random bytes. The magic comes first so
  that a stranger is named as one; the version is the first frame so that a hello of another
  version is known as one whatever its layout. Each side refuses a hello that differs, and the
  refusal names both sides' values. Both sides write before they read, so both refuse, and each
  says so in its own log.
- **Then each writes a proof**: `HMAC-SHA-256(key, role label ++ dialer's hello ++ acceptor's
  hello)`. A side is connected once the other's proof checks (`Peers.Handshake.Reachable.ready_proved`).
  The proof covers the checker's own nonce, so a recorded handshake does not check on a new
  connection, and it names its maker's role, so it cannot be sent back to its maker.
- **The decisions are a pure function**, `Peers.Handshake.step` (rule 3.9), and the handler
  performs it on each connection before the courier hears of it. The courier is unchanged: a
  connection it dialed is `connected` only after the handshake, and one it adopted carries
  parcels only after it.
- **The schema is a description the application writes**, until the codecs carry a schema of
  their own (#91). It is compared as a digest, so its text may be anything that changes when a
  message type does.
- **The key is at least 16 bytes**; `Peers.start` refuses a shorter one.

## What it does not do

The bytes after the handshake are neither signed nor encrypted: whoever can change bytes on the
network can change parcels. That is TLS between peers, later. A handshake has a deadline
(`Limits.handshake_ms`) and a bound on the hello (`Limits.helloBytes`).

## Alternatives

- **TLS with client certificates now.** It authenticates the stream and hides it, but needs a
  TLS server, which Lanes does not have, and certificates to manage. The handshake's format and
  its version leave room for it.
- **A MAC on every parcel.** It authenticates the stream without TLS, and changes the courier's
  framing and its proofs. Not needed for a first step.
- **A one-sided check** (the acceptor checks the dialer only). A dialer would then send parcels
  to whatever listens on a peer's port.
