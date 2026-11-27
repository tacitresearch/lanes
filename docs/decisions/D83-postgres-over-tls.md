# D83. PostgreSQL over TLS, with channel binding, and a pool of connections

D68 left TLS, channel binding and a pool out of the PostgreSQL client, and D70's stack turned off
`rds.force_ssl` because of it: the database's traffic crossed the VPC in the clear, and SCRAM
proved that the server knew the password but not that it was the server meant. D67 has since
given a TLS client (`native/tls.c`, `Lanes/Web/IO/Tls.lean`) that does no IO, so it sits under
any socket. This decision puts it under the PostgreSQL connection, binds SCRAM to the server's
certificate, and adds a bounded pool. It amends D68's "Out of scope" and D70's database.

## TLS: what is decided where

PostgreSQL asks for TLS inside its own protocol: the client sends `SSLRequest` (a length of 8
and the code 80877103), the server answers one byte, `S` or `N`, and on `S` the TLS handshake
runs on the same socket, and the protocol starts again inside it. PostgreSQL 17 also takes TLS
at once (`sslnegotiation=direct`), with the ALPN protocol `postgresql`.

The pure connection decides all of it (rule 3.9). `Conn.Config.encryption` is `plain`,
`negotiated` or `direct`; `Conn.start` sends `SSLRequest` or asks for TLS at once (`startTls`),
and the phases `sslRequest` and `handshake` come before `startup`. The IO runs the handshake
when asked, through `Tls.Session`, and tells the connection `secured` (with the certificate's
hash for channel binding and the ALPN protocol the server chose) or `insecure` (with OpenSSL's
reason); from then on it sends and receives through the session. What the connection then
promises, proved for every configuration and every sequence of events:

- with TLS, nothing leaves before the IO says the handshake is done but `SSLRequest`: not the
  start-up, not a password, not a request (`Conn.tls_first`, from `Conn.step_beforeTls` and
  `Conn.run_beforeTls`);
- `N` closes the connection (`Conn.step_refusedTls`); there is no `prefer`, which would go on in
  the clear when an attacker answers `N`;
- the handshake starts only on an `S` alone (`Conn.step_startTls`): bytes after the `S` were
  written before the handshake, in the clear, and are refused, as libpq refuses them since
  CVE-2021-23222;
- after the handshake the start-up is sent only if the server chose ALPN `postgresql` with
  direct TLS, or `postgresql` or nothing otherwise (`Conn.step_secured`), so that a server of
  another protocol that holds a certificate for the name is not spoken to.

The client's modes (`Client.Config.sslmode`) are `disable`, `require` and `verifyFull`, the
default. `verifyFull` is D67's session: the certificate must chain to `trust` and be for
`serverName` (or the address called). `require` checks the chain only, as libpq's `verify-ca`
does (libpq's `require` checks nothing, which this client never does); for it `native/tls.c`
takes a flag that leaves out the name check, and `Tls.Session.startChain` is the only way to
set it, so D67's "there is no way to turn it off" now holds for `Tls.Session.start` and the HTTP
client, not for the TLS client as a whole. `serverName` exists because the client still takes
an IPv4 address and RDS's certificate is for the endpoint's name. Direct TLS is
`Client.Config.direct`; ALPN cost two OpenSSL calls (`SSL_set_alpn_protos`,
`SSL_get0_alpn_selected`), and the HTTP client offers none.

## Channel binding

SCRAM-SHA-256-PLUS (RFC 5802, RFC 7677) with `tls-server-end-point` (RFC 5929 §4.1) puts the
hash of the server's certificate into the client's last message, under the proof. A party in
the middle that holds a certificate the client accepts (one from an authority of a large bundle,
or any from the authority under `require`) and relays to the real server has the client bind its
own certificate, which the real server does not have, and the server refuses the proof.

- The certificate comes from OpenSSL as DER (`SSL_get1_peer_certificate`, `i2d_X509`, five lines
  of C). Which hash is pure Lean (`Lanes/Lib/Crypto/Certificate.lean`): the outer
  `signatureAlgorithm` of the DER is read, and SHA-256, SHA-384 or SHA-512 is the one it names,
  SHA-256 for MD5 and SHA-1, and none for RSASSA-PSS, Ed25519 or SHA-224, as libpq has none.
  SHA-384 and SHA-512 are pure Lean (`Lanes/Lib/Crypto/Sha512.lean`, tested against NIST's
  examples and `openssl dgst`); libsodium has no SHA-384, and RDS's RSA4096 and ECC384
  authorities sign with SHA-384.
- `Conn.Config.channelBinding` is `require`, `prefer` (the default) or `disable`. `Conn.choose`
  decides: with TLS, a hash, and the server offering `SCRAM-SHA-256-PLUS`, it binds; with TLS
  and no offer, `prefer` sends the GS2 flag `y`, which a server that did offer refuses, so a
  relay that hides the offer is seen; without TLS, or with no hash, `n`; `require` refuses all
  but a binding. Proved: a binding is to the hash the handshake gave and with `require` there
  is one, over every run (`Conn.run_bound`, from `Conn.choose_endPoint` and
  `Conn.choose_require`), and the client's last message carries `c=` the GS2 header and that
  hash in base 64 (`Conn.onMessage_binds`, `Scram.respond_binds`, `Scram.Binding.data_endPoint`).
- RFC 7677 has no vector for `-PLUS`; the messages are tested against Python's `hashlib`
  computing RFC 5802 for a fixed hash, and live: PostgreSQL 16 accepts the binding with a
  certificate signed with SHA-384, and refuses it, as it refuses libpq's, through a relay with
  another certificate from the same authority (`Tests/PostgresTls.lean`).

## A pool

`Postgres.Pool` hands connections to clients. The policy is pure (`Lanes/Lib/Postgres/Pool.lean`):
at most `max` connections open or being opened (`Pool.run_size`) and `waiting_max` clients
waiting (`Pool.run_waiting`), a full queue refused at once, a connection opened only for a client
that no connection being opened will serve, and each failure to open one refusing the oldest
client waiting, so that a server that is down is not asked once per retry. A connection handed
back is reusable only when it is open, idle outside a transaction and has nothing in flight
(`Conn.reusable`, pure); otherwise it is closed and never handed out again (`Pool.never_again`),
given the premise that the IO never reports a connection opened under a number it used before,
which it keeps by drawing every number from one counter. The IO (`Lanes/Lib/Postgres/IO/Pool.lean`)
opens, closes, keeps clients waiting on promises and tells the policy when a client's deadline
passed; the policy, not the timer, says whether that client was answered first. An idle
connection is not watched: one that broke there is found when used, handed back not reusable,
and replaced. `Store.handler` still opens a connection per transaction.

## RDS

The stack sets `rds.force_ssl` to 1. The instance fetches RDS's global bundle,
`https://truststore.pki.rds.amazonaws.com/global/global-bundle.pem`, at setup and at each
`configure`, refuses it unless its SHA-256 is the stack's `DatabaseCaBundleSha256`, and installs
it as `/etc/lanes/db-ca.pem` (`LANES_DB_CA`); the application connects with `verifyFull` to the
endpoint's name (`LANES_DB_HOST`) and `channelBinding := .require` (`docs/DEPLOY.md`). Pinning the
hash means an AWS change to the bundle stops `configure` until the parameter is updated, which
is the point: what the application trusts changes only when someone looked. The bundle holds
about a hundred authorities, every region's, any of which can then sign for the endpoint's
name; a regional bundle is smaller and could replace it.

## Trusted

`native/tls.c` grows by `lanes_tls_peer`, `lanes_tls_alpn`, the ALPN offer and the flag of
`require`, with their OpenSSL functions declared and checked by `scripts/tls-declarations.py`.
`Lanes/Lib/Postgres/IO/Client.lean` runs the handshake, tells `secured` only once it is done,
and from then on sends and receives through the session only; `Lanes/Lib/Postgres/IO/Pool.lean`
performs the pool's actions. The rest is proved or tested.

## Not done

Names are not resolved: the client takes an IPv4 address and a `serverName`. TLS client
certificates (`sslcert`), CRLs and OCSP;
`tls-exporter` binding (RFC 9266), which PostgreSQL does not offer; a pool that watches idle
connections, ends them after an idle time or checks one with a query before handing it out;
`Store.handler` on the pool. Direct TLS is tested against `openssl s_server` only, since the
PostgreSQL here is 16.
