# D?. Connecting to managed PostgreSQL as libpq does, and signing with a role's credentials

Status: Accepted

PostgreSQL is the default store and AWS the deploy target (`docs/decisions/D111-typed-store.md`,
`docs/decisions/D74-aws-integration.md`), so the client must connect to a managed database the
way its operators already configure libpq, and an application on AWS must run without a
long-lived key. Issue #109 had put the password file's permissions, `PGSERVICE` and
`root.crt` (C2) and credentials from IO for signing (C12) later; the owner took them up.

## PostgreSQL: libpq's sources and names, stricter where libpq is lax

`Postgres.Settings.read` takes an option from the connection string an application gives (a
`postgresql://` URI or `keyword=value` pairs), else from the service that string or `PGSERVICE`
names, else from libpq's variable, else from a deploy's (`LANES_DB_*`), else libpq's default.
The service before the variables is libpq's order (`conninfo_add_defaults`). The readers of
strings and service files follow libpq 16's code, and libpq itself is their oracle
(`oracles/libpq`): agreement is measured, not argued.

Where libpq warns and goes on, the client refuses, because it has no channel for a warning and
a warning nobody reads is a silent fallback (rule 3.1):

- A password file that others may read, or that is not a plain file, is an error; libpq skips
  it with a warning. Lean's `IO.FS.Metadata` has no mode, so the IO reads it from `stat`'s
  output; a binding of `stat(2)` beside `fsync` in `native/lanes.c` would replace that.
- An option libpq knows and the client does not support is an error naming it, but for the
  few that change nothing here (TCP keepalives, `gssencmode` short of `require`, `sslsni=1`,
  `client_encoding=UTF8`), so that a service file shared with `psql` still works.
- `connect_timeout` of zero, libpq's "forever", is the client's own deadline (rule 3.4).
- `sslrootcert` defaults to `~/.postgresql/root.crt` when it is there, as in libpq, then to the
  deploy's bundle, then to the system's authorities; libpq would fail without the file.

Several hosts are tried in order, each with its line of the password file, and
`target_session_attrs` asks each server reached one query, as libpq asks servers older than 14.
Reach was weighed against cost (rule 1.8): a cluster endpoint of RDS or Aurora is one name and
needs none of this, but self-managed failover does, and the cost is a loop in the IO and a
pure judgement of one reply.

Not taken: Unix sockets, client certificates, `hostaddr`, GSSAPI, `load_balance_hosts`,
`require_auth` and replication connections, each of which needs a transport or an
authentication the client does not have; and `DATABASE_URL`, which libpq does not read: an
application passes it to `Client.fromEnv` itself.

## AWS: the SDKs' chain, and what is signed ends with its credentials

`Aws.Imds.chain` looks where AWS's SDKs look, in their order: keys in the environment, a
container's endpoint, the instance's metadata service unless `AWS_EC2_METADATA_DISABLED`.
Profiles, SSO and STS are left out: they are for people at a terminal, or need a signed call
to STS, and an application on EC2 or ECS needs none of them.

S3 refuses a request signed with credentials that have expired, and a presigned link or a
form is such a request made later. So `SigV4.Source` gives each credential's expiry, and
`S3.presignNow` and `S3.Post.formNow` sign for the time asked or until the credentials
expire, whichever is sooner (`S3.expiryWithin_le`): a link says when it ends, rather than
failing early. Fetching a role's credentials earlier does not lengthen this: the metadata
service gives the same credentials until it rotates them.

A bridge is pure and is given its credentials once, so an application that signs in its
bridge still needs a key that does not expire. Giving a bridge a value read in IO at each
answer is a change to the server, left to issue #188.
