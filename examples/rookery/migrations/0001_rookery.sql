-- rookery's tables, as `Rookery.schema` declares them. Run once, at the start, by
-- `Postgres.Typed.prepare`, which then refuses to start if the tables are not the declared ones.
CREATE TABLE members (
  name text COLLATE "C" NOT NULL PRIMARY KEY,
  hash text COLLATE "C" NOT NULL,
  bot boolean NOT NULL,
  token bigint NOT NULL,
  last_seq bigint NOT NULL,
  locked_at_s bigint NOT NULL
);
CREATE TABLE posts (
  author text COLLATE "C" NOT NULL,
  id bigint NOT NULL,
  body text COLLATE "C" NOT NULL,
  posted_s bigint NOT NULL,
  PRIMARY KEY (author, id)
);
CREATE TABLE follows (
  follower text COLLATE "C" NOT NULL,
  followee text COLLATE "C" NOT NULL,
  PRIMARY KEY (follower, followee)
);
CREATE TABLE windows (
  name text COLLATE "C" NOT NULL PRIMARY KEY,
  start_s bigint NOT NULL,
  count bigint NOT NULL
);
CREATE TABLE counters (
  name text COLLATE "C" NOT NULL PRIMARY KEY,
  next bigint NOT NULL
);
-- The API changes acted on (`Lanes.Db.Keys`): at most one a member.
CREATE TABLE api_keys (
  key text COLLATE "C" NOT NULL PRIMARY KEY,
  answer text COLLATE "C" NOT NULL
);
-- Failed log-ins and open sessions (`Lanes/Web/Auth/Rows.lean`).
CREATE TABLE login_attempts (
  "user" text COLLATE "C" NOT NULL PRIMARY KEY,
  failures bigint NOT NULL,
  locked boolean NOT NULL
);
CREATE TABLE sessions (
  id bigint NOT NULL PRIMARY KEY,
  "user" text COLLATE "C" NOT NULL,
  started_s bigint NOT NULL,
  used_s bigint NOT NULL
);
CREATE INDEX sessions_by_user ON sessions ("user");
