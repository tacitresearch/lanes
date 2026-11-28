-- The to-dos, as `TodoDb.schema` declares them. Uniqueness by title is not a constraint: it is
-- the invariant every transaction keeps (`TodoDb.preserves`).
CREATE TABLE todos (
  id bigint NOT NULL PRIMARY KEY,
  owner bigint NOT NULL,
  title text COLLATE "C" NOT NULL,
  done boolean NOT NULL
);
CREATE INDEX todos_by_title ON todos (owner, title);
