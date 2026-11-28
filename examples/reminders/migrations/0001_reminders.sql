-- The reminders, a jobs table as `Reminders.schema` declares it (`Lanes/Db/Jobs.lean`).
CREATE TABLE reminders (
  id bigint NOT NULL PRIMARY KEY,
  key text COLLATE "C" NOT NULL,
  work text COLLATE "C" NOT NULL,
  due_ms bigint NOT NULL,
  status bigint NOT NULL,
  attempts bigint NOT NULL,
  lease bigint NOT NULL,
  every_ms bigint NOT NULL,
  note text COLLATE "C" NOT NULL
);
CREATE UNIQUE INDEX reminders_by_key ON reminders (key);
CREATE INDEX reminders_by_due ON reminders (status, due_ms);
