-- The items of the typed store's oracle (`Tests/Oracle/Service/Db.lean`).
CREATE TABLE lanes_items (
  id bigint NOT NULL PRIMARY KEY,
  tag text COLLATE "C" NOT NULL,
  owner bigint NOT NULL,
  data bytea,
  flag boolean
);
CREATE UNIQUE INDEX lanes_items_by_tag ON lanes_items (tag);
