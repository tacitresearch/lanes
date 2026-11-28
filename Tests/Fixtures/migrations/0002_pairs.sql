-- A column added, an index and a table with a key of two columns.
ALTER TABLE lanes_items ADD COLUMN note text COLLATE "C";
CREATE INDEX lanes_items_by_owner ON lanes_items (owner, tag);

CREATE TABLE lanes_pairs (
  a bigint NOT NULL,
  b text COLLATE "C" NOT NULL,
  v bigint,
  PRIMARY KEY (a, b)
);
