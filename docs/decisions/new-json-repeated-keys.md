# D?. A JSON key given twice keeps its last value

The parser refused an object that gave a key twice. RFC 8259 allows such a text (its names
"SHOULD be unique"), JSONTestSuite counts `{"a":"b","a":"c"}` as valid (`y_object_duplicated_key`),
and Go's `encoding/json` and JavaScript's `JSON.parse` keep the last value. The parser now builds
every object with `Json.mkObj`, which sorts the fields by key and keeps the last of a repeated key
(`Json.getObjVal?_mkObj`), so the value it returns for a text is `Json.normalize` of the text's
meaning, and `Json.parse_iff` states exactly what it accepts.

The parser has no mode that refuses them. That matters where a second reader of the same text
keeps the first value instead; `Json.mkObj?` still refuses a repeated key when a value is built.

**Against Go** (`Tests/Oracle/Json.lean`, `oracle/json/`, D50), on 100,000 cases at seed 0:
94,608 agree, 5,392 known, none other. Values are compared, not spellings: a number as its
value in lowest terms, so `1.50` and `15e-1` agree. Where we depart from Go:

- *Unpaired surrogates.* Go reads `"\ud800"` as U+FFFD. Ours refuses it: the escape stands for
  no character, and a reader that replaces it changes the text it was given.
- *Invalid UTF-8.* Go reads bytes and replaces invalid ones with U+FFFD. Ours reads a `String`,
  which is UTF-8 by its type; an adapter refuses other bytes before the parser sees them.
- *Limits.* Ours refuses more than `maxDigits` digits (1000 by default), an exponent beyond
  `±maxDigits`, and nesting beyond `maxDepth` (128); Go has a nesting limit of 10,000 and no
  limit on numbers.
