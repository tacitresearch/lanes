# D?. A JSON key given twice keeps its last value

The parser refused an object that gave a key twice. RFC 8259 allows such a text (its names
"SHOULD be unique"), JSONTestSuite counts `{"a":"b","a":"c"}` as valid (`y_object_duplicated_key`),
and Go's `encoding/json` and JavaScript's `JSON.parse` keep the last value. The parser now builds
every object with `Json.mkObj`, which sorts the fields by key and keeps the last of a repeated key
(`Json.getObjVal?_mkObj`), so the value it returns for a text is `Json.normalize` of the text's
meaning, and `Json.parse_iff` states exactly what it accepts.

The parser has no mode that refuses them. That matters where a second reader of the same text
keeps the first value instead; `Json.mkObj?` still refuses a repeated key when a value is built.
