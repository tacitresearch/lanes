// Ops: read, read-semicolon, read-tab (text in; the records encoding/csv reads with that
// delimiter and any number of fields per record, or a refusal).
package main

import (
	"encoding/csv"
	"strings"

	"lanes/oracles/internal/cases"
)

func read(in []byte, comma rune) (any, bool) {
	r := csv.NewReader(strings.NewReader(string(in)))
	r.Comma = comma
	r.FieldsPerRecord = -1
	records, err := r.ReadAll()
	if err != nil {
		return nil, false
	}
	if records == nil {
		records = [][]string{}
	}
	return records, true
}

func main() {
	cases.Run(func(op string, in []byte) (any, bool) {
		switch op {
		case "read":
			return read(in, ',')
		case "read-semicolon":
			return read(in, ';')
		case "read-tab":
			return read(in, '\t')
		}
		panic("unknown op " + op)
	})
}
