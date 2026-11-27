// Ops: parse (text in; the media type mime.ParseMediaType reads, its parameters, and
// mime.FormatMediaType of the two).
package main

import (
	"mime"

	"lanes/oracles/internal/cases"
)

func main() {
	cases.Run(func(op string, in []byte) (any, bool) {
		switch op {
		case "parse":
			t, params, err := mime.ParseMediaType(string(in))
			if err != nil {
				return nil, false
			}
			return map[string]any{"type": t, "params": params, "format": mime.FormatMediaType(t, params)}, true
		}
		panic("unknown op " + op)
	})
}
