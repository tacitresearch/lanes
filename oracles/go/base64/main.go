// Ops: encode-<name> (raw bytes in, text out) and decode-<name> (text in, hex out), for the
// strict forms of Go's four encodings.
package main

import (
	"encoding/base64"
	"encoding/hex"
	"strings"

	"lanes/oracles/internal/cases"
)

var encodings = map[string]*base64.Encoding{
	"std":    base64.StdEncoding.Strict(),
	"rawstd": base64.RawStdEncoding.Strict(),
	"url":    base64.URLEncoding.Strict(),
	"rawurl": base64.RawURLEncoding.Strict(),
}

func main() {
	cases.Run(func(op string, in []byte) (any, bool) {
		kind, name, _ := strings.Cut(op, "-")
		enc, found := encodings[name]
		if !found {
			panic("unknown op " + op)
		}
		switch kind {
		case "encode":
			return enc.EncodeToString(in), true
		case "decode":
			out, err := enc.DecodeString(string(in))
			if err != nil {
				return nil, false
			}
			return hex.EncodeToString(out), true
		}
		panic("unknown op " + op)
	})
}
