// Ops: inflate, gunzip, zlib (a compressed stream in; the bytes compress/flate, compress/gzip
// or compress/zlib read from it, in hexadecimal, refused on an error or past 1 MiB).
package main

import (
	"bytes"
	"compress/flate"
	"compress/gzip"
	"compress/zlib"
	"encoding/hex"
	"io"

	"lanes/oracles/internal/cases"
)

const max = 1 << 20

func main() {
	cases.Run(func(op string, in []byte) (any, bool) {
		var r io.Reader
		switch op {
		case "inflate":
			r = flate.NewReader(bytes.NewReader(in))
		case "gunzip":
			z, err := gzip.NewReader(bytes.NewReader(in))
			if err != nil {
				return nil, false
			}
			r = z
		case "zlib":
			z, err := zlib.NewReader(bytes.NewReader(in))
			if err != nil {
				return nil, false
			}
			r = z
		default:
			panic("unknown op " + op)
		}
		out, err := io.ReadAll(io.LimitReader(r, max+1))
		if err != nil || len(out) > max {
			return nil, false
		}
		return hex.EncodeToString(out), true
	})
}
