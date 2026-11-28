// Ops: parse-<boundary> (a body in; the parts mime/multipart's Reader reads with NextRawPart,
// each its header lines, names in lowercase, sorted, and its bytes in hexadecimal; refused when
// the reader returns an error before the end).
package main

import (
	"bytes"
	"encoding/hex"
	"errors"
	"io"
	"mime/multipart"
	"sort"
	"strings"

	"lanes/oracles/internal/cases"
)

func main() {
	cases.Run(func(op string, in []byte) (any, bool) {
		boundary, ok := strings.CutPrefix(op, "parse-")
		if !ok {
			panic("unknown op " + op)
		}
		r := multipart.NewReader(bytes.NewReader(in), boundary)
		parts := []any{}
		for {
			p, err := r.NextRawPart()
			if errors.Is(err, io.EOF) {
				return parts, true
			}
			if err != nil {
				return nil, false
			}
			body, err := io.ReadAll(p)
			if err != nil {
				return nil, false
			}
			headers := [][2]string{}
			for k, vs := range p.Header {
				for _, v := range vs {
					headers = append(headers, [2]string{strings.ToLower(k), v})
				}
			}
			sort.Slice(headers, func(i, j int) bool {
				if headers[i][0] != headers[j][0] {
					return headers[i][0] < headers[j][0]
				}
				return headers[i][1] < headers[j][1]
			})
			parts = append(parts, map[string]any{"headers": headers, "body": hex.EncodeToString(body)})
		}
	})
}
