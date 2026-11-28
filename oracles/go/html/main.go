// Ops: unescape (text in; html.UnescapeString of it).
package main

import (
	"html"

	"lanes/oracles/internal/cases"
)

func main() {
	cases.Run(func(op string, in []byte) (any, bool) {
		switch op {
		case "unescape":
			return html.UnescapeString(string(in)), true
		}
		panic("unknown op " + op)
	})
}
