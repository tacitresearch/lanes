// Ops: clean (a path in; path.Clean of it), join (paths separated by NUL in; path.Join of
// them), match (a pattern, NUL, a name in; whether path.Match matches, or a refusal when it
// reports ErrBadPattern).
package main

import (
	"path"
	"strings"

	"lanes/oracles/internal/cases"
)

func main() {
	cases.Run(func(op string, in []byte) (any, bool) {
		switch op {
		case "clean":
			return path.Clean(string(in)), true
		case "join":
			return path.Join(strings.Split(string(in), "\x00")...), true
		case "match":
			pattern, name, found := strings.Cut(string(in), "\x00")
			if !found {
				return nil, false
			}
			matched, err := path.Match(pattern, name)
			if err != nil {
				return nil, false
			}
			return matched, true
		}
		panic("unknown op " + op)
	})
}
