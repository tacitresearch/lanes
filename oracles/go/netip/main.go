// Ops: parse (text in, Addr.String out), print (4 or 16 bytes in, Addr.String out), prefix
// (text in, Prefix.String and Masked().String out) and contains ("<prefix> <addr>" in, a bool).
package main

import (
	"net/netip"
	"strings"

	"lanes/oracles/internal/cases"
)

func main() {
	cases.Run(func(op string, in []byte) (any, bool) {
		switch op {
		case "parse":
			a, err := netip.ParseAddr(string(in))
			if err != nil {
				return nil, false
			}
			return a.String(), true
		case "print":
			a, ok := netip.AddrFromSlice(in)
			if !ok {
				return nil, false
			}
			return a.String(), true
		case "prefix":
			p, err := netip.ParsePrefix(string(in))
			if err != nil {
				return nil, false
			}
			return map[string]string{"text": p.String(), "masked": p.Masked().String()}, true
		case "contains":
			ps, as, found := strings.Cut(string(in), " ")
			if !found {
				return nil, false
			}
			p, err := netip.ParsePrefix(ps)
			if err != nil {
				return nil, false
			}
			a, err := netip.ParseAddr(as)
			if err != nil {
				return nil, false
			}
			return p.Contains(a), true
		}
		panic("unknown op " + op)
	})
}
