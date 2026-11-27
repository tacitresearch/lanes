// Op: parse (an address in, as RFC 5322 §3.4 writes one). net/mail's ParseAddress reads it; the
// answer is its addr-spec and its display name.
package main

import (
	"net/mail"

	"lanes/oracles/internal/cases"
)

type address struct {
	Address string `json:"address"`
	Name    string `json:"name"`
}

func main() {
	cases.Run(func(op string, in []byte) (any, bool) {
		if op != "parse" {
			panic("unknown op " + op)
		}
		a, err := mail.ParseAddress(string(in))
		if err != nil {
			return nil, false
		}
		return address{Address: a.Address, Name: a.Name}, true
	})
}
