// Op: parse (the bytes of a document in, its value out). A number is written as the string
// "num:<m>e-<e>", the value m / 10^e with e as small as it can be, or "num:unbounded" when its
// exponent is beyond ±100000, and a string as "s:" and its text, so that the two sides compare
// values, not spellings.
package main

import (
	"bytes"
	"encoding/json"
	"io"
	"math/big"
	"strconv"
	"strings"

	"lanes/oracle/internal/cases"
)

func number(n json.Number) string {
	text := string(n)
	if i := strings.IndexAny(text, "eE"); i >= 0 {
		e, err := strconv.Atoi(strings.TrimPrefix(text[i+1:], "+"))
		if err != nil || e > 100000 || e < -100000 {
			return "num:unbounded"
		}
	}
	r, ok := new(big.Rat).SetString(text)
	if !ok {
		return "num:unbounded"
	}
	ten := big.NewInt(10)
	e := 0
	for !r.IsInt() {
		r.Mul(r, new(big.Rat).SetInt(ten))
		e++
	}
	return "num:" + r.Num().String() + "e-" + big.NewInt(int64(e)).String()
}

func canonical(v any) any {
	switch v := v.(type) {
	case map[string]any:
		out := make(map[string]any, len(v))
		for k, x := range v {
			out[k] = canonical(x)
		}
		return out
	case []any:
		out := make([]any, len(v))
		for i, x := range v {
			out[i] = canonical(x)
		}
		return out
	case json.Number:
		return number(v)
	case string:
		return "s:" + v
	default:
		return v
	}
}

func main() {
	cases.Run(func(op string, in []byte) (any, bool) {
		if op != "parse" {
			panic("unknown op " + op)
		}
		if !json.Valid(in) {
			return nil, false
		}
		decoder := json.NewDecoder(bytes.NewReader(in))
		decoder.UseNumber()
		var v any
		if err := decoder.Decode(&v); err != nil {
			return nil, false
		}
		var rest any
		if err := decoder.Decode(&rest); err != io.EOF {
			return nil, false
		}
		return canonical(v), true
	})
}
