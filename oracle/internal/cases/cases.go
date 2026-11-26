// Package cases reads the cases `lanesOracle` writes, one JSON object per line
// ({"id": 7, "op": "decode-std", "in": "<hex>"}), and prints one answer per line
// ({"id": 7, "ok": true, "out": ...}, or "ok": false when Go refuses the input).
package cases

import (
	"bufio"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"io"
	"os"
)

type Case struct {
	ID int    `json:"id"`
	Op string `json:"op"`
	In string `json:"in"`
}

type Answer struct {
	ID  int  `json:"id"`
	OK  bool `json:"ok"`
	Out any  `json:"out,omitempty"`
}

// Run answers every case in the file named by the first argument, or on standard input.
func Run(answer func(op string, in []byte) (any, bool)) {
	var input io.Reader = os.Stdin
	if len(os.Args) > 1 {
		f, err := os.Open(os.Args[1])
		if err != nil {
			fmt.Fprintln(os.Stderr, err)
			os.Exit(2)
		}
		defer f.Close()
		input = f
	}
	scanner := bufio.NewScanner(input)
	scanner.Buffer(make([]byte, 1<<20), 1<<26)
	out := bufio.NewWriter(os.Stdout)
	defer out.Flush()
	encoder := json.NewEncoder(out)
	encoder.SetEscapeHTML(false)
	for scanner.Scan() {
		var c Case
		if err := json.Unmarshal(scanner.Bytes(), &c); err != nil {
			fmt.Fprintln(os.Stderr, "bad case:", err)
			os.Exit(2)
		}
		in, err := hex.DecodeString(c.In)
		if err != nil {
			fmt.Fprintln(os.Stderr, "bad hex in case", c.ID)
			os.Exit(2)
		}
		result, ok := answer(c.Op, in)
		a := Answer{ID: c.ID, OK: ok}
		if ok {
			a.Out = result
		}
		if err := encoder.Encode(a); err != nil {
			fmt.Fprintln(os.Stderr, err)
			os.Exit(2)
		}
	}
	if err := scanner.Err(); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(2)
	}
}
