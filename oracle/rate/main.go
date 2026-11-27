// Ops: run ("<num>/<den> <burst>" then one "allow <ms> <n>" or "reserve <ms> <n>" per line in;
// for each, AllowN's answer or ReserveN's delay in nanoseconds, null when it is not OK). The
// limiter allows num/den events a second; times are milliseconds after a fixed instant.
package main

import (
	"fmt"
	"strings"
	"time"

	"golang.org/x/time/rate"

	"lanes/oracle/internal/cases"
)

func main() {
	start := time.Unix(1_000_000_000, 0)
	cases.Run(func(op string, in []byte) (any, bool) {
		switch op {
		case "run":
			lines := strings.Split(string(in), "\n")
			var num, den float64
			var burst int
			if _, err := fmt.Sscanf(lines[0], "%g/%g %d", &num, &den, &burst); err != nil {
				panic(err)
			}
			lim := rate.NewLimiter(rate.Limit(num/den), burst)
			out := []any{}
			for _, line := range lines[1:] {
				var kind string
				var ms int64
				var n int
				if _, err := fmt.Sscanf(line, "%s %d %d", &kind, &ms, &n); err != nil {
					panic(err)
				}
				t := start.Add(time.Duration(ms) * time.Millisecond)
				switch kind {
				case "allow":
					out = append(out, lim.AllowN(t, n))
				case "reserve":
					r := lim.ReserveN(t, n)
					if !r.OK() {
						out = append(out, nil)
					} else {
						out = append(out, r.DelayFrom(t).Nanoseconds())
					}
				default:
					panic("unknown request " + kind)
				}
			}
			return out, true
		}
		panic("unknown op " + op)
	})
}
