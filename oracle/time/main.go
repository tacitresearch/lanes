// Ops: rfc3339 (text in, the fields Go's time.Parse(time.RFC3339Nano) reads), rfc3339-format
// ("y m d h mi s ns offset_min" in, Format(time.RFC3339Nano) out), unix (seconds in, the UTC
// fields), days ("y m d" in, days since the epoch), http (text in, http.ParseTime's fields) and
// http-format ("y m d h mi s" in, Format(http.TimeFormat) out).
package main

import (
	"fmt"
	"net/http"
	"time"

	"lanes/oracle/internal/cases"
)

func fields(t time.Time, nanos bool) map[string]int64 {
	_, offset := t.Zone()
	f := map[string]int64{
		"year": int64(t.Year()), "month": int64(t.Month()), "day": int64(t.Day()),
		"hour": int64(t.Hour()), "minute": int64(t.Minute()), "second": int64(t.Second()),
		"unix": t.Unix(),
	}
	if nanos {
		f["nanos"] = int64(t.Nanosecond())
		f["offset"] = int64(offset)
	}
	return f
}

func main() {
	cases.Run(func(op string, in []byte) (any, bool) {
		s := string(in)
		switch op {
		case "rfc3339":
			t, err := time.Parse(time.RFC3339Nano, s)
			if err != nil {
				return nil, false
			}
			return fields(t, true), true
		case "rfc3339-format":
			var y, m, d, h, mi, sec, ns, off int
			if _, err := fmt.Sscan(s, &y, &m, &d, &h, &mi, &sec, &ns, &off); err != nil {
				panic(err)
			}
			zone := time.FixedZone("", off*60)
			return time.Date(y, time.Month(m), d, h, mi, sec, ns, zone).Format(time.RFC3339Nano), true
		case "unix":
			var n int64
			if _, err := fmt.Sscan(s, &n); err != nil {
				panic(err)
			}
			return fields(time.Unix(n, 0).UTC(), false), true
		case "days":
			var y, m, d int
			if _, err := fmt.Sscan(s, &y, &m, &d); err != nil {
				panic(err)
			}
			return time.Date(y, time.Month(m), d, 0, 0, 0, 0, time.UTC).Unix() / 86400, true
		case "http":
			t, err := http.ParseTime(s)
			if err != nil {
				return nil, false
			}
			return fields(t.UTC(), false), true
		case "http-format":
			var y, m, d, h, mi, sec int
			if _, err := fmt.Sscan(s, &y, &m, &d, &h, &mi, &sec); err != nil {
				panic(err)
			}
			return time.Date(y, time.Month(m), d, h, mi, sec, 0, time.UTC).Format(http.TimeFormat), true
		}
		panic("unknown op " + op)
	})
}
