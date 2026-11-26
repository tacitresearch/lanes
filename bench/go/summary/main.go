// Reads the JSON lines run.sh writes and prints one Markdown row per server and connection
// count: medians over the runs, with the lowest and highest rate.
package main

import (
	"bufio"
	"encoding/json"
	"fmt"
	"os"
	"sort"
)

type load struct {
	Conns      int     `json:"conns"`
	Seconds    float64 `json:"seconds"`
	Requests   int     `json:"requests"`
	RPS        float64 `json:"rps"`
	P50us      float64 `json:"p50_us"`
	P99us      float64 `json:"p99_us"`
	MaxUs      float64 `json:"max_us"`
	Errors     int64   `json:"errors"`
	Reconnects int64   `json:"reconnects"`
	Non2xx     int64   `json:"non2xx"`
}

type run struct {
	Server       string  `json:"server"`
	Load1        float64 `json:"load1"`
	CPUs         float64 `json:"cpu_s"`
	RSSkB        int     `json:"rss_kb"`
	JournalBytes int64   `json:"journal_bytes"`
	Load         load    `json:"load"`
}

func median(xs []float64) float64 {
	s := append([]float64(nil), xs...)
	sort.Float64s(s)
	if len(s) == 0 {
		return 0
	}
	if len(s)%2 == 1 {
		return s[len(s)/2]
	}
	return (s[len(s)/2-1] + s[len(s)/2]) / 2
}

func minMax(xs []float64) (float64, float64) {
	lo, hi := xs[0], xs[0]
	for _, x := range xs {
		if x < lo {
			lo = x
		}
		if x > hi {
			hi = x
		}
	}
	return lo, hi
}

func main() {
	type key struct {
		server string
		conns  int
	}
	var order []key
	groups := map[key][]run{}
	for _, path := range os.Args[1:] {
		f, err := os.Open(path)
		if err != nil {
			fmt.Fprintln(os.Stderr, err)
			os.Exit(1)
		}
		scanner := bufio.NewScanner(f)
		for scanner.Scan() {
			var r run
			if err := json.Unmarshal(scanner.Bytes(), &r); err != nil {
				continue
			}
			k := key{r.Server, r.Load.Conns}
			if _, ok := groups[k]; !ok {
				order = append(order, k)
			}
			groups[k] = append(groups[k], r)
		}
		f.Close()
	}
	fmt.Println("| server | conns | runs | req/s (median) | req/s (min–max) | p50 µs | p99 µs | max µs | server CPU % | CPU µs/req | peak RSS MB | reconnects | errors | load avg |")
	fmt.Println("| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |")
	for _, k := range order {
		rs := groups[k]
		var rps, p50, p99, mx, cpuPct, cpuPer, rss, rec, loads []float64
		var errs int64
		for _, r := range rs {
			rps = append(rps, r.Load.RPS)
			p50 = append(p50, r.Load.P50us)
			p99 = append(p99, r.Load.P99us)
			mx = append(mx, r.Load.MaxUs)
			cpuPct = append(cpuPct, 100*r.CPUs/r.Load.Seconds)
			if r.Load.Requests > 0 {
				cpuPer = append(cpuPer, 1e6*r.CPUs/float64(r.Load.Requests))
			}
			rss = append(rss, float64(r.RSSkB)/1024)
			rec = append(rec, float64(r.Load.Reconnects))
			loads = append(loads, r.Load1)
			errs += r.Load.Errors + r.Load.Non2xx
		}
		lo, hi := minMax(rps)
		_, rssHi := minMax(rss)
		fmt.Printf("| %s | %d | %d | %.0f | %.0f–%.0f | %.0f | %.0f | %.0f | %.0f | %.1f | %.1f | %.0f | %d | %.1f |\n",
			k.server, k.conns, len(rs), median(rps), lo, hi, median(p50), median(p99), median(mx),
			median(cpuPct), median(cpuPer), rssHi, median(rec), errs, median(loads))
	}
}
