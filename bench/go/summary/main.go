// Reads the JSON lines run.sh writes, one per run, and the machine's description, and writes
// a Markdown report and a JSON file: one row per server and connection count, with medians
// over the runs and their spread.
package main

import (
	"bufio"
	"encoding/json"
	"flag"
	"fmt"
	"os"
	"sort"
	"strings"
)

type load struct {
	Conns       int     `json:"conns"`
	Seconds     float64 `json:"seconds"`
	Requests    int     `json:"requests"`
	RPS         float64 `json:"rps"`
	P50us       float64 `json:"p50_us"`
	P90us       float64 `json:"p90_us"`
	P99us       float64 `json:"p99_us"`
	MaxUs       float64 `json:"max_us"`
	Errors      int64   `json:"errors"`
	Reconnects  int64   `json:"reconnects"`
	Non2xx      int64   `json:"non2xx"`
	ServerCPUs  float64 `json:"server_cpu_s"`
	ServerRSSkB int64   `json:"server_rss_peak_kb"`
	Threads     int64   `json:"server_threads"`
	LoadCPUs    float64 `json:"load_cpu_s"`
	OtherCPUs   float64 `json:"other_cpu_s"`
	SoftirqCPUs float64 `json:"softirq_s"`
}

type run struct {
	Server       string  `json:"server"`
	Run          int     `json:"run"`
	Load1        float64 `json:"load1"`
	OtherJobs    int     `json:"other_jobs"`
	JournalBytes int64   `json:"journal_bytes"`
	Alive        bool    `json:"alive"`
	Load         load    `json:"load"`
}

type row struct {
	Server        string  `json:"server"`
	Conns         int     `json:"conns"`
	Runs          int     `json:"runs"`
	RPS           float64 `json:"rps_median"`
	RPSMin        float64 `json:"rps_min"`
	RPSMax        float64 `json:"rps_max"`
	SpreadPct     float64 `json:"rps_spread_pct"`
	P50us         float64 `json:"p50_us_median"`
	P99us         float64 `json:"p99_us_median"`
	MaxUs         float64 `json:"max_us_median"`
	ServerCores   float64 `json:"server_cpu_cores_median"`
	CPUPerReqUs   float64 `json:"server_cpu_us_per_request_median"`
	RSSMB         float64 `json:"server_rss_peak_mb_max"`
	Threads       int64   `json:"server_threads_max"`
	Reconnects    float64 `json:"reconnects_median"`
	Errors        int64   `json:"errors_total"`
	OtherCores    float64 `json:"other_cpu_cores_max"`
	Disturbed     int     `json:"disturbed_runs"`
	Crashed       int     `json:"crashed_runs"`
	JournalMBEach float64 `json:"journal_mb_max"`
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
	if len(xs) == 0 {
		return 0, 0
	}
	lo, hi := xs[0], xs[0]
	for _, x := range xs {
		lo, hi = min(lo, x), max(hi, x)
	}
	return lo, hi
}

func main() {
	machinePath := flag.String("machine", "", "a JSON file describing the machine and the settings")
	mdPath := flag.String("md", "", "where to write the Markdown report (default: standard output)")
	jsonPath := flag.String("json", "", "where to write the JSON report")
	idleCores := flag.Float64("idle-cores", 1.0, "other CPU, in cores, above which a run is disturbed")
	flag.Parse()

	machine := map[string]any{}
	if *machinePath != "" {
		data, err := os.ReadFile(*machinePath)
		if err == nil {
			err = json.Unmarshal(data, &machine)
		}
		if err != nil {
			fmt.Fprintln(os.Stderr, "machine:", err)
			os.Exit(1)
		}
	}

	type key struct {
		server string
		conns  int
	}
	var order []key
	var runs []run
	groups := map[key][]run{}
	for _, path := range flag.Args() {
		f, err := os.Open(path)
		if err != nil {
			fmt.Fprintln(os.Stderr, err)
			os.Exit(1)
		}
		scanner := bufio.NewScanner(f)
		scanner.Buffer(make([]byte, 1<<16), 1<<20)
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
			runs = append(runs, r)
		}
		f.Close()
	}

	disturbed := func(r run) bool {
		return r.OtherJobs > 0 || (r.Load.Seconds > 0 && r.Load.OtherCPUs/r.Load.Seconds > *idleCores)
	}
	var rows []row
	totalDisturbed := 0
	for _, k := range order {
		rs := groups[k]
		var rps, p50, p99, mx, cores, perReq, rss, rec, other, journal []float64
		out := row{Server: k.server, Conns: k.conns, Runs: len(rs)}
		for _, r := range rs {
			l := r.Load
			rps = append(rps, l.RPS)
			p50 = append(p50, l.P50us)
			p99 = append(p99, l.P99us)
			mx = append(mx, l.MaxUs)
			if l.Seconds > 0 {
				cores = append(cores, l.ServerCPUs/l.Seconds)
				other = append(other, l.OtherCPUs/l.Seconds)
			}
			if l.Requests > 0 {
				perReq = append(perReq, 1e6*l.ServerCPUs/float64(l.Requests))
			}
			rss = append(rss, float64(l.ServerRSSkB)/1024)
			rec = append(rec, float64(l.Reconnects))
			journal = append(journal, float64(r.JournalBytes)/1e6)
			out.Threads = max(out.Threads, l.Threads)
			out.Errors += l.Errors + l.Non2xx
			if disturbed(r) {
				out.Disturbed++
			}
			if !r.Alive {
				out.Crashed++
			}
		}
		totalDisturbed += out.Disturbed
		out.RPS = median(rps)
		out.RPSMin, out.RPSMax = minMax(rps)
		if out.RPS > 0 {
			out.SpreadPct = 100 * (out.RPSMax - out.RPSMin) / out.RPS
		}
		out.P50us, out.P99us, out.MaxUs = median(p50), median(p99), median(mx)
		out.ServerCores, out.CPUPerReqUs = median(cores), median(perReq)
		_, out.RSSMB = minMax(rss)
		out.Reconnects = median(rec)
		_, out.OtherCores = minMax(other)
		_, out.JournalMBEach = minMax(journal)
		rows = append(rows, out)
	}

	var md strings.Builder
	fmt.Fprintf(&md, "# HTTP benchmark\n\n")
	keys := make([]string, 0, len(machine))
	for k := range machine {
		keys = append(keys, k)
	}
	sort.Strings(keys)
	for _, k := range keys {
		fmt.Fprintf(&md, "- %s: %v\n", k, machine[k])
	}
	fmt.Fprintf(&md, "\n")
	if totalDisturbed > 0 {
		fmt.Fprintf(&md, "**%d of %d runs were disturbed** (another job on the machine, or more than %.1f cores of other CPU): their numbers are not results.\n\n",
			totalDisturbed, len(runs), *idleCores)
	}
	fmt.Fprintln(&md, "| server | conns | runs | req/s (median) | req/s (min–max) | spread % | p50 µs | p99 µs | max µs | server CPU (cores) | CPU µs/req | peak RSS MB | threads | reconnects | errors | other CPU (cores, max) | disturbed | crashed |")
	fmt.Fprintln(&md, "| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |")
	for _, r := range rows {
		fmt.Fprintf(&md, "| %s | %d | %d | %.0f | %.0f–%.0f | %.1f | %.0f | %.0f | %.0f | %.2f | %.1f | %.1f | %d | %.0f | %d | %.2f | %d | %d |\n",
			r.Server, r.Conns, r.Runs, r.RPS, r.RPSMin, r.RPSMax, r.SpreadPct, r.P50us, r.P99us, r.MaxUs,
			r.ServerCores, r.CPUPerReqUs, r.RSSMB, r.Threads, r.Reconnects, r.Errors, r.OtherCores,
			r.Disturbed, r.Crashed)
	}
	if *mdPath == "" {
		fmt.Print(md.String())
	} else if err := os.WriteFile(*mdPath, []byte(md.String()), 0o644); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}

	if *jsonPath != "" {
		data, err := json.MarshalIndent(map[string]any{
			"machine": machine, "disturbed_runs": totalDisturbed, "rows": rows, "runs": runs,
		}, "", "  ")
		if err == nil {
			err = os.WriteFile(*jsonPath, append(data, '\n'), 0o644)
		}
		if err != nil {
			fmt.Fprintln(os.Stderr, err)
			os.Exit(1)
		}
	}
}
