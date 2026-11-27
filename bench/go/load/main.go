// A minimal keep-alive HTTP/1.1 load generator: N connections, each sending one GET at a
// time for a fixed duration. A server that closes a connection (Connection: close, or EOF
// between responses) is dialed again, and the reconnect is counted.
package main

import (
	"bufio"
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"io"
	"net"
	"os"
	"sort"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"syscall"
	"time"
)

type result struct {
	Conns      int     `json:"conns"`
	Seconds    float64 `json:"seconds"`
	Requests   int     `json:"requests"`
	RPS        float64 `json:"rps"`
	P50us      float64 `json:"p50_us"`
	P90us      float64 `json:"p90_us"`
	P99us      float64 `json:"p99_us"`
	MaxUs      float64 `json:"max_us"`
	Errors     int64   `json:"errors"`
	Reconnects int64   `json:"reconnects"`
	Non2xx     int64   `json:"non2xx"`
	// Measured over the same window as the requests, when -pid is given.
	ServerCPUs  float64 `json:"server_cpu_s"`
	ServerRSSkB int64   `json:"server_rss_peak_kb"`
	Threads     int64   `json:"server_threads"`
	LoadCPUs    float64 `json:"load_cpu_s"`
	// CPU time spent on the -cpus set by anything but the server, this process and the
	// kernel's threads: other jobs on the machine. Kernel threads are counted on every CPU, so
	// this is exact when -cpus covers the machine. Softirq time is apart from all of these.
	OtherCPUs         float64 `json:"other_cpu_s"`
	KernelThreadsCPUs float64 `json:"kernel_threads_cpu_s"`
	SoftirqCPUs       float64 `json:"softirq_s"`
}

// The kernel's USER_HZ, which /proc/<pid>/stat and /proc/stat count in; 100 on Linux.
const userHz = 100

// cpuList parses a list such as "0-3,8,10-11" into a set; empty means every CPU.
func cpuList(s string) (map[int]bool, error) {
	if s == "" {
		return nil, nil
	}
	set := map[int]bool{}
	for _, part := range strings.Split(s, ",") {
		lo, hi, isRange := strings.Cut(part, "-")
		a, err := strconv.Atoi(lo)
		if err != nil {
			return nil, err
		}
		b := a
		if isRange {
			if b, err = strconv.Atoi(hi); err != nil {
				return nil, err
			}
		}
		for c := a; c <= b; c++ {
			set[c] = true
		}
	}
	return set, nil
}

// cpuTicks sums the busy (user, nice, system) and softirq ticks of the CPUs in set.
func cpuTicks(set map[int]bool) (busy, softirq int64) {
	data, err := os.ReadFile("/proc/stat")
	if err != nil {
		return 0, 0
	}
	for _, line := range strings.Split(string(data), "\n") {
		f := strings.Fields(line)
		if len(f) < 8 || !strings.HasPrefix(f[0], "cpu") || f[0] == "cpu" {
			continue
		}
		n, err := strconv.Atoi(f[0][3:])
		if err != nil || (set != nil && !set[n]) {
			continue
		}
		v := func(i int) int64 { x, _ := strconv.ParseInt(f[i], 10, 64); return x }
		busy += v(1) + v(2) + v(3)
		softirq += v(7)
	}
	return busy, softirq
}

// processTicks is utime + stime of a process, from the fields after its name in /proc/<pid>/stat.
func processTicks(pid int) int64 {
	data, err := os.ReadFile(fmt.Sprintf("/proc/%d/stat", pid))
	if err != nil {
		return 0
	}
	s := string(data)
	f := strings.Fields(s[strings.LastIndexByte(s, ')')+1:])
	if len(f) < 13 {
		return 0
	}
	u, _ := strconv.ParseInt(f[11], 10, 64)
	k, _ := strconv.ParseInt(f[12], 10, 64)
	return u + k
}

// kernelThreadTicks sums utime + stime of the kernel's threads (kthreadd, pid 2, and its
// children), such as ksoftirqd, which carry the loopback's packets under load.
func kernelThreadTicks() int64 {
	entries, err := os.ReadDir("/proc")
	if err != nil {
		return 0
	}
	var total int64
	for _, e := range entries {
		pid, err := strconv.Atoi(e.Name())
		if err != nil {
			continue
		}
		data, err := os.ReadFile(fmt.Sprintf("/proc/%d/stat", pid))
		if err != nil {
			continue
		}
		s := string(data)
		f := strings.Fields(s[strings.LastIndexByte(s, ')')+1:])
		if len(f) < 13 || (pid != 2 && f[1] != "2") {
			continue
		}
		u, _ := strconv.ParseInt(f[11], 10, 64)
		k, _ := strconv.ParseInt(f[12], 10, 64)
		total += u + k
	}
	return total
}

// status reads a "Name: value kB" field of /proc/<pid>/status.
func status(pid int, name string) int64 {
	data, err := os.ReadFile(fmt.Sprintf("/proc/%d/status", pid))
	if err != nil {
		return 0
	}
	for _, line := range strings.Split(string(data), "\n") {
		if rest, ok := strings.CutPrefix(line, name+":"); ok {
			f := strings.Fields(rest)
			if len(f) > 0 {
				x, _ := strconv.ParseInt(f[0], 10, 64)
				return x
			}
		}
	}
	return 0
}

func selfCPU() time.Duration {
	var ru syscall.Rusage
	syscall.Getrusage(syscall.RUSAGE_SELF, &ru)
	return time.Duration(ru.Utime.Nano() + ru.Stime.Nano())
}

// readResponse reads one response and says whether the connection stays open.
func readResponse(r *bufio.Reader) (status int, keep bool, err error) {
	line, err := r.ReadSlice('\n')
	if err != nil {
		return 0, false, err
	}
	fields := strings.Fields(string(line))
	if len(fields) < 2 {
		return 0, false, fmt.Errorf("bad status line %q", line)
	}
	status, err = strconv.Atoi(fields[1])
	if err != nil {
		return 0, false, err
	}
	keep = true
	length := -1
	chunked := false
	for {
		h, err := r.ReadSlice('\n')
		if err != nil {
			return 0, false, err
		}
		if len(h) <= 2 {
			break
		}
		colon := strings.IndexByte(string(h), ':')
		if colon < 0 {
			continue
		}
		name := strings.ToLower(string(h[:colon]))
		value := strings.TrimSpace(string(h[colon+1:]))
		switch name {
		case "content-length":
			length, _ = strconv.Atoi(value)
		case "connection":
			if strings.EqualFold(value, "close") {
				keep = false
			}
		case "transfer-encoding":
			chunked = strings.Contains(strings.ToLower(value), "chunked")
		}
	}
	switch {
	case chunked:
		for {
			sizeLine, err := r.ReadString('\n')
			if err != nil {
				return 0, false, err
			}
			size, err := strconv.ParseInt(strings.TrimSpace(strings.SplitN(sizeLine, ";", 2)[0]), 16, 64)
			if err != nil {
				return 0, false, err
			}
			if _, err := r.Discard(int(size) + 2); err != nil {
				return 0, false, err
			}
			if size == 0 {
				break
			}
		}
	case length >= 0:
		if _, err := r.Discard(length); err != nil {
			return 0, false, err
		}
	default:
		io.Copy(io.Discard, r)
		keep = false
	}
	return status, keep, nil
}

func main() {
	addr := flag.String("addr", "127.0.0.1:8090", "server address")
	conns := flag.Int("c", 16, "connections")
	duration := flag.Duration("d", 10*time.Second, "measured duration")
	warmup := flag.Duration("warmup", time.Second, "unmeasured time before the measurement")
	path := flag.String("path", "/", "request path")
	asJSON := flag.Bool("json", false, "print one JSON line")
	pid := flag.Int("pid", 0, "the server's process, whose CPU time and peak RSS to measure")
	cpus := flag.String("cpus", "", "the CPUs to measure other work on, as 0-3,8 (default all)")
	flag.Parse()
	cpuSet, err := cpuList(*cpus)
	if err != nil {
		fmt.Fprintln(os.Stderr, "bad -cpus:", err)
		os.Exit(2)
	}

	request := []byte("GET " + *path + " HTTP/1.1\r\nHost: 127.0.0.1\r\nUser-Agent: lanesbench\r\n\r\n")
	var errorCount, reconnects, non2xx atomic.Int64
	var measuring atomic.Bool
	var stop atomic.Bool
	latencies := make([][]time.Duration, *conns)
	var wg sync.WaitGroup
	for w := 0; w < *conns; w++ {
		wg.Add(1)
		go func(w int) {
			defer wg.Done()
			own := make([]time.Duration, 0, 1<<16)
			var conn net.Conn
			var reader *bufio.Reader
			dial := func() bool {
				if conn != nil {
					conn.Close()
				}
				c, err := net.Dial("tcp", *addr)
				if err != nil {
					errorCount.Add(1)
					time.Sleep(10 * time.Millisecond)
					conn = nil
					return false
				}
				c.(*net.TCPConn).SetNoDelay(true)
				conn, reader = c, bufio.NewReaderSize(c, 16384)
				return true
			}
			for !stop.Load() {
				if conn == nil && !dial() {
					continue
				}
				start := time.Now()
				if _, err := conn.Write(request); err != nil {
					if measuring.Load() {
						reconnects.Add(1)
					}
					conn.Close()
					conn = nil
					continue
				}
				status, keep, err := readResponse(reader)
				elapsed := time.Since(start)
				if err != nil {
					if measuring.Load() && !stop.Load() {
						if errors.Is(err, io.EOF) {
							reconnects.Add(1)
						} else {
							errorCount.Add(1)
						}
					}
					conn.Close()
					conn = nil
					continue
				}
				if measuring.Load() && !stop.Load() {
					own = append(own, elapsed)
					if status < 200 || status >= 300 {
						non2xx.Add(1)
					}
					if !keep {
						reconnects.Add(1)
					}
				}
				if !keep {
					conn.Close()
					conn = nil
				}
			}
			if conn != nil {
				conn.Close()
			}
			latencies[w] = own
		}(w)
	}
	time.Sleep(*warmup)
	serverBefore, selfBefore := processTicks(*pid), selfCPU()
	kernelBefore := kernelThreadTicks()
	busyBefore, softBefore := cpuTicks(cpuSet)
	measuring.Store(true)
	began := time.Now()
	time.Sleep(*duration)
	stop.Store(true)
	seconds := time.Since(began).Seconds()
	busyAfter, softAfter := cpuTicks(cpuSet)
	kernelAfter := kernelThreadTicks()
	serverAfter, selfAfter := processTicks(*pid), selfCPU()
	wg.Wait()
	serverCPU := float64(serverAfter-serverBefore) / userHz
	loadCPU := (selfAfter - selfBefore).Seconds()

	var all []time.Duration
	for _, l := range latencies {
		all = append(all, l...)
	}
	sort.Slice(all, func(i, j int) bool { return all[i] < all[j] })
	pct := func(p float64) float64 {
		if len(all) == 0 {
			return 0
		}
		i := int(p * float64(len(all)-1))
		return float64(all[i].Nanoseconds()) / 1000
	}
	res := result{
		Conns: *conns, Seconds: seconds, Requests: len(all), RPS: float64(len(all)) / seconds,
		P50us: pct(0.50), P90us: pct(0.90), P99us: pct(0.99), MaxUs: pct(1),
		Errors: errorCount.Load(), Reconnects: reconnects.Load(), Non2xx: non2xx.Load(),
		LoadCPUs:          loadCPU,
		KernelThreadsCPUs: float64(kernelAfter-kernelBefore) / userHz,
		SoftirqCPUs:       float64(softAfter-softBefore) / userHz,
	}
	res.OtherCPUs = float64(busyAfter-busyBefore)/userHz - loadCPU - res.KernelThreadsCPUs
	if *pid != 0 {
		res.ServerCPUs = serverCPU
		res.OtherCPUs -= serverCPU
		res.ServerRSSkB = status(*pid, "VmHWM")
		res.Threads = status(*pid, "Threads")
	}
	if *asJSON {
		json.NewEncoder(os.Stdout).Encode(res)
		return
	}
	fmt.Printf("%d connections, %.1f s: %d requests, %.0f req/s\n", res.Conns, res.Seconds, res.Requests, res.RPS)
	fmt.Printf("latency p50 %.0f us, p90 %.0f us, p99 %.0f us, max %.0f us\n", res.P50us, res.P90us, res.P99us, res.MaxUs)
	fmt.Printf("errors %d, reconnects %d, non-2xx %d\n", res.Errors, res.Reconnects, res.Non2xx)
	fmt.Printf("CPU s: server %.2f, load generator %.2f, kernel threads %.2f, other %.2f, softirq %.2f\n",
		res.ServerCPUs, res.LoadCPUs, res.KernelThreadsCPUs, res.OtherCPUs, res.SoftirqCPUs)
}
