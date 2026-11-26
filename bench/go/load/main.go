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
}

var errClosed = errors.New("server closed the connection")

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
	flag.Parse()

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
	measuring.Store(true)
	began := time.Now()
	time.Sleep(*duration)
	stop.Store(true)
	seconds := time.Since(began).Seconds()
	wg.Wait()

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
	}
	if *asJSON {
		json.NewEncoder(os.Stdout).Encode(res)
		return
	}
	fmt.Printf("%d connections, %.1f s: %d requests, %.0f req/s\n", res.Conns, res.Seconds, res.Requests, res.RPS)
	fmt.Printf("latency p50 %.0f us, p90 %.0f us, p99 %.0f us, max %.0f us\n", res.P50us, res.P90us, res.P99us, res.MaxUs)
	fmt.Printf("errors %d, reconnects %d, non-2xx %d\n", res.Errors, res.Reconnects, res.Non2xx)
}
