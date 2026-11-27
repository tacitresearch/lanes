// The Go side of oracles/go/requests/requests.py: net/http's server with the limits of Request.Limits,
// answering each request it reads with its method and the length of its body, 400 for a body
// it cannot decode and 599 for one cut short by the end of the connection.
package main

import (
	"errors"
	"fmt"
	"io"
	"net"
	"net/http"
	"os"
)

func main() {
	listener, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		panic(err)
	}
	fmt.Println(listener.Addr().(*net.TCPAddr).Port)
	os.Stdout.Sync()
	handler := http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		body, err := io.ReadAll(http.MaxBytesReader(w, r.Body, 1048576))
		var tooLarge *http.MaxBytesError
		switch {
		case errors.As(err, &tooLarge):
			w.WriteHeader(413)
		case errors.Is(err, io.ErrUnexpectedEOF):
			w.WriteHeader(599)
		case err != nil:
			w.WriteHeader(400)
		default:
			w.Header().Set("X-Verdict", fmt.Sprintf("ok:%s:%d", r.Method, len(body)))
			w.WriteHeader(200)
		}
	})
	server := &http.Server{Handler: handler, MaxHeaderBytes: 16384}
	server.Serve(listener)
}
