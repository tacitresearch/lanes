// Ops: parse (text in; the components url.Parse reads and URL.String), resolve ("<base> <ref>"
// in; the components of base.ResolveReference(ref), as for parse), query (text in; url.ParseQuery's values) and
// query-encode (keys and values separated by NUL in; Values.Encode).
package main

import (
	"encoding/hex"
	"net/netip"
	"net/url"
	"strings"

	"lanes/oracle/internal/cases"
)

func host(u *url.URL) string {
	h := u.Hostname()
	if strings.HasPrefix(u.Host, "[") {
		if a, err := netip.ParseAddr(h); err == nil {
			return "ip6:" + a.String()
		}
		return "bad:" + h
	}
	return "name:" + hex.EncodeToString([]byte(h))
}

// authority says whether Go read an authority: a "//" after the scheme, or at the start but
// not "///" (which url.Parse reads as a path).
func authority(u *url.URL, s string) bool {
	rest := s
	if u.Scheme != "" {
		rest = s[len(u.Scheme)+1:]
	}
	return u.Host != "" || u.User != nil ||
		strings.HasPrefix(rest, "//") && (u.Scheme != "" || !strings.HasPrefix(rest, "///"))
}

func parse(u *url.URL, s string) map[string]any {
	out := map[string]any{"string": u.String()}
	if u.Scheme != "" {
		out["scheme"] = u.Scheme
	}
	if u.User != nil {
		out["user"] = hex.EncodeToString([]byte(u.User.Username()))
		if p, ok := u.User.Password(); ok {
			out["password"] = hex.EncodeToString([]byte(p))
		}
	}
	if authority(u, s) {
		out["host"] = host(u)
	}
	if p := u.Port(); p != "" {
		out["port"] = p
	}
	if u.Opaque != "" {
		out["path"] = u.Opaque
	} else {
		out["path"] = u.EscapedPath()
	}
	if u.ForceQuery || u.RawQuery != "" {
		out["query"] = u.RawQuery
	}
	if u.Fragment != "" {
		out["fragment"] = u.EscapedFragment()
	}
	return out
}

func main() {
	cases.Run(func(op string, in []byte) (any, bool) {
		s := string(in)
		switch op {
		case "parse":
			u, err := url.Parse(s)
			if err != nil {
				return nil, false
			}
			return parse(u, s), true
		case "resolve":
			b, r, found := strings.Cut(s, " ")
			if !found {
				return nil, false
			}
			base, err := url.Parse(b)
			if err != nil {
				return nil, false
			}
			ref, err := url.Parse(r)
			if err != nil {
				return nil, false
			}
			t := base.ResolveReference(ref)
			return parse(t, t.String()), true
		case "query":
			v, err := url.ParseQuery(s)
			if err != nil {
				return nil, false
			}
			return v, true
		case "query-encode":
			v := url.Values{}
			parts := strings.Split(s, "\x00")
			for i := 0; i+1 < len(parts); i += 2 {
				v.Add(parts[i], parts[i+1])
			}
			return v.Encode(), true
		}
		panic("unknown op " + op)
	})
}
