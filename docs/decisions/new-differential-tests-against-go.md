# D?. A parser is proved against its RFC and tested against Go, and every difference is decided

A proof says the code meets its spec; it does not say the spec reads the standard right. Go's
standard library has had years of use, so each package of the standard library Lanes builds
(`docs/STDLIB.md`) is also run against Go's on generated inputs, and each input on which the
two differ is either a misreading of ours, fixed, or a place where we depart from Go on purpose,
written down as a predicate with its reason.

**The pattern.** `oracle/` is a Go module (`oracle/go.mod` pins the toolchain) with one program
per package, `oracle/<package>/main.go`, built on `oracle/internal/cases`: it reads one case per
line, `{"id": 7, "op": "decode-std", "in": "<hex>"}`, and answers one line per case,
`{"id": 7, "ok": true, "out": …}` or `"ok": false` for a refusal. Inputs are hex so that invalid
UTF-8 survives. On the Lean side a `Package` (`Tests/Oracle/Basic.lean`) has a generator of
cases, fixed edge cases first, our answer in the same JSON shape, and a `known` predicate that,
given Go's answer, names the reason for a decided difference. Only acceptance and the structured
result are compared, never error messages.

- `lake exe lanesOracle [--cases N] [--seed S] [package…]` runs `go build`, asks Go, compares
  and prints, per package, the agreements, the known differences with a count and an example of
  each reason, and every other difference shrunk by deleting bytes while it still differs, with
  the command that reproduces it. It exits non-zero on any difference no predicate decides.
- `--record` writes the first thousand cases with Go's answers to
  `Tests/Oracle/vectors/<package>.jsonl`; `lake test` replays them (`Package.replay`), so it
  never needs Go.
- A package is added as `Tests/Oracle/<Package>.lean`, listed in `Tests/Oracle/All.lean`, and an
  `oracle/<package>/main.go`. Its `known` predicates live in its own file, so branches that add
  packages touch disjoint files.

**Results on 100,000 cases each (seed 0).** Base64: 99,434 agree, 566 known, none other. IP
addresses and prefixes: 98,197 agree, 1,803 known, none other. Time: 91,233 agree, 8,767 known,
none other. The cases mix valid encodings, one-edit mutations of them and random strings over
each grammar's alphabet; about two thirds of the address cases are accepted by Go.

**Where we depart from Go, and why.**

- *Base64: newlines.* Go's decoders skip `\r` and `\n` anywhere, even `Strict()` ones. Ours
  refuse them: `decode e s = some b ↔ encode e b = s` (`Base64.decode_eq_some_iff`) makes every
  byte string have one spelling, which is what makes an encoded cursor or token comparable as
  text. Otherwise we are Go's `Strict()` mode: padding exactly as RFC 4648 §3.2 writes it for the
  padded encodings and none for the raw ones, zero trailing bits (§3.5), only the alphabet.
- *IP: zones.* Go's `ParseAddr` reads `fe80::1%eth0`. Ours refuses a zone: it names an interface
  of the host that wrote it and means nothing as a rate-limit key or in another machine's
  logs; RFC 6874 zones in URLs can be added with the URL parser if one is needed. Everything else
  agrees with Go: dotted decimal without leading zeros, one to four hex digits per group in
  either case, one `::` standing for at least one group, an IPv4 tail only in the last 32 bits,
  and RFC 5952 output with `::ffff:a.b.c.d` for mapped addresses, as Go writes it.
- *RFC 3339: lowercase `t` and `z`.* RFC 3339 §5.6 allows them; Go refuses them. Ours reads them
  and writes uppercase.
- *RFC 3339: Go's fallback.* `time.Parse(time.RFC3339Nano, …)` tries a strict parser and, when
  that fails, Go's general layout parser, which reads an hour of one digit, a comma before the
  fraction and offsets of hour 24 or more and minute 60 or more (go.dev/issue/54580, where the
  strict checks are disabled). Ours is RFC 3339's grammar: two digits, a period, offsets under
  24:00. With Go we refuse a leap second (`:60`): POSIX time has no place for one. With Go we
  keep nine fraction digits and drop the rest.
- *HTTP dates.* Go's `http.ParseTime` reads day and month names in any case, an hour of one
  digit and runs of spaces, and does not check the day name against the date. RFC 9110 §5.6.7
  names are case-sensitive and the grammar has two-digit hours and single spaces; ours follows
  it, and refuses a date whose day name is not its own, so that a date has one spelling. Go reads
  an RFC 850 two-digit year as 1969 to 2068; RFC 9110 says a year more than 50 years ahead is the
  century before, so ours takes the current year as an argument (`parseHttpDate nowYear`), and
  the oracle passes 2018, at which the two rules agree.

Each of these is a predicate in `Tests/Oracle/Base64.lean`, `Ip.lean` or `Time.lean`. The ones
that say "Go reads X" check that ours, given the input with X written our way, answers as Go
did, so a predicate cannot hide a difference of value.
