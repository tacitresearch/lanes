# bank-web

The bank of `examples/bank` behind a server-rendered page: typed routes, a bridge from requests
to inputs and from outputs to HTML fragments, and htmx in the browser.

```bash
cd examples/bank-web
mkdir -p .lake && ln -s ../../../.lake/packages .lake/packages   # share the fetched dependencies
lake build
lake test                # what the page asks for and what the bridge makes of it
lake exe bankWeb 8080    # serves http://127.0.0.1:8080
```

**The balances last only until the process restarts**, as the bank's do: every account is an
actor, and a restart opens each again at 100. It is here to show the web front of a system of
actors, which is the same whether the actors keep their state or a database does. For a web
application whose data outlives the process, read `examples/counter` (what `lanes new` writes)
and `examples/rookery`.
