# Exact root-count comparison against degree

The compiled ladder uses Chebyshev `T_n`, query one, and the open interval
`(-2,2)`, with degrees 4, 8, 16, 32 and 64. Every backend returns the complete
exact count `n`; expected-result guards and paired `Option Int` hashes check
that observable. Coefficient height grows with degree in this family, so this
is not an experiment holding all other input dimensions constant.

Hex calls the shipped rational Sturm query, including its domain/chain
checks. The pinned Z3 RCF and FLINT qqbar drivers produce real roots, filter
the interval, evaluate the constant query and sum signs. Inputs and contexts
are prepared before timing. Each child warms up once; root production or
chain construction, JSON transport and temporary cleanup remain timed.
The drivers cache coefficients/contexts, not roots. Backends may retain
internal caches within a batch. Protocol controls have the same count payload.

[capture.py](capture.py) uses one automatically leased CPU on the shared
host, four fixed trial-major blocks, and adjacent native/external arms with
alternating AB/BA order. It retains all completed, failed and censored
observations. It refuses to overwrite an existing collection. The schedule
and 50 ms batching floor are fixed before collection; no quiet-core preflight,
load rejection or unchanged rerun is used. An exact executable copy and raw
records also go to persistent host storage.

[analyze.py](analyze.py) joins the complete hash-checked pairs and displays
elapsed time and raw/protocol-adjusted ratios. Protocol adjustment is a
framing control, not an isolated pure-algorithm time. No fitted exponent,
complexity admission, absolute budget or phase advancement is claimed.
