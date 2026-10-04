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


[Results](summary.csv) retain 120 successful observations: 40 exact-hash-matched
native/external pairs and 40 protocol controls, with no failures or censored
points. [Metadata](metadata.json) records source `612b3e591`, leased CPU 69,
source snapshots, pinned interpreter, commands, load context and the exact
persistent executable. Source and executable checks remain unchanged.
[Analysis](analysis.json) retains every arm and paired calculation.

| Degree | Hex median ms (Z3 pairs) | Z3 RCF median ms | FLINT qqbar median ms | Z3 / Hex paired ratio | FLINT / Hex paired ratio |
| --- | ---: | ---: | ---: | ---: | ---: |
| 4 | 0.0351 | 0.0540 | 0.0853 | 1.543 | 2.437 |
| 8 | 0.1027 | 0.1101 | 0.2015 | 1.085 | 1.984 |
| 16 | 0.3382 | 0.3447 | 0.5507 | 1.020 | 1.629 |
| 32 | 1.3006 | 1.8482 | 3.5449 | 1.423 | 2.701 |
| 64 | 5.5980 | 14.8606 | 35.2700 | 2.654 | 6.335 |

Native FLINT-pair medians are recorded separately in the CSV and used in
FLINT ratios; ratios are medians of adjacent pairs, not ratios of the displayed
aggregate medians. Transport is material on the small rungs: at degree 4 it
is 13.0% of the Z3 median and 8.4% of FLINT's. Protocol-adjusted Z3/Hex ratios
at degrees 4, 8, 16, 32 and 64 are 1.343, 1.019, 0.999, 1.417 and 2.653.
Both raw and adjusted curves appear in the [plot](comparison.png), with
[SVG](comparison.svg) and [PDF](comparison.pdf) versions. Time panels include
all observations with observed min–max shading; ratio panels summarize pairs.
These observations make this exact-count family plausibly competitive. They
do not attest growing-query memory use, arbitrary polynomial shapes,
extension depth or canonical real-algebraic arithmetic.
