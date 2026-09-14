# HexGenericRank performance

## Registered workloads and ceilings

The `symbolic` family registers producer and compiled checker separately for
all 216 combinations of dimensions 2/4/8, variables 1/2/4/8, factor support caps
1/4/16 and total degree caps 1/2/4, at full and low rank (432 registrations).
Each fixed mode-3 registration has a preregistered 5 second per-call ceiling,
five measured repeats and a 1 millisecond inner-loop floor. Checker certificates
are prepared before its timer. Each fixed workload uses lean-bench's registered repeat schedule.

Full-rank inputs have a polynomial first row and the remaining identity rows.
Low-rank inputs factor through rank n/2; their leading block is diagonal with
one polynomial diagonal entry. These are structured support-growth workloads,
not a model for worst-case minor swell. Support/degree labels bound the factor
polynomials; multiplication can increase realised entry support and degree.
Untimed instrumentation records the maximum entry support across both actual
producer passes, including the augmented pivot block.

Comparator: **no-comparable-surface-in-named-comparator**. python-flint has no
multivariate polynomial matrix surface; SymPy is used only as an exact oracle.

## Retained compiled measurements

The shared host was chungus2 (AMD EPYC 9455, Linux, Lean 4.34.0-rc2), pinned
to automatically selected logical CPU 5. The five-repeat sweep completed all
432 registrations. No completed repeat was removed and no repeat was retried.
The host load changed from 4.95 to 24.62 during the run; those observations are
context, not sample rejection criteria.

Ranges below are the minimum and maximum of the five-repeat medians across
variable, degree and factor-support rungs, in milliseconds.

| Rank family | Dimension | Producer median range (ms) | Checker median range (ms) |
|---|---:|---:|---:|
| full | 2 | 0.009–4.352 | 0.006–3.753 |
| full | 4 | 0.067–44.202 | 0.023–7.512 |
| full | 8 | 0.464–253.168 | 0.108–29.500 |
| low | 2 | 0.002–9.651 | 0.004–20.259 |
| low | 4 | 0.017–71.862 | 0.012–84.461 |
| low | 8 | 0.137–664.417 | 0.049–354.633 |

The largest individual observed call was 683 ms, below the preregistered
5 s ceiling. The largest producer median was 664 ms on low.n8.k8.d2.s16;
the largest checker median was 355 ms on the same workload. These are
absolute observations for the registered structured inputs, not asymptotic
evidence about general polynomial matrices.

The certificate denominator has at most 16 terms and degree at most 4;
the adjugate has at most 225 terms, and the largest serialized certificate
is 5,685 bytes. Maximum realised entry support and intermediate support are
both 108. The per-workload JSONL records all four certificate-size dimensions
and the peak support across both producer passes.

Raw evidence: [all repeats](data/hex-generic-rank-compiled.json.gz),
[host and command](data/hex-generic-rank-context.json),
[certificate/support statistics](data/hex-generic-rank-statistics.jsonl).
The sweep began at d5a36ad737 and continued across 2870e70e0; the computational
library and benchmark sources are identical at both commits. The latter
changes only companion proofs, tests and documentation. Every row retains
its observed commit and dirty state.

Reproduce after `lake build hexgenericrank_bench` with
`taskset -c "$(python3 scripts/bench/idle_core.py)" .lake/build/bin/hexgenericrank_bench run --tag symbolic --export-file /tmp/generic-rank.json`.
Collect sizes with `.lake/build/bin/hexgenericrank_bench stats`.

## Representative attribution

A separate 499 Hz `perf` profile of full.n8.k8.d4.s16.producer on automatically
selected CPU 15 retained 609 of 628 samples inside the benchmark's monotonic
operation regions. This profile is attribution only; its durations are not
benchmark observations. Allocation/free/reference-count functions account for
47.9% of retained leaf samples, closure application for 10.7%, monomial degree
and order comparison for 13.0%, and list/vector conversion and traversal for
19.0%. The cost is dominated by representation and polynomial-order work,
consistent with measuring realised support rather than claiming a uniform
cubic wall-time model. Worker-thread call chains were unavailable, so the
report makes leaf-cost claims only.

[Profile summary and capture command](data/hex-generic-rank-profile.json) and
[all symbolized leaf samples](data/hex-generic-rank-profile-leaves.txt.gz) retain
the attribution. The raw perf file has SHA-256
`71f252fe4d480be50118be44c23210b027afd8e0c219b6b31e43514caed7a83f`.
