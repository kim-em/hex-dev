# BZ Versus Isabelle Investigation

The prior ratio tables in this investigation have been retired. They mixed
factorization work with comparator-process startup and therefore did not
measure the claimed algorithm ratio.

The current comparison is at revision
`5c371a5abb85ca6ef6510ec60888f3048db71719`, measured 2026-07-28 on
`chungus2` (AMD EPYC 9455), pinned to CPU 0. Isabelle2025-2, AFP
2026-05-29, and GHC 9.10.3 were supplied by a transient Nix environment.
The AFP sessions and standalone Haskell exports were built before timing.
Both extracted comparators then ran as warm persistent line-protocol services;
measured protocol overhead was 17.777 µs for BZ and 17.136 µs for LLL.

## Corpus frontiers

| System | Solved / 392 | Solved-row median | p90 | Slowest solved |
|---|---:|---:|---:|---:|
| Hex public factor | 371 | 1.244 ms | 24.831 ms | 5.016 s |
| Hex lattice | 365 | 2.258 ms | 99.293 ms | 9.540 s |
| Hex classical, no decline | 371 | 1.008 ms | 12.708 ms | 4.032 s |
| Verified Isabelle BZ | 371 | 441.134 µs | 5.128 ms | 8.363 s |
| Verified Isabelle LLL | 314 | 6.109 ms | 1.219 s | 9.528 s |

The two 371-row frontiers are not identical. Hex public solves
`cyclo_phi257` and `cyclo_phi331`, where verified BZ times out; verified BZ
solves `cyclo_phi121` and `cyclo_phi1031`, where Hex public times out.

## Common-row ratios

Ratios below divide the per-row median Hex time by the corresponding Isabelle
time and include only rows where both systems answered before the cutoff.
They therefore describe common solved work, not the missing timeout tails.

| Pair | Common rows | Median ratio | p10–p90 | Hex faster | Isabelle faster |
|---|---:|---:|---:|---:|---:|
| Hex public / verified BZ | 369 | 2.73x | 0.55x–11.81x | 95 | 274 |
| Hex classical / verified BZ | 369 | 1.88x | 0.60x–5.86x | 79 | 290 |
| Hex lattice / verified LLL | 313 | 0.39x | 0.008x–3.85x | 222 | 91 |

Thus the public path is slower than verified BZ on the median common corpus
row, while the Hex lattice entry point is faster than verified Isabelle LLL
on its median common row. The broad percentile ranges and differing timeout
frontiers make a single aggregate ratio insufficient for a gating decision.
In particular, this corpus comparison is not the SPEC's
largest-eligible-scaling-rung test.

Every current factor-degree check against a committed corpus oracle passed.
See `hexbz-factor-sweep.md` and
`polynomial-factorization-performance.md` for all eight systems and artifact
hashes. The retired startup-contaminated timings remain available only in git
history and must not be reused.
