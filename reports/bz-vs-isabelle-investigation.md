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

The exports record `5c371a5-dirty` because the benchmark registrations and
reports were being repaired in the same worktree; the measured library revision
is the full hash above.

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

Ratios divide the per-row median Hex service wall clock by the corresponding
Isabelle time. Protocol overhead is recorded but not subtracted because several
fast rows fluctuate below the overhead estimate. To keep overhead from
dominating, a row is eligible only when both medians are at least ten times the
larger measured overhead of the pair.

| Pair | Common solved | Eligible | Median ratio | p10–p90 | Hex faster | Isabelle faster |
|---|---:|---:|---:|---:|---:|---:|
| Hex public / verified BZ | 369 | 247 | 3.95x | 0.64x–12.76x | 46 | 201 |
| Hex classical / verified BZ | 369 | 244 | 2.40x | 0.97x–6.84x | 27 | 217 |
| Hex lattice / verified LLL | 313 | 234 | 0.20x | 0.006x–2.93x | 173 | 61 |

Thus the public path is slower than verified BZ on the median common corpus
row with adequate signal, while the Hex lattice entry point is faster than
verified Isabelle LLL on its median eligible row. These filtered comparisons
exclude 122, 125, and 79 common rows respectively. The broad percentile ranges
and differing timeout frontiers make a single aggregate ratio insufficient for
a gating decision. In particular, this corpus comparison is not the SPEC's
largest-eligible-scaling-rung test.

Every current factor-degree check against a committed corpus oracle passed.
See `hexbz-factor-sweep.md` and
`polynomial-factorization-performance.md` for all eight systems and artifact
hashes. The retired startup-contaminated timings remain available only in git
history and must not be reused.
