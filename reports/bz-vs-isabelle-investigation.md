# BZ Versus Isabelle Investigation

This comparison pairs the exact-exponent/factor-only Hex implementation and
guarded dominant-degree tree at
`53bb12e21c5107e9da5d837c207eb3254238967f` (2026-07-29) with
the already-current Isabelle2025-2 / AFP 2026-05-29 exports (2026-07-28).
All three Hex rows come from that revision. All were measured on `chungus2`,
pinned to CPU 0, against the same 392-row corpus and warm persistent-service
protocol. The external export was not rerun because the implementation change
is confined to Hex.

The Hex artifact records a clean worktree. Measured protocol overhead was
16.905 µs for Hex public,
19.039 µs for Hex lattice, 18.287 µs for Hex classical, 17.777 µs for
Isabelle BZ, and 17.136 µs for Isabelle LLL.

## Corpus frontiers

| System | Solved / 392 | Solved-row median | p90 | Slowest solved |
|---|---:|---:|---:|---:|
| Hex public factor | 373 | 420.153 µs | 5.302 ms | 9.077 s |
| Hex lattice | 369 | 1.838 ms | 87.386 ms | 9.901 s |
| Hex classical, no decline | 372 | 401.736 µs | 7.184 ms | 3.818 s |
| Verified Isabelle BZ | 371 | 441.134 µs | 5.128 ms | 8.363 s |
| Verified Isabelle LLL | 314 | 6.109 ms | 1.219 s | 9.528 s |

Hex public solves `cyclo_phi257`, `cyclo_phi331`, `sd5_x_phi45`, and `sd6`,
where verified BZ times out. Verified BZ solves `cyclo_phi121` and
`cyclo_phi1031`, where Hex public times out. Thus Hex has two more successes,
but the frontiers are not nested.

## Common-row ratios

Ratios divide the per-row median Hex service wall clock by Isabelle's. A row
is eligible only when each median is at least ten times its service's measured
protocol overhead.

| Pair | Common solved | Eligible | Median ratio | p10–p90 | Hex faster | Isabelle faster |
|---|---:|---:|---:|---:|---:|---:|
| Hex public / verified BZ | 369 | 238 | 0.909x | 0.47x–2.64x | 127 | 111 |
| Hex classical / verified BZ | 369 | 231 | 1.04x | 0.48x–2.78x | 110 | 121 |
| Hex lattice / verified LLL | 313 | 229 | 0.14x | 0.005x–2.29x | 178 | 51 |

The former 3.95× public/BZ median gap is now a 9.1% aggregate Hex lead.
This is stronger than parity but not uniform superiority: the family medians
are 2.05× on Chebyshev and 1.85× on Legendre, while Hex leads on Conway
(0.76×), cyclotomic products (0.58×), Laguerre (0.80×), signed-digit products
(0.82×), Swinnerton-Dyer (0.86×), and Wilkinson (0.62×). Isabelle also leads
on cyclotomic (1.10×) and random products (1.17×). FLINT, PARI/GP, and NTL
remain substantially faster overall.

The conclusion does not depend on the new overhead boundary. Reapplying the
preceding, lower 13.650 µs Hex floor gives a 0.892× median over 244 rows;
requiring both systems to clear the larger current pair floor gives 0.916×
over 236 rows. The remaining concern is instead the broad per-family and
per-row spread: the four largest ratios are `sd5_shift2` at 5.31×,
`sd5_shift1` at 5.25×, `cyclo_phi24_x_phi35` at 4.52×, and
`conway_p2_n38` at 4.28× Hex/Isabelle.

The lattice entry point remains substantially faster than verified Isabelle
LLL on its median eligible row, but it solves fewer rows and has a heavy tail.
The broad percentile bands and non-identical timeout frontiers make any single
aggregate ratio inadequate as a release gate.

Every factor-degree check against a committed corpus oracle passed. See
`hexbz-factor-sweep.md` for all eight systems, plots, and artifact provenance.
The current Hex input is:

- `hexbz-factor-sweep-hex-53bb12e2-guarded-tree-all-chungus2.json`
  (SHA-256
  `926e91245e45523a40e8b915004bf4e0e17f01ed3547feca94589760d3e55e27`).

The path is relative to `reports/bench-results/`.
