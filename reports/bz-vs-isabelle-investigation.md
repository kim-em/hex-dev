# BZ Versus Isabelle Investigation

This comparison pairs the exact-exponent/factor-only Hex implementation,
guarded dominant-degree tree, remainder-only GCD, cached finite-field inverses,
and linear monomial Hensel kernel at
`09f7f532338c7be474ac7a696adbc1e43ba77186` (2026-07-29) with
the already-current Isabelle2025-2 / AFP 2026-05-29 exports (2026-07-28).
All three Hex rows come from that revision. All were measured on `chungus2`,
pinned to CPU 0, against the same 392-row corpus and warm persistent-service
protocol. The external export was not rerun because the implementation change
is confined to Hex.

The Hex artifacts record clean worktrees. Measured protocol overhead was
16.976 µs for Hex public,
19.609 µs for Hex lattice, 18.417 µs for Hex classical, 17.777 µs for
Isabelle BZ, and 17.136 µs for Isabelle LLL.

## Corpus frontiers

| System | Solved / 392 | Solved-row median | p90 | Slowest solved |
|---|---:|---:|---:|---:|
| Hex public factor | 373 | 398.571 µs | 4.115 ms | 8.984 s |
| Hex lattice | 369 | 1.884 ms | 87.334 ms | 9.702 s |
| Hex classical, no decline | 372 | 390.399 µs | 6.589 ms | 4.633 s |
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
| Hex public / verified BZ | 369 | 236 | 0.881x | 0.46x–2.50x | 138 | 98 |
| Hex classical / verified BZ | 369 | 234 | 0.980x | 0.46x–2.53x | 119 | 115 |
| Hex lattice / verified LLL | 313 | 227 | 0.134x | 0.004x–2.36x | 178 | 49 |

The former 3.95× public/BZ median gap is now an 11.9% aggregate Hex lead.
This is clear aggregate superiority but not uniform superiority: the family
medians are 1.68× on Chebyshev and 1.55× on Legendre, while Hex leads on Conway
(0.74×), cyclotomic products (0.56×), Laguerre (0.77×), signed-digit products
(0.86×), Swinnerton-Dyer (0.89×), and Wilkinson (0.59×). Cyclotomic is near
parity (1.04×), and random products slightly favour Hex (0.99×). FLINT,
PARI/GP, and NTL remain substantially faster overall.

The conclusion does not depend on the new overhead boundary. Reapplying the
preceding, lower 13.650 µs Hex floor gives a 0.867× median over 243 rows;
requiring both systems to clear the larger current pair floor gives 0.891×
over 232 rows. The remaining concern is instead the broad per-family and
per-row spread: the largest ratios still include `sd5_shift2` at 5.22× and
`sd5_shift1` at 5.17× Hex/Isabelle.

The lattice entry point remains substantially faster than verified Isabelle
LLL on its median eligible row, but it solves fewer rows and has a heavy tail.
The broad percentile bands and non-identical timeout frontiers make any single
aggregate ratio inadequate as a release gate.

Every factor-degree check against a committed corpus oracle passed. See
`hexbz-factor-sweep.md` for all eight systems, plots, and artifact provenance.
The current Hex inputs are:

- `hexbz-factor-sweep-hex-09f7f532-gcd-hensel-public-chungus2.json`
  (public; SHA-256
  `b69ead6e9d194f15413e63f80baf6af91ba827793b180c2117e713a438145a17`),
- `hexbz-factor-sweep-hex-09f7f532-gcd-hensel-lattice-chungus2.json`
  (lattice; SHA-256
  `4ff66a75064ce0171c767a3a175e8581ec1b491d6ba5710297c7fcb7f033f3a3`),
- `hexbz-factor-sweep-hex-09f7f532-gcd-hensel-classical-chungus2.json`
  (no-decline classical; SHA-256
  `6ebff5a43be7d34232dd4c56e9f4463aebd736dc92626cfa7f68858562f224f0`).

The path is relative to `reports/bench-results/`.
