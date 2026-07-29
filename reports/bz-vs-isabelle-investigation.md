# BZ Versus Isabelle Investigation

This comparison pairs the exact-exponent/factor-only Hex implementation,
guarded dominant-degree tree, remainder-only GCD, cached finite-field inverses,
and linear monomial Hensel kernel at
`0b95505b7c926911a9f487bac56676a8c7da48f6` (2026-07-29) with
the already-current Isabelle2025-2 / AFP 2026-05-29 exports (2026-07-28).
All three Hex rows come from that revision. All were measured on `chungus2`,
pinned to CPU 0, against the same 392-row corpus and warm persistent-service
protocol. The external export was not rerun because the implementation change
is confined to Hex.

The Hex artifacts record clean worktrees. Measured protocol overhead was
16.975 µs for Hex public,
18.848 µs for Hex lattice, 18.448 µs for Hex classical, 17.777 µs for
Isabelle BZ, and 17.136 µs for Isabelle LLL.

## Corpus frontiers

| System | Solved / 392 | Solved-row median | p90 | Slowest solved |
|---|---:|---:|---:|---:|
| Hex public factor | 373 | 400.334 µs | 4.082 ms | 9.047 s |
| Hex lattice | 369 | 1.812 ms | 87.886 ms | 9.590 s |
| Hex classical, no decline | 372 | 389.203 µs | 5.561 ms | 3.724 s |
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
| Hex public / verified BZ | 369 | 234 | 0.887x | 0.454x–2.513x | 135 | 99 |
| Hex classical / verified BZ | 369 | 229 | 0.913x | 0.464x–2.568x | 128 | 101 |
| Hex lattice / verified LLL | 313 | 230 | 0.137x | 0.004x–2.437x | 182 | 48 |

The former 3.95× public/BZ median gap is now an 11.3% aggregate Hex lead.
This is clear aggregate superiority but not uniform superiority: the family
medians are 1.64× on Chebyshev and 1.49× on Legendre, while Hex leads on Conway
(0.75×), cyclotomic products (0.57×), Laguerre (0.79×), signed-digit products
(0.78×), Swinnerton-Dyer (0.82×), and Wilkinson (0.60×). Cyclotomic is near
parity (1.04×), and random products slightly favour Hex (0.98×). FLINT,
PARI/GP, and NTL remain substantially faster overall.

The conclusion does not depend on the new overhead boundary. Reapplying the
preceding, lower 13.650 µs Hex floor gives a 0.836× median over 243 rows;
requiring both systems to clear the larger current pair floor gives 0.889×
over 233 rows. On the preceding fixed 238-row eligibility set the current
median is 0.870×. The remaining concern is instead the broad per-family and
per-row spread: the largest ratios still include `sd5_shift2` at 5.16× and
`sd5_shift1` at 5.12× Hex/Isabelle.

The lattice entry point remains substantially faster than verified Isabelle
LLL on its median eligible row, but it solves fewer rows and has a heavy tail.
The broad percentile bands and non-identical timeout frontiers make any single
aggregate ratio inadequate as a release gate.

Every factor-degree check against a committed corpus oracle passed. See
`hexbz-factor-sweep.md` for all eight systems, plots, and artifact provenance.
The current Hex input is:

- `hexbz-factor-sweep-hex-0b95505b-gcd-hensel-final-chungus2.json`
  (public, lattice, and no-decline classical; SHA-256
  `9f9f63ac9f35b3af6d35e530b085a1a1e47e7d03d958179d7597d7850e59c583`).

The path is relative to `reports/bench-results/`.
