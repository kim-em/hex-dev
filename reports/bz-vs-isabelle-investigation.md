# BZ Versus Isabelle Investigation

This comparison pairs the exact-exponent/factor-only Hex implementation over
base revision `b4b3675472f58958c9c2f9b2ab2f7aae16c3dc62` (2026-07-29) with
the already-current Isabelle2025-2 / AFP 2026-05-29 exports (2026-07-28).
The lattice and no-decline classical rows come from current revision
`aaabcf1520121b4acaa793811c8567dddcf39f1f`. All were measured on `chungus2`,
pinned to CPU 0, against the same 392-row corpus and warm persistent-service
protocol. The external export was not rerun because the implementation change
is confined to Hex.

The Hex artifact records `git_dirty = true`: the measured worktree differs
from its stated base only by the exact-exponent and factor-only Hensel patch
reported here. Measured protocol overhead was 17.196 µs for Hex public,
19.118 µs for Hex lattice, 18.527 µs for Hex classical, 17.777 µs for
Isabelle BZ, and 17.136 µs for Isabelle LLL.

## Corpus frontiers

| System | Solved / 392 | Solved-row median | p90 | Slowest solved |
|---|---:|---:|---:|---:|
| Hex public factor | 373 | 424.039 µs | 5.577 ms | 8.986 s |
| Hex lattice | 369 | 1.957 ms | 91.186 ms | 10.000 s |
| Hex classical, no decline | 372 | 423.939 µs | 9.029 ms | 3.845 s |
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
| Hex public / verified BZ | 369 | 238 | 0.930x | 0.48x–2.91x | 126 | 112 |
| Hex classical / verified BZ | 369 | 231 | 1.21x | 0.48x–3.22x | 93 | 138 |
| Hex lattice / verified LLL | 313 | 230 | 0.15x | 0.004x–2.25x | 176 | 54 |

The former 3.95× public/BZ median gap is now a 7.0% aggregate Hex lead.
This is stronger than parity but not uniform superiority: the family medians
are 2.07× on Chebyshev and 2.13× on Legendre, while Hex leads on Conway
(0.77×), cyclotomic products (0.57×), Laguerre (0.84×), signed-digit products
(0.81×), Swinnerton-Dyer (0.95×), and Wilkinson (0.62×). Isabelle also leads
on cyclotomic (1.10×) and random products (1.19×). FLINT, PARI/GP, and NTL
remain substantially faster overall.

The conclusion does not depend on the new overhead boundary. Reapplying the
preceding, lower 13.650 µs Hex floor gives a 0.904× median over 244 rows;
requiring both systems to clear the larger current pair floor gives 0.944×
over 235 rows. The remaining concern is instead the broad per-family and
per-row spread: the four largest ratios are `legendre_P38` at 5.61×,
`sd5_shift2` at 5.55×, `sd5_shift1` at 5.53×, and `chebyshev_U24` at 5.21×
Hex/Isabelle.

The lattice entry point remains substantially faster than verified Isabelle
LLL on its median eligible row, but it solves fewer rows and has a heavy tail.
The broad percentile bands and non-identical timeout frontiers make any single
aggregate ratio inadequate as a release gate.

Every factor-degree check against a committed corpus oracle passed. See
`hexbz-factor-sweep.md` for all eight systems, plots, and artifact provenance.
The two current Hex inputs are:

- `hexbz-factor-sweep-hex-b4b36754-exact-factor-only-chungus2.json`
  (SHA-256
  `090b594a14b12af8332fef091d2bd8ca5652c3e7566e6bd452a984eb473a058a`);
- `hexbz-factor-sweep-hex-aaabcf15-chungus2.json` (SHA-256
  `30e56da9aa3c6f4f50faca4ef19e5c4d4f6523362542f2d8967ca7665f62f747`).

Both paths are relative to `reports/bench-results/`.
