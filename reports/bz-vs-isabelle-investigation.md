# BZ Versus Isabelle Investigation

This comparison pairs the fresh Hex revision
`a1fdbd81ef038faa41765fb39a79cd083109c8ed` (2026-07-29) with the
already-current Isabelle2025-2 / AFP 2026-05-29 exports (2026-07-28). Both
were measured on `chungus2`, pinned to CPU 0, against the same 392-row corpus
and warm persistent-service protocol. The external export was not rerun
because the implementation change is confined to Hex.

Measured protocol overhead was 16.905 µs for Hex public, 19.219 µs for Hex
lattice, 18.347 µs for Hex classical, 17.777 µs for Isabelle BZ, and
17.136 µs for Isabelle LLL.

## Corpus frontiers

| System | Solved / 392 | Solved-row median | p90 | Slowest solved |
|---|---:|---:|---:|---:|
| Hex public factor | 373 | 460.392 µs | 9.191 ms | 9.747 s |
| Hex lattice | 366 | 1.864 ms | 89.351 ms | 9.612 s |
| Hex classical, no decline | 371 | 424.409 µs | 9.484 ms | 3.918 s |
| Verified Isabelle BZ | 371 | 441.134 µs | 5.128 ms | 8.363 s |
| Verified Isabelle LLL | 314 | 6.109 ms | 1.219 s | 9.528 s |

Hex public solves `cyclo_phi257`, `cyclo_phi331`, `sd5_x_phi45`, and `sd6`,
where verified BZ times out. Verified BZ solves `cyclo_phi121` and
`cyclo_phi1031`, where Hex public times out. Thus Hex has two more successes,
but the frontiers are not nested.

## Common-row ratios

Ratios divide the per-row median Hex service wall clock by Isabelle's. A row
is eligible only when both medians are at least ten times the larger measured
protocol overhead of the pair.

| Pair | Common solved | Eligible | Median ratio | p10–p90 | Hex faster | Isabelle faster |
|---|---:|---:|---:|---:|---:|---:|
| Hex public / verified BZ | 369 | 234 | 1.09x | 0.48x–3.60x | 108 | 126 |
| Hex classical / verified BZ | 369 | 231 | 1.26x | 0.50x–3.39x | 92 | 139 |
| Hex lattice / verified LLL | 313 | 228 | 0.15x | 0.004x–2.55x | 175 | 53 |

The former 3.95× public/BZ median gap is now 1.09×. That is near parity, not
an overall win: Isabelle BZ is faster on 126 eligible rows versus Hex's 108,
and the family medians remain mixed. Hex public is faster by family median on
Conway, cyclotomic products, signed-digit products, Swinnerton-Dyer, and
Wilkinson; Isabelle leads on Chebyshev, cyclotomic, Laguerre, Legendre, and
random products.

The eligible set is smaller than the old 247-row set because some newly faster
Hex rows fell below the 10× overhead floor. The direction is conservative for
Hex, but the 3.95× and 1.09× medians are therefore not computed over identical
row sets.

The lattice entry point remains substantially faster than verified Isabelle
LLL on its median eligible row, but it solves fewer rows and has a heavy tail.
The broad percentile bands and non-identical timeout frontiers make any single
aggregate ratio inadequate as a release gate.

Every factor-degree check against a committed corpus oracle passed. See
`hexbz-factor-sweep.md` for all eight systems, plots, and artifact provenance.
