# Classical BZ Spike Findings

Current diagnostic run at revision
`a1fdbd81ef038faa41765fb39a79cd083109c8ed`, 2026-07-29, on
`chungus2`, pinned to CPU 0.

The capture records a dirty worktree because the benchmark registrations and
reports were being repaired together; the measured library revision is the
full hash above.

## Product Construction

Sixteen shifted-linear inputs were measured per degree.

| Degree | Sequential Mignotte | Balanced Mignotte | Sequential `k=4` | Balanced `k=4` |
|---:|---:|---:|---:|---:|
| 8 | 203.158 µs | 202.281 µs | 147.583 µs | 146.394 µs |
| 12 | 627.422 µs | 626.847 µs | 282.766 µs | 280.679 µs |
| 16 | 2.684 ms | 2.690 ms | 497.219 µs | 495.440 µs |
| 20 | 4.522 ms | 4.510 ms | 823.453 µs | 819.151 µs |
| 24 | 6.557 ms | 6.541 ms | 1.259 ms | 1.257 ms |

Balanced construction is effectively neutral on these fixtures. The precision
schedule matters much more than the product-tree shape.

## Hybrid and Lattice Seam

| Fixture | Hybrid wall time | Answering tier | Lattice-core wall time |
|---|---:|---|---:|
| reducible degree 4 | 82.873 µs | classical | 118.405 µs |
| `SD_2` | 37.736 µs | classical | 156.281 µs |
| `Phi_15` | 105.747 µs | classical | 270.951 µs |
| `SD_3` | 205.655 µs | classical | 1.578 ms |
| `SD_4` | 1.183 ms | classical | 28.557 ms |
| `SD_5` | 96.895 ms | classical | 238.245 ms |
| `SD_6` | 9.087 s | lattice decline | 8.492 s |

The production dispatcher handles `SD_2` through `SD_5` in the classical
tier. `SD_6` reaches the lattice tier, declines, and returns the irreducible
fallback; the persistent public corpus service nevertheless completes `sd6`
inside its 10-second cutoff.

This seam table is single-shot process output. It is not directly comparable
with the warm auto-tuned fixed benchmarks (`SD_3` 1.613 ms and `SD_4`
29.580 ms): the single-shot path includes startup and measurement noise, so a
narrower core can still show a larger absolute time.

Raw stdout: `reports/bench-results/bz-spikes-a1fdbd81-chungus2.txt`
(SHA-256
`cd0cd2c0ecc5c6a3fc6bdd2b08a5f4b114403aa7510fab75048fba4db9c17477`).

## Reproducing

```sh
lake build hex_classical_spike hex_lattice_spike
taskset -c 0 .lake/build/bin/hex_classical_spike
taskset -c 0 .lake/build/bin/hex_lattice_spike hybrid
taskset -c 0 .lake/build/bin/hex_lattice_spike core
```
