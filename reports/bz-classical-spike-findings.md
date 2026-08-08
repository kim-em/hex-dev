# Classical BZ Spike Findings

Current diagnostic run for the exact-exponent/factor-only implementation over
base revision `b4b3675472f58958c9c2f9b2ab2f7aae16c3dc62`, 2026-07-29, on
`chungus2`, pinned to CPU 0.

The capture records a dirty worktree because the runtime patch, benchmark
labels, and reports were pending over the stated base.

## Factor-only final correction

Sixteen shifted-linear inputs were measured per degree.

| Degree | Production Mignotte | Full-witness Mignotte | Production `k=4` | Full-witness `k=4` |
|---:|---:|---:|---:|---:|
| 8 | 208.053 µs | 219.928 µs | 144.864 µs | 152.690 µs |
| 12 | 525.872 µs | 663.705 µs | 276.286 µs | 293.029 µs |
| 16 | 1.192 ms | 1.789 ms | 493.226 µs | 520.152 µs |
| 20 | 2.012 ms | 2.892 ms | 797.602 µs | 847.893 µs |
| 24 | 4.506 ms | 5.837 ms | 1.241 ms | 1.274 ms |

Both columns use the same balanced product-tree shape. Production skips the
unused final Bezout update at every split node, while the full-witness
reference calls `henselLiftQuadratic` throughout. The factor-only surface is
1.30× faster at the degree-24 Mignotte rung and 1.03× faster at `k=4`.

## Hybrid and Lattice Seam

| Fixture | Hybrid wall time | Answering tier | Lattice-core wall time |
|---|---:|---|---:|
| reducible degree 4 | 107.269 µs | classical | 128.320 µs |
| `SD_2` | 41.050 µs | classical | 212.225 µs |
| `Phi_15` | 108.891 µs | classical | 275.598 µs |
| `SD_3` | 214.488 µs | classical | 1.622 ms |
| `SD_4` | 1.190 ms | classical | 28.722 ms |
| `SD_5` | 100.706 ms | classical | 231.403 ms |
| `SD_6` | 9.132 s | lattice decline | 8.257 s |

The production dispatcher handles `SD_2` through `SD_5` in the classical
tier. `SD_6` reaches the lattice tier, declines, and returns the irreducible
fallback; the persistent public corpus service nevertheless completes `sd6`
inside its 10-second cutoff.

This seam table is single-shot process output. It is not directly comparable
with the warm auto-tuned fixed benchmarks (`SD_3` 1.624 ms and `SD_4`
29.573 ms): the single-shot path includes startup and measurement noise, so a
narrower core can still show a larger absolute time.

Raw stdout:
`reports/bench-results/bz-spikes-b4b36754-exact-factor-only-chungus2.txt`
(SHA-256
`1e63599da4da285708b9ac2a6b06fbbb3986b7d418f3452b374682306b3f7efb`).

## Reproducing

```sh
lake build hex_classical_spike hex_lattice_spike
taskset -c 0 .lake/build/bin/hex_classical_spike
taskset -c 0 .lake/build/bin/hex_lattice_spike hybrid
taskset -c 0 .lake/build/bin/hex_lattice_spike core
```
