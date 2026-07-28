# Classical BZ Spike Findings

Current diagnostic run at revision
`5c371a5abb85ca6ef6510ec60888f3048db71719`, 2026-07-28, on
`chungus2`, pinned to CPU 0.

The capture records a dirty worktree because the benchmark registrations and
reports were being repaired together; the measured library revision is the
full hash above.

## Product Construction

Sixteen shifted-linear inputs were measured per degree.

| Degree | Sequential Mignotte | Balanced Mignotte | Sequential `k=4` | Balanced `k=4` |
|---:|---:|---:|---:|---:|
| 8 | 649.502 µs | 653.320 µs | 377.155 µs | 384.496 µs |
| 12 | 1.583 ms | 1.556 ms | 749.313 µs | 745.875 µs |
| 16 | 3.779 ms | 3.793 ms | 1.272 ms | 1.268 ms |
| 20 | 6.133 ms | 6.131 ms | 1.954 ms | 1.935 ms |
| 24 | 8.834 ms | 8.807 ms | 2.840 ms | 2.818 ms |

Balanced construction is effectively neutral on these fixtures. The precision
schedule matters much more than the product-tree shape.

## Hybrid and Lattice Seam

| Fixture | Hybrid wall time | Answering tier | Lattice-core wall time |
|---|---:|---|---:|
| reducible degree 4 | 85.747 µs | classical | 204.093 µs |
| `SD_2` | 102.412 µs | classical | 459.813 µs |
| `Phi_15` | 217.693 µs | classical | 583.516 µs |
| `SD_3` | 752.557 µs | classical | 4.033 ms |
| `SD_4` | 4.540 ms | classical | 52.536 ms |
| `SD_5` | 134.197 ms | classical | 399.583 ms |
| `SD_6` | 9.858 s | lattice decline | 9.158 s |

The production dispatcher handles `SD_2` through `SD_5` in the classical
tier. `SD_6` reaches the lattice tier, declines, and returns the irreducible
fallback.

This seam table is single-shot process output. It is not directly comparable
with the warm auto-tuned fixed benchmarks (`SD_3` 2.596 ms and `SD_4`
34.266 ms): the single-shot path includes startup and measurement noise, so a
narrower core can still show a larger absolute time.

Raw stdout: `reports/bench-results/bz-spikes-5c371a5a-chungus2.txt`
(SHA-256
`fe2c873c73ba29bb7f5193aac976691483505880803cdc0429cb09f1d7b21f1b`).

## Reproducing

```sh
lake build hex_classical_spike hex_lattice_spike
taskset -c 0 .lake/build/bin/hex_classical_spike
taskset -c 0 .lake/build/bin/hex_lattice_spike hybrid
taskset -c 0 .lake/build/bin/hex_lattice_spike core
```
