# Berlekamp Factor Phase Profile

Current compiled diagnostic at revision
`a1fdbd81ef038faa41765fb39a79cd083109c8ed`, 2026-07-29, on
`chungus2`, pinned to CPU 0.

The capture records a dirty worktree because the benchmark registrations and
reports were being repaired together; the measured library revision is the
full hash above.

The rebuilding baseline reconstructs the kernel for each basis vector. The
shared baseline builds it once. The fixed path is the current optimized
implementation.

| Fixture | Rebuilding baseline | Shared baseline | Fixed path | Rebuild/fixed |
|---|---:|---:|---:|---:|
| split degree 6 | 166.246 µs | 43.685 µs | 30.415 µs | `5.47x` |
| split degree 12 | 1.374 ms | 206.766 µs | 116.122 µs | `11.83x` |
| split degree 18 | 5.736 ms | 579.529 µs | 285.233 µs | `20.11x` |
| split degree 24 | 16.387 ms | 1.245 ms | 569.224 µs | `28.79x` |
| `Phi_15` | 217.122 µs | 55.643 µs | 55.632 µs | `3.90x` |
| `SD_3` | 328.687 µs | 73.179 µs | 71.226 µs | `4.61x` |
| `SD_4` | 4.963 ms | 445.701 µs | 420.854 µs | `11.79x` |

The dominant avoided work is repeated kernel reconstruction. The optimized
path is close to the shared baseline on low-split fixtures and substantially
better on fully split families.

Raw stdout:
`reports/bench-results/berlekamp-diagnostic-a1fdbd81-chungus2.txt`
(SHA-256
`76f28eb9e779f4672a3138c8167de2d6849b28a899609bff19227a378151af52`).

Reproduce with:

```sh
taskset -c 0 env RELIFT_PROFILE=berlekamp \
  .lake/build/bin/hex_recursive_relift_spike
```
