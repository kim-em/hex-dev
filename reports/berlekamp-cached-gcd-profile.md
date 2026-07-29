# Berlekamp Cached-GCD Profile

Current compiled diagnostic at revision
`a1fdbd81ef038faa41765fb39a79cd083109c8ed`, 2026-07-29, on
`chungus2`, pinned to CPU 0.

The capture records a dirty worktree because the benchmark registrations and
reports were being repaired together; the measured library revision is the
full hash above.

This compares the baseline witness split with the reduced-witness cached
variant. Output checksums agreed in every row.

| Fixture | Baseline | Cached | Baseline/cached |
|---|---:|---:|---:|
| split degree 6 | 18.558 µs | 18.678 µs | `0.994x` |
| split degree 12 | 83.614 µs | 83.614 µs | `1.000x` |
| split degree 18 | 216.882 µs | 216.581 µs | `1.001x` |
| split degree 24 | 453.402 µs | 453.703 µs | `0.999x` |
| `Phi_15` | 8.683 µs | 8.713 µs | `0.997x` |
| `SD_3` | 38.097 µs | 36.203 µs | `1.052x` |
| `SD_4` | 261.758 µs | 236.521 µs | `1.107x` |

Caching is neutral on the fully split family and gives only a modest win on
`SD_4`; it is not the primary optimization lever.

Raw stdout:
`reports/bench-results/berlekamp-diagnostic-a1fdbd81-chungus2.txt`
(SHA-256
`76f28eb9e779f4672a3138c8167de2d6849b28a899609bff19227a378151af52`).

Reproduce with:

```sh
taskset -c 0 env RELIFT_PROFILE=berlekamp \
  .lake/build/bin/hex_recursive_relift_spike
```
