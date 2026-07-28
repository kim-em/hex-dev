# Berlekamp Cached-GCD Profile

Current compiled diagnostic at revision
`5c371a5abb85ca6ef6510ec60888f3048db71719`, 2026-07-28, on
`chungus2`, pinned to CPU 0.

This compares the baseline witness split with the reduced-witness cached
variant. Output checksums agreed in every row.

| Fixture | Baseline | Cached | Baseline/cached |
|---|---:|---:|---:|
| split degree 6 | 18.788 µs | 18.898 µs | `0.994x` |
| split degree 12 | 86.348 µs | 86.379 µs | `1.000x` |
| split degree 18 | 222.450 µs | 222.300 µs | `1.001x` |
| split degree 24 | 465.380 µs | 465.231 µs | `1.000x` |
| `Phi_15` | 8.723 µs | 8.713 µs | `1.001x` |
| `SD_3` | 38.958 µs | 36.915 µs | `1.055x` |
| `SD_4` | 262.950 µs | 237.623 µs | `1.107x` |

Caching is neutral on the fully split family and gives only a modest win on
`SD_4`; it is not the primary optimization lever.

Reproduce with:

```sh
taskset -c 0 env RELIFT_PROFILE=berlekamp \
  .lake/build/bin/hex_recursive_relift_spike
```
