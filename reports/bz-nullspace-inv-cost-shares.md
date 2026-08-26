# Berlekamp Matrix, Nullspace, and Split Cost Shares

Current compiled diagnostic at revision
`a1fdbd81ef038faa41765fb39a79cd083109c8ed`, 2026-07-29, on
`chungus2`, pinned to CPU 0.

The capture records a dirty worktree because the benchmark registrations and
reports were being repaired together; the measured library revision is the
full hash above.

Shares below are within the current fixed Berlekamp factorization path.

| Fixture | Matrix | Nullspace | Witness split | Fixed total |
|---|---:|---:|---:|---:|
| split degree 6 | 34.61% | 6.62% | 58.77% | 30.415 µs |
| split degree 12 | 25.23% | 4.90% | 69.87% | 116.122 µs |
| split degree 18 | 21.99% | 3.82% | 74.19% | 285.233 µs |
| split degree 24 | 18.89% | 2.95% | 78.17% | 569.224 µs |
| `Phi_15` | 54.89% | 29.61% | 15.50% | 55.632 µs |
| `SD_3` | 40.54% | 9.80% | 49.66% | 71.226 µs |
| `SD_4` | 33.68% | 10.46% | 55.86% | 420.854 µs |

The nullspace is not the dominant cost on the fully split ladder; its share
is about 3% by degree 24. Witness splitting dominates there. On `Phi_15`,
matrix plus nullspace accounts for most of the much smaller fixed total.

Raw stdout:
`reports/bench-results/berlekamp-diagnostic-a1fdbd81-chungus2.txt`
(SHA-256
`03e59491ed588ca377ece2ef387450ba699ef9e63d323db50e6c36fa17f265b5`).

Reproduce with:

```sh
taskset -c 0 env RELIFT_PROFILE=berlekamp \
  .lake/build/bin/hex_recursive_relift_spike
```
