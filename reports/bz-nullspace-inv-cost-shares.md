# Berlekamp Matrix, Nullspace, and Split Cost Shares

Current compiled diagnostic at revision
`5c371a5abb85ca6ef6510ec60888f3048db71719`, 2026-07-28, on
`chungus2`, pinned to CPU 0.

The capture records a dirty worktree because the benchmark registrations and
reports were being repaired together; the measured library revision is the
full hash above.

Shares below are within the current fixed Berlekamp factorization path.

| Fixture | Matrix | Nullspace | Witness split | Fixed total |
|---|---:|---:|---:|---:|
| split degree 6 | 34.37% | 6.68% | 58.95% | 30.766 µs |
| split degree 12 | 24.47% | 4.96% | 70.57% | 118.636 µs |
| split degree 18 | 21.20% | 4.04% | 74.76% | 289.440 µs |
| split degree 24 | 18.18% | 2.84% | 78.99% | 577.347 µs |
| `Phi_15` | 53.79% | 30.00% | 16.21% | 55.112 µs |
| `SD_3` | 38.81% | 10.28% | 50.91% | 71.587 µs |
| `SD_4` | 32.60% | 10.38% | 57.02% | 414.275 µs |

The nullspace is not the dominant cost on the fully split ladder; its share
falls below 3% by degree 24. Witness splitting dominates there. On `Phi_15`,
matrix plus nullspace accounts for most of the much smaller fixed total.

Raw stdout:
`reports/bench-results/berlekamp-diagnostic-5c371a5a-chungus2.txt`
(SHA-256
`c79c0167c402c714fbd664e3157236fc5aa1f426a67f83b9f1250a5e5135c364`).

Reproduce with:

```sh
taskset -c 0 env RELIFT_PROFILE=berlekamp \
  .lake/build/bin/hex_recursive_relift_spike
```
