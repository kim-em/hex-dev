# Berlekamp Witness-Split Profile

Current compiled diagnostic at revision
`a1fdbd81ef038faa41765fb39a79cd083109c8ed`, 2026-07-29, on
`chungus2`, pinned to CPU 0.

The capture records a dirty worktree because the benchmark registrations and
reports were being repaired together; the measured library revision is the
full hash above.

| Fixture | Factors visited | Witnesses | Constants | GCD calls | Splits | Baseline |
|---|---:|---:|---:|---:|---:|---:|
| split degree 6 | 11 | 10 | 20 | 20 | 5 | 18.558 µs |
| split degree 12 | 23 | 22 | 77 | 77 | 11 | 83.614 µs |
| split degree 18 | 35 | 34 | 170 | 170 | 17 | 216.882 µs |
| split degree 24 | 47 | 46 | 315 | 315 | 23 | 453.402 µs |
| `Phi_15` | 3 | 6 | 3 | 3 | 1 | 8.683 µs |
| `SD_3` | 7 | 22 | 12 | 12 | 3 | 38.097 µs |
| `SD_4` | 15 | 78 | 42 | 42 | 7 | 261.758 µs |

At split degree 24, the detailed baseline attribution was 3.555 µs reduction,
7.530 µs sweep overhead, 419.554 µs in GCD work, 29.651 µs cofactor work,
and 35.525 µs residual work. Witness splitting, especially GCDs, is therefore
the dominant remaining phase after kernel sharing.

Those separately instrumented stage medians total 495.815 µs, 9.4% above the
453.402 µs end-to-end witness baseline because instrumentation and independent
phase timing add overhead. Phase shares should therefore be interpreted against
the instrumented total.

Raw stdout:
`reports/bench-results/berlekamp-diagnostic-a1fdbd81-chungus2.txt`
(SHA-256
`76f28eb9e779f4672a3138c8167de2d6849b28a899609bff19227a378151af52`).

Reproduce with:

```sh
taskset -c 0 env RELIFT_PROFILE=berlekamp \
  .lake/build/bin/hex_recursive_relift_spike
```
