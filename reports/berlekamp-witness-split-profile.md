# Berlekamp Witness-Split Profile

Current compiled diagnostic at revision
`5c371a5abb85ca6ef6510ec60888f3048db71719`, 2026-07-28, on
`chungus2`, pinned to CPU 0.

The capture records a dirty worktree because the benchmark registrations and
reports were being repaired together; the measured library revision is the
full hash above.

| Fixture | Factors visited | Witnesses | Constants | GCD calls | Splits | Baseline |
|---|---:|---:|---:|---:|---:|---:|
| split degree 6 | 11 | 10 | 20 | 20 | 5 | 18.788 µs |
| split degree 12 | 23 | 22 | 77 | 77 | 11 | 86.348 µs |
| split degree 18 | 35 | 34 | 170 | 170 | 17 | 222.450 µs |
| split degree 24 | 47 | 46 | 315 | 315 | 23 | 465.380 µs |
| `Phi_15` | 3 | 6 | 3 | 3 | 1 | 8.723 µs |
| `SD_3` | 7 | 22 | 12 | 12 | 3 | 38.958 µs |
| `SD_4` | 15 | 78 | 42 | 42 | 7 | 262.950 µs |

At split degree 24, the detailed baseline attribution was 3.515 µs reduction,
7.547 µs sweep overhead, 430.124 µs in GCD work, 30.898 µs cofactor work,
and 35.489 µs residual work. Witness splitting, especially GCDs, is therefore
the dominant remaining phase after kernel sharing.

Those separately instrumented stage medians total 507.573 µs, 9.1% above the
465.380 µs end-to-end witness baseline because instrumentation and independent
phase timing add overhead. Phase shares should therefore be interpreted against
the instrumented total.

Raw stdout:
`reports/bench-results/berlekamp-diagnostic-5c371a5a-chungus2.txt`
(SHA-256
`c79c0167c402c714fbd664e3157236fc5aa1f426a67f83b9f1250a5e5135c364`).

Reproduce with:

```sh
taskset -c 0 env RELIFT_PROFILE=berlekamp \
  .lake/build/bin/hex_recursive_relift_spike
```
