# BZ Finite-Field Factor Localization

Current compiled diagnostic at revision
`5c371a5abb85ca6ef6510ec60888f3048db71719`, 2026-07-28, on
`chungus2`, pinned to CPU 0.

The capture records a dirty worktree because the benchmark registrations and
reports were being repaired together; the measured library revision is the
full hash above.

## Current Cost Shape

The kernel-sharing optimization remains decisive on fully split inputs:

| Degree | Rebuilding baseline | Shared baseline | Fixed factor path |
|---:|---:|---:|---:|
| 6 | 165.135 µs | 44.235 µs | 30.766 µs |
| 12 | 1.367 ms | 215.309 µs | 118.636 µs |
| 18 | 5.672 ms | 598.949 µs | 289.440 µs |
| 24 | 16.077 ms | 1.280 ms | 577.347 µs |

At degree 24, the fixed path spends 18.18% in matrix construction, 2.84% in
nullspace computation, and 78.99% in witness splitting. Within the detailed
witness profile, GCD work accounts for 430.124 µs of the 507.573 µs profiled
total. That separately instrumented total is 9.1% above the 465.380 µs
end-to-end witness baseline, so its phase shares are interpreted only within
the instrumented run. The remaining performance frontier is therefore witness
splitting and GCD work, not matrix inversion or nullspace construction.

Reduced-witness caching is neutral on the fully split ladder:
465.380 µs baseline versus 465.231 µs cached at degree 24. It helps the
`SD_4` witness phase modestly, from 262.950 µs to 237.623 µs.

## Production Context

The standalone finite-field suite remains consistent with its declared models:
Berlekamp factorization takes 3.388 ms at its largest degree-256 rung;
matrix construction takes 10.776 ms at degree 192. Rabin and DDF remain much
slower than their FLINT comparators, as documented in
`hex-berlekamp-performance.md`.

Raw stdout:
`reports/bench-results/berlekamp-diagnostic-5c371a5a-chungus2.txt`
(SHA-256
`c79c0167c402c714fbd664e3157236fc5aa1f426a67f83b9f1250a5e5135c364`).

## Reproducing

```sh
taskset -c 0 env RELIFT_PROFILE=berlekamp \
  .lake/build/bin/hex_recursive_relift_spike
```
