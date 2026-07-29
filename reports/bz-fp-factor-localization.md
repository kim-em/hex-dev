# BZ Finite-Field Factor Localization

Current compiled diagnostic at revision
`a1fdbd81ef038faa41765fb39a79cd083109c8ed`, 2026-07-29, on
`chungus2`, pinned to CPU 0.

The capture records a dirty worktree because the benchmark registrations and
reports were being repaired together; the measured library revision is the
full hash above.

## Current Cost Shape

The kernel-sharing optimization remains decisive on fully split inputs:

| Degree | Rebuilding baseline | Shared baseline | Fixed factor path |
|---:|---:|---:|---:|
| 6 | 166.246 µs | 43.685 µs | 30.415 µs |
| 12 | 1.374 ms | 206.766 µs | 116.122 µs |
| 18 | 5.736 ms | 579.529 µs | 285.233 µs |
| 24 | 16.387 ms | 1.245 ms | 569.224 µs |

At degree 24, the fixed path spends 18.89% in matrix construction, 2.95% in
nullspace computation, and 78.17% in witness splitting. Within the detailed
witness profile, GCD work accounts for 419.554 µs of the 495.815 µs profiled
total. That separately instrumented total is 9.4% above the 453.402 µs
end-to-end witness baseline, so its phase shares are interpreted only within
the instrumented run. The remaining performance frontier is therefore witness
splitting and GCD work, not matrix inversion or nullspace construction.

Reduced-witness caching is neutral on the fully split ladder:
453.402 µs baseline versus 453.703 µs cached at degree 24. It helps the
`SD_4` witness phase modestly, from 261.758 µs to 236.521 µs.

## Production Context

The standalone finite-field suite remains consistent with its declared models:
Berlekamp factorization takes 3.271 ms at its largest degree-256 rung;
matrix construction takes 10.791 ms at degree 192. Rabin and DDF remain much
slower than their FLINT comparators, as documented in
`hex-berlekamp-performance.md`.

Raw stdout:
`reports/bench-results/berlekamp-diagnostic-a1fdbd81-chungus2.txt`
(SHA-256
`03e59491ed588ca377ece2ef387450ba699ef9e63d323db50e6c36fa17f265b5`).

## Reproducing

```sh
taskset -c 0 env RELIFT_PROFILE=berlekamp \
  .lake/build/bin/hex_recursive_relift_spike
```
