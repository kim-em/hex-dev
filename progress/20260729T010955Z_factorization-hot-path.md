# Polynomial factorization hot path

## Accomplished

- Added allocation-free scalar Montgomery and full-word modular add/sub
  externs, plus packed word-polynomial add/subtract/multiply/multiply-add
  kernels for quadratic Hensel lifting.
- Reused word-polynomial conversions throughout each quadratic lift step and
  proved the optimized surface equal to the existing generic operations.
- Fused content/primitive-part normalization so the coefficient gcd is
  computed once.
- Limited recursive relifting to one useful low-precision probe, skipping it
  entirely when at most three modular factors make the full scan cheap.
- Added a proved, bounded prime look-ahead for coefficient-swell cases with at
  least nine factors at the first good prime. It found modular irreducibility
  certificates that reduced Legendre P18, P20, and P26 by approximately 36%,
  88%, and 58% in production-path checks.
- Added compiled boundary and behavioral conformance guards for the native
  arithmetic, packed polynomials, one-pass normalization, and adaptive prime
  selector.

## Current frontier

- The retained implementation and focused production benchmarks are green.
- A fresh commit-keyed full Hex sweep, report regeneration, independent review,
  and PR validation remain.

## Next step

- Complete the full build/conformance pass, rebase, commit, record the fresh
  Hex-only sweep without rerunning external comparators, and regenerate the
  comparison report and six selected graphs.

## Blockers

- None.
