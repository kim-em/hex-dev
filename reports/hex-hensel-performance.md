# HexHensel Performance Report

Current at revision `a1fdbd81ef038faa41765fb39a79cd083109c8ed`,
measured 2026-07-29 on `chungus2` (AMD EPYC 9455, Linux x86-64), pinned to
CPU 0.

The export records a dirty worktree because the borrowed-extern ownership fix,
fresh artifacts, and reports were pending together. Generated C confirms that
all object arguments are borrowed, and the quadratic ladders now stay near
66–69 MB RSS instead of growing with the inner-repeat count.

## Verdicts

| Target | Model | Largest rung | Median | Verdict |
|---|---|---:|---:|---|
| Reduce mod `p` | `n` | 131072 | 9.343 ms | consistent |
| Lift to `Z` | `n` | 131072 | 2.619 ms | consistent |
| Reduce mod `p^k` | `n` | 131072 | 10.276 ms | consistent |
| Linear step | `n²` | 512 | 15.089 ms | consistent |
| Iterated linear lift | `n²k` | `(192,64)` | 142.543 ms | inconclusive |
| Quadratic step | `n²` | 512 | 8.681 ms | consistent |
| Product | `n²` | 1024 | 158.092 ms | consistent |
| Linear multifactor | `n²k` | `(192,64)` | 143.939 ms | inconclusive |
| Quadratic multifactor | `n² log k` | `(192,64)` | 89.522 ms | inconclusive |

The packed verified kernels are visible most clearly in the quadratic rows:
the degree-512 quadratic step fell from 128.731 ms to 8.681 ms (14.8×), and
quadratic multifactor lifting at `(192,64)` fell from 145.140 ms to
89.522 ms (1.62×). Linear lifting and product construction are essentially
unchanged.

Raw export:
`reports/bench-results/hex-hensel-a1fdbd81-chungus2.json` (SHA-256
`0bd78e60348a1ab7c4ffe1e6368ea05d96933411badaa5211ab7a3bf118b706a`).
`list` and `verify` passed.

The covered input families are `bridge-operations`, `linear-hensel`,
`quadratic-hensel`, and `multifactor-lifting`.

## External Comparator Status

The declared comparator is `FLINT nmod_poly_hensel_lift_* via python-flint`.
The five python-flint comparator exports from 2026-07-28 remain valid records
of their fixtures and FLINT 0.9.0 timings, but their embedded Hex side predates
the packed quadratic kernels. They are retained under
`reports/bench-results/hex-hensel-*-flint-5c371a5a-chungus2.json` and are not
presented as current ratios here. python-flint does not bind native
`nmod_poly_hensel_lift_*`; the iterated comparator is an `fmpz_poly` emulation
and is not a native-FLINT performance claim.

## Concerns

- The `n²k` iterated-linear verdicts remain inconclusive on the mixed
  degree/precision schedule.
- The quadratic-multifactor model is now inconclusive because the optimized
  high-precision rung changes the observed ladder shape.
- A current native-FLINT Hensel comparison still needs bindings that
  python-flint does not expose.
