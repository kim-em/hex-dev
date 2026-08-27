# HexHensel Performance Report

Current at revision `0b95505b7c926911a9f487bac56676a8c7da48f6`, measured
2026-07-29 on `chungus2` (AMD EPYC 9455, Linux x86-64), pinned to CPU 0.
All nine parametric targets were refreshed together from a clean worktree.

## Verdicts

All nine registrations use **mode 1, two-sided parametric**. Their models are
derived from the intended linear or quadratic lifting algorithm on the
registered degree/precision family, so mode 2's prerequisite — inability to
derive a tight family model — does not hold. The six consistent results pass
mode 1. The three inconclusive results are failed mode-1 results, so Phase 4 is
blocked: the existing mixed schedules have not established the derived
scaling, and no published bound plus dominant-phase attribution has been
supplied for a one-sided reinterpretation. Mode 3 is not justified while the
controlled degree/precision families remain available. Mode 4 does not apply
to these registrations because mode 1 is an honest claim; it simply has not
passed.

| Target | Model | Largest rung | Median | Verdict |
|---|---|---:|---:|---|
| Reduce mod `p` | `n` | 131072 | 9.601 ms | consistent |
| Lift to `Z` | `n` | 131072 | 2.582 ms | consistent |
| Reduce mod `p^k` | `n` | 131072 | 733.006 µs | consistent |
| Linear step | `n²` | 512 | 15.568 ms | consistent |
| Iterated linear lift | `n²k` | `(192,64)` | 145.374 ms | inconclusive |
| Quadratic step | `n²` | 512 | 8.481 ms | consistent |
| Product | `n²` | 1024 | 161.314 ms | consistent |
| Linear multifactor | `n²k` | `(192,64)` | 147.330 ms | inconclusive |
| Quadratic multifactor | `n² log k` | `(192,64)` | 48.711 ms | inconclusive |

The packed verified kernels remain visible in the quadratic row: the
degree-512 step is 15.2× faster than the 128.731 ms pre-kernel record. The new
coefficient-array prime-power reduction lowers its degree-131072 rung from
10.276 ms to 733.006 µs (14.0×), while the shift-and-scale monomial division
kernel lowers quadratic multifactor lifting from 89.522 ms to 48.711 ms
(1.84×). A direct-array implementation of ordinary `modP` was rejected after
a same-code A/B measured 15.194 ms versus 9.677 ms for the retained compiled
path; the clean final measurement is 9.601 ms.

Raw export:
`reports/bench-results/hex-hensel-0b95505b-gcd-hensel-chungus2.json`
(SHA-256
`1ef93fd4fbf93109dcc19e9450935e90bc2d68affbe3d7ccc7902bd637a93f65`).
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

- The `n²k` iterated-linear mode-1 verdicts remain inconclusive on the mixed
  degree/precision schedule, so Phase 4 is blocked.
- The quadratic-multifactor model is now inconclusive because the optimized
  high-precision rung changes the observed ladder shape.
- A current native-FLINT Hensel comparison still needs bindings that
  python-flint does not expose.

The failed mode-1 verdicts and rollback are tracked by
[#9741](https://github.com/kim-em/hex-dev/issues/9741).
