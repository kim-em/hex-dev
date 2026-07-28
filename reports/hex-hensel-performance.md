# HexHensel Performance Report

Current at revision `5c371a5abb85ca6ef6510ec60888f3048db71719`,
measured 2026-07-28 on `chungus2` (AMD EPYC 9455, Linux x86-64),
pinned to CPU 0.

The exports record `5c371a5-dirty` because the benchmark registrations and
reports were being repaired in the same worktree; the measured library revision
is the full hash above.

## Bench Targets

The nine parametric targets cover the coefficient bridges, linear and
quadratic binary steps, iterated lifting, product construction, and the two
multifactor strategies.

## Verdicts

| Target | Model | Largest rung | Median | Verdict |
|---|---|---:|---:|---|
| Reduce mod `p` | `n` | 131072 | 10.073 ms | consistent |
| Lift to `Z` | `n` | 131072 | 2.661 ms | consistent |
| Reduce mod `p^k` | `n` | 131072 | 10.431 ms | consistent |
| Linear step | `n²` | 512 | 15.077 ms | consistent |
| Iterated linear lift | `n²k` | `(192,64)` | 145.228 ms | inconclusive |
| Quadratic step | `n²` | 512 | 128.731 ms | consistent |
| Product | `n²` | 1024 | 159.670 ms | consistent |
| Linear multifactor | `n²k` | `(192,64)` | 141.179 ms | inconclusive |
| Quadratic multifactor | `n² log k` | `(192,64)` | 145.140 ms | consistent |

Raw export: `reports/bench-results/hex-hensel-5c371a5a-chungus2.json`
(SHA-256
`bf157d3e95cf405dad42497b69aed75acb91432e20acb3be07d6a7dbb60d923a`).
`list` and `verify` passed.

## Comparator Ratios

The declared comparator is `FLINT nmod_poly_hensel_lift_* via python-flint`.
python-flint 0.9.0 used a persistent warm driver, five repeats, and a 0.2 s
inner-repeat floor. Ratios below are FLINT/Hex at the largest shared rung.

| Surface | Rung | Hex | FLINT | Ratio |
|---|---:|---:|---:|---:|
| Linear step | 512 | 27.256 ms | 11.445 ms | `0.42x` |
| Quadratic step | 512 | 225.867 ms | 5.168 ms | `0.02x` |
| Iterated linear | `(256,8)` | 53.016 ms | 1.067 s | `20.13x` |
| Linear multifactor | `(256,8)` | 28.382 ms | 695.342 ms | `24.50x` |
| Quadratic multifactor | `(256,8)` | 80.566 ms | 648.198 ms | `8.05x` |

The single-step comparison favours FLINT. The iterated comparisons favour Hex
only against the current python-side `fmpz_poly` emulation; python-flint does
not bind the native `nmod_poly_hensel_lift_*` entry points, so these are not
native-FLINT performance claims.

Five current comparator exports are named
`hex-hensel-*-flint-5c371a5a-chungus2.json` under
`reports/bench-results/`.

## Profile

No fresh sampling-profiler trace was collected. The current ladders isolate
bridge, binary-step, product, and multifactor costs, and the fixed comparator
registrations give steady-state per-call timings without process-startup
contamination.

The covered profile families are `bridge-operations`, `linear-hensel`,
`quadratic-hensel`, and `multifactor-lifting`.

## Concerns

- The `n²k` verdicts for the iterated linear surfaces are inconclusive on the
  mixed degree/precision schedule.
- The FLINT iterative driver is an emulation with poor high-degree behaviour.
- The fixed and parametric fixtures differ, so their absolute headline values
  should not be interchanged.
