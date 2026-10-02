# Rank carrier proof performance

Closed rational, Gaussian integer, and number-field matrices are checked by
`rank`. These are build-only proof probes; they are excluded from computational
bench executables.

## Fresh-module measurements

The [raw six-trial record](bench-results/hex-rank-carriers-10216-rebased.json) records
commit `acb9a521c`, host `chungus2`, CPU 36, source hashes, dependency revisions,
and host activity. Every completed sample is retained. The runner rotates
fixture order across trials and alternates the order of each adjacent
import-baseline/theorem pair. All 108 builds and theorem axiom audits passed;
the measurement has no validity exceptions.

```sh
python3 scripts/bench/rank_carrier_sweep.py --shared-host --samples 6 \
  --output reports/bench-results/hex-rank-carriers-10216-rebased.json
```

Times below are seconds. “Above imports” is the median of the six paired
differences, so it need not equal the difference between the two independent
medians. The figures are observations on a shared host, with no speedup
confidence claim. Different imports contribute materially to total build time.

| Fixture | Tactic | Import baseline | Theorem module | Above imports |
| --- | --- | ---: | ---: | ---: |
| rational-8-rank-8 | `eval_rank` | 1.810 | 2.301 | 0.505 |
| rational-8-rank-8 | `rank` | 2.514 | 2.696 | 0.186 |
| rational-16-rank-14 | `eval_rank` | 1.805 | 5.000 | 3.203 |
| rational-16-rank-14 | `rank` | 2.522 | 3.107 | 0.562 |
| quadratic-8-rank-8 | `eval_rank` | 1.866 | 2.289 | 0.426 |
| quadratic-8-rank-8 | `rank` | 2.510 | 2.753 | 0.232 |
| quadratic-16-rank-14 | `eval_rank` | 1.897 | 4.516 | 2.649 |
| quadratic-16-rank-14 | `rank` | 2.501 | 3.892 | 1.354 |
| closed-algebraic-8-rank-8 | `rank` | 7.337 | 7.732 | 0.398 |

The rational fixtures scale the existing dense 8 × 8 and rank-14 16 × 16
integer rows by `1 / (i + 2)`. The Gaussian fixtures multiply each integer
row by the nonzero Gaussian integer `1 + (i % 3 + 1) * I`. The closed-algebraic
fixture is four diagonal `[[α, 1], [1, α]]` blocks with `α² = 2`, represented
by `PolyQuot`. The direct `QAdjoin` route is covered separately by kernel
regression tests. The Gaussian comparator explicitly imports Mathlib’s
`Echelon.Zsqrtd` tactic registration.

These fixtures test row-denominator clearing and certificate transport. They
do not characterize coefficient growth on dense matrices with independently
mixed extension coefficients or on higher-degree number fields. The Gaussian
results describe these row-scaled fixtures only; they do not establish a
performance advantage on general extension-field matrices. The quadratic handler
is included for carrier support, with cheap carrier dispatch before literal parsing.

## Integer matrices

The [integer sweep](bench-results/hex-rank-mathlib-tactic-probes-10216-rebased.json)
measures the same source revision on CPU 36, with six trials and all 120 fresh
builds retained. Reproduce with:

```sh
python3 scripts/bench/rank_tactic_sweep.py --shared-host --cpu 36 --samples 6
```

CPU 36 was selected automatically using the same nonblocking placement lease
as the carrier sweep. Each arm includes its own
imports, so the table captures the ordinary umbrella and the additional
carrier dispatch as well as proof construction. It reports current costs;
it is not a controlled before/after comparison with the earlier frontend.
Times are seconds, with the same paired-difference convention as above.

| Fixture | Tactic | Import baseline | Theorem module | Above imports |
| --- | --- | ---: | ---: | ---: |
| dense-8 | `eval_rank` | 1.901 | 2.202 | 0.287 |
| dense-8 | `rank` | 2.578 | 2.668 | 0.109 |
| dense-16 | `eval_rank` | 1.889 | 3.800 | 1.950 |
| dense-16 | `rank` | 2.601 | 2.800 | 0.204 |
| deficient-16 | `eval_rank` | 1.893 | 3.799 | 1.903 |
| deficient-16 | `rank` | 2.614 | 2.879 | 0.281 |
| dense-32 | `eval_rank` | 1.861 | 16.980 | 15.112 |
| dense-32 | `rank` | 2.618 | 3.528 | 0.911 |
| low-rank-32 | `eval_rank` | 1.821 | 17.922 | 16.107 |
| low-rank-32 | `rank` | 2.535 | 3.102 | 0.573 |

For the 8 × 8 integer fixture, `rank` has a lower proof-time increment but a
higher total module time than `eval_rank`. Imports dominate this small case.
The larger fixed-size fixtures show lower total module times for `rank`.

## Kernel attribution

The [profile record](bench-results/hex-rank-carrier-kernel-10216-rebased.json) contains
one representative build per arm, pinned to CPU 5, with complete output.
To reproduce, put `set_option profiler true` and
`set_option profiler.threshold 1000000` immediately before the probe theorem
and run the recorded `taskset … lake build …` command. Restore the source
afterward. These attribution runs are separate from the six-trial timing
samples; the table reports Lean’s cumulative `type checking` category.

| Probe | Kernel time (s) |
| --- | ---: |
| `RationalDeficient16Hex` | 0.179 |
| `RationalDeficient16Mathlib` | 1.320 |
| `QuadraticDeficient16Hex` | 1.020 |
| `QuadraticDeficient16Mathlib` | 1.190 |
| `Algebraic8Hex` | 0.133 |

The polynomial checker verifies multiplication and explicit division witnesses
on integer coefficient lists; it does not run polynomial division or elimination
in the kernel. The number-field entry identification additionally reduces each
scaled entry to its coefficient model once. All audited rank theorems depend
only on `propext`, `Classical.choice`, and `Quot.sound`.
