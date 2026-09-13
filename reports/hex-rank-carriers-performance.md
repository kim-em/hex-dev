# Rank carrier proof performance

Closed rational, Gaussian integer, and number-field matrices are checked by
`rank`. These are build-only proof probes; they are excluded from computational
bench executables.

## Fresh-module measurements

The [raw six-trial record](bench-results/hex-rank-carriers-10216.json) records
commit `50ececa3c`, host `chungus2`, CPU 32, source hashes, dependency revisions,
and host activity. Every completed sample is retained. The runner rotates
fixture order across trials and alternates the order of each adjacent
import-baseline/theorem pair. All 108 builds and theorem axiom audits passed;
the measurement has no validity exceptions.

```sh
python3 scripts/bench/rank_carrier_sweep.py --shared-host --samples 6 \
  --output reports/bench-results/hex-rank-carriers-10216.json
```

Times below are seconds. “Above imports” is the median of the six paired
differences, so it need not equal the difference between the two independent
medians. The figures are observations on a shared host, with no speedup
confidence claim. Different imports contribute materially to total build time.

| Fixture | Tactic | Import baseline | Theorem module | Above imports |
| --- | --- | ---: | ---: | ---: |
| rational-8-rank-8 | `eval_rank` | 1.861 | 2.306 | 0.488 |
| rational-8-rank-8 | `rank` | 2.606 | 3.352 | 0.299 |
| rational-16-rank-14 | `eval_rank` | 1.819 | 4.962 | 3.146 |
| rational-16-rank-14 | `rank` | 3.048 | 4.048 | 1.038 |
| quadratic-8-rank-8 | `eval_rank` | 2.478 | 2.820 | 0.441 |
| quadratic-8-rank-8 | `rank` | 2.621 | 2.965 | 0.385 |
| quadratic-16-rank-14 | `eval_rank` | 1.903 | 4.555 | 2.610 |
| quadratic-16-rank-14 | `rank` | 2.619 | 4.913 | 2.322 |
| closed-algebraic-8-rank-8 | `rank` | 7.383 | 7.877 | 0.520 |

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
results are close to `eval_rank` at these sizes; they do not establish a
performance advantage. The quadratic handler is included for carrier support,
with cheap carrier dispatch before literal parsing.

## Kernel attribution

The [profile record](bench-results/hex-rank-carrier-kernel-10216.json) contains
one representative build per arm, pinned to CPU 17, with complete output.
To reproduce, put `set_option profiler true` and
`set_option profiler.threshold 1000000` immediately before the probe theorem
and run the recorded `taskset … lake build …` command. Restore the source
afterward. These attribution runs are separate from the six-trial timing
samples; the table reports Lean’s cumulative `type checking` category.

| Probe | Kernel time (s) |
| --- | ---: |
| `RationalDeficient16Hex` | 0.301 |
| `RationalDeficient16Mathlib` | 1.950 |
| `QuadraticDeficient16Hex` | 1.460 |
| `QuadraticDeficient16Mathlib` | 1.720 |
| `Algebraic8Hex` | 0.170 |

The polynomial checker verifies multiplication and explicit division witnesses
on integer coefficient lists; it does not run polynomial division or elimination
in the kernel. The number-field entry identification additionally reduces each
scaled entry to its coefficient model once. All audited rank theorems depend
only on `propext`, `Classical.choice`, and `Quot.sound`.
