# Rank carrier proof performance

Closed rational, Gaussian integer, and number-field matrices are checked by
`rank`. These are build-only proof probes; they are excluded from computational
bench executables.

## Fresh-module measurements

The [raw six-trial record](bench-results/hex-rank-carriers-10216-reviewed.json) records
commit `9e0fea774`, host `chungus2`, CPU 2, source hashes, dependency revisions,
and host activity. Every completed sample is retained. The runner rotates
fixture order across trials and alternates the order of each adjacent
import-baseline/theorem pair. All 108 builds and theorem axiom audits passed;
the measurement has no validity exceptions.

```sh
python3 scripts/bench/rank_carrier_sweep.py --shared-host --samples 6 \
  --output reports/bench-results/hex-rank-carriers-10216-reviewed.json
```

Times below are seconds. “Above imports” is the median of the six paired
differences, so it need not equal the difference between the two independent
medians. The figures are observations on a shared host, with no speedup
confidence claim. Different imports contribute materially to total build time.

| Fixture | Tactic | Import baseline | Theorem module | Above imports |
| --- | --- | ---: | ---: | ---: |
| rational-8-rank-8 | `eval_rank` | 1.813 | 2.308 | 0.495 |
| rational-8-rank-8 | `rank` | 2.516 | 2.729 | 0.207 |
| rational-16-rank-14 | `eval_rank` | 1.823 | 4.814 | 3.010 |
| rational-16-rank-14 | `rank` | 2.517 | 3.367 | 0.860 |
| quadratic-8-rank-8 | `eval_rank` | 1.813 | 2.211 | 0.392 |
| quadratic-8-rank-8 | `rank` | 2.502 | 2.913 | 0.394 |
| quadratic-16-rank-14 | `eval_rank` | 1.823 | 4.504 | 2.704 |
| quadratic-16-rank-14 | `rank` | 2.518 | 4.872 | 2.368 |
| closed-algebraic-8-rank-8 | `rank` | 7.263 | 7.859 | 0.590 |

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

## Integer matrices

The [integer sweep](bench-results/hex-rank-mathlib-tactic-probes-10216.json)
measures the same source revision on CPU 2, with six trials and all 120 fresh
builds retained. Reproduce with:

```sh
python3 scripts/bench/rank_tactic_sweep.py --shared-host --cpu 2 --samples 6
```

CPU 2 was selected automatically using the same nonblocking placement lease
as the carrier sweep. Each arm includes its own
imports, so the table captures the ordinary umbrella and the additional
carrier dispatch as well as proof construction. It reports current costs;
it is not a controlled before/after comparison with the earlier frontend.
Times are seconds, with the same paired-difference convention as above.

| Fixture | Tactic | Import baseline | Theorem module | Above imports |
| --- | --- | ---: | ---: | ---: |
| dense-8 | `eval_rank` | 1.812 | 2.112 | 0.297 |
| dense-8 | `rank` | 2.529 | 2.672 | 0.141 |
| dense-16 | `eval_rank` | 1.816 | 3.616 | 1.807 |
| dense-16 | `rank` | 2.522 | 2.909 | 0.387 |
| deficient-16 | `eval_rank` | 1.916 | 3.721 | 1.797 |
| deficient-16 | `rank` | 2.556 | 2.961 | 0.401 |
| dense-32 | `eval_rank` | 1.819 | 15.770 | 13.945 |
| dense-32 | `rank` | 2.538 | 4.710 | 2.172 |
| low-rank-32 | `eval_rank` | 1.820 | 16.867 | 15.010 |
| low-rank-32 | `rank` | 2.521 | 3.213 | 0.687 |

For the 8 × 8 integer fixture, `rank` has a lower proof-time increment but a
higher total module time than `eval_rank`. Imports dominate this small case.
The larger fixed-size fixtures show lower total module times for `rank`.

## Kernel attribution

The [profile record](bench-results/hex-rank-carrier-kernel-10216-reviewed.json) contains
one representative build per arm, pinned to CPU 53, with complete output.
To reproduce, put `set_option profiler true` and
`set_option profiler.threshold 1000000` immediately before the probe theorem
and run the recorded `taskset … lake build …` command. Restore the source
afterward. These attribution runs are separate from the six-trial timing
samples; the table reports Lean’s cumulative `type checking` category.

| Probe | Kernel time (s) |
| --- | ---: |
| `RationalDeficient16Hex` | 0.209 |
| `RationalDeficient16Mathlib` | 1.400 |
| `QuadraticDeficient16Hex` | 1.110 |
| `QuadraticDeficient16Mathlib` | 1.310 |
| `Algebraic8Hex` | 0.135 |

The polynomial checker verifies multiplication and explicit division witnesses
on integer coefficient lists; it does not run polynomial division or elimination
in the kernel. The number-field entry identification additionally reduces each
scaled entry to its coefficient model once. All audited rank theorems depend
only on `propext`, `Classical.choice`, and `Quot.sound`.
