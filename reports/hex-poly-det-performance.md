# Polynomial determinant executable performance

The compiled producer and canonical-list checker were measured separately on
48 feasible `(dimension, atoms, degree, support)` workloads. The 96 fixed
registrations contain five samples each; every sample and cap failure is retained.
These are fixed-workload observations (Mode 3), not a fitted cubic complexity claim.

Raw outcomes: `{'ok': 450, 'killed_at_cap': 30}`. Source commit: `87ced16f06c0d3f2f91987d874ce31691c0bbb1f`.
The full [data and context](bench-results/hex-poly-det-native.json.gz) include
the executable hash, all 89 repository source hashes, dependency checkouts,
runner source, CPU topology, per-sample RSS fields and compiler/runtime versions.
The run used automatically leased CPU 47 on chungus2 (AMD EPYC 9455),
with two Lean workers pinned to that one CPU. Sources remained unchanged and
the measuring worktree remained clean. Host activity was not used to discard samples.

## Inputs and timing boundaries

The matrices are dense integer matrices (3 on the diagonal, 1 elsewhere),
with each row multiplied by its own sparse polynomial. Entries within a row
are correlated. The exceptional 2×2, four-variable linear monomial case uses
four independent entries. Requested entry degree and support are realized;
33 support requests exceeding the available monomials are infeasible, as in
the proof-probe manifest. The compiled and proof-probe generators choose
different integer coefficients and polynomial terms, so equal parameter labels
do not identify equal matrices across the two reports.

The producer times retained-transform elimination with a trivial callback,
excluding list conversion and self-check. The checker times only list replay
on prepared rows and a precomputed witness. Each child prepares its witness
before the timer; the configured five-second process cap includes preparation.
Consequently a capped checker sample does not establish that list replay alone
exceeds five seconds. Lean-bench uses one warmup and five measured repetitions,
autotuning repetitions toward 1 ms within each sample. A table median requires
all five samples; no surviving subset replaces a censored workload.

There is **no-comparable-surface-in-named-comparator** for timed multivariate
determinants. SymPy Berkowitz is the conformance oracle, not a timed comparator.
All 42 Int, Rat and prime-101 fixtures pass, including dense, pivot-swap,
singular and vanishing-specialization shapes.

## Medians

All N/K/D/S rows below use the correlated row-scaled family described above;
the exceptional independent 2×2 family is N2/K4/D1/S1. Times are microseconds.

| N/K/D/S | Producer µs | Checker µs | Completed P/C |
|---|---:|---:|---:|
| 2/1/1/1 | 4.469 | 1.097 | 5/5 |
| 2/1/2/1 | 4.589 | 1.059 | 5/5 |
| 2/1/4/1 | 4.625 | 1.083 | 5/5 |
| 2/1/4/4 | 30.18 | 5.251 | 5/5 |
| 2/2/1/1 | 5.13 | 1.169 | 5/5 |
| 2/2/2/1 | 5.079 | 1.154 | 5/5 |
| 2/2/2/4 | 50.59 | 6.741 | 5/5 |
| 2/2/4/1 | 5.055 | 1.152 | 5/5 |
| 2/2/4/4 | 58.6 | 6.883 | 5/5 |
| 2/4/1/1 | 7.924 | 1.331 | 5/5 |
| 2/4/1/4 | 85.32 | 9.34 | 5/5 |
| 2/4/2/1 | 6.284 | 1.335 | 5/5 |
| 2/4/2/4 | 105 | 9.466 | 5/5 |
| 2/4/4/1 | 6.153 | 1.329 | 5/5 |
| 2/4/4/4 | 104.1 | 9.368 | 5/5 |
| 2/4/4/16 | 1564 | 152.8 | 5/5 |
| 4/1/1/1 | 40.43 | 4.731 | 5/5 |
| 4/1/2/1 | 39.78 | 4.722 | 5/5 |
| 4/1/4/1 | 39.65 | 4.727 | 5/5 |
| 4/1/4/4 | 1068 | 80.3 | 5/5 |
| 4/2/1/1 | 46.55 | 5.299 | 5/5 |
| 4/2/2/1 | 46.82 | 5.318 | 5/5 |
| 4/2/2/4 | 3816 | 174.7 | 5/5 |
| 4/2/4/1 | 46.62 | 5.364 | 5/5 |
| 4/2/4/4 | 6878 | 245.8 | 5/5 |
| 4/4/1/1 | 56.11 | 6.327 | 5/5 |
| 4/4/1/4 | 7206 | 233.2 | 5/5 |
| 4/4/2/1 | 57.06 | 6.343 | 5/5 |
| 4/4/2/4 | 3.424e+04 | 663.4 | 5/5 |
| 4/4/4/1 | 57.62 | 6.474 | 5/5 |
| 4/4/4/4 | 3.968e+04 | 678.6 | 5/5 |
| 4/4/4/16 | 2.137e+06 | 1.786e+04 | 5/5 |
| 8/1/1/1 | 327.4 | 27.09 | 5/5 |
| 8/1/2/1 | 318.5 | 26.88 | 5/5 |
| 8/1/4/1 | 322.6 | 26.81 | 5/5 |
| 8/1/4/4 | 4.5e+04 | 1228 | 5/5 |
| 8/2/1/1 | 365.5 | 31.55 | 5/5 |
| 8/2/2/1 | 367.3 | 30.57 | 5/5 |
| 8/2/2/4 | 4.913e+05 | 5119 | 5/5 |
| 8/2/4/1 | 374 | 31.3 | 5/5 |
| 8/2/4/4 | 2.526e+06 | 1.314e+04 | 5/5 |
| 8/4/1/1 | 450 | 37.69 | 5/5 |
| 8/4/1/4 | 1.573e+06 | 9350 | 5/5 |
| 8/4/2/1 | 456.7 | 37.84 | 5/5 |
| 8/4/2/4 | cap/failure | cap/failure | 0/0 |
| 8/4/4/1 | 450.5 | 38.06 | 5/5 |
| 8/4/4/4 | cap/failure | cap/failure | 0/0 |
| 8/4/4/16 | cap/failure | cap/failure | 0/0 |

The higher-support cases expose polynomial expression growth. These fixed
observations do not extrapolate to independent dense entries or to larger minors.

## Retained diagnostic run

The [one-worker diagnostic](bench-results/hex-poly-det-native-diagnostic.json.gz)
retains all 480 samples and full output from the initial runner configuration.
With one worker, the blocking stderr reader could starve the timeout task.
An external cap allowed that fixed schedule to finish; every intervention is
recorded. Its source tree also changed outside the running executable during
the run. It is excluded from the table above. The corrected run changes the
runner configuration to two workers and freezes its separate worktree;
it is not an unchanged rerun selected for a quieter host.
