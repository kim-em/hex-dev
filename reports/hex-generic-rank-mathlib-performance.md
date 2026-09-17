# HexGenericRankMathlib performance

The symbolic rank proof suite covers canonical integer lists and the shared
canonical Nat residue lists. All three finite-field outputs are enabled:
generic rank over a polynomial ring, a condition discharged from a hypothesis,
and a visible nonvanishing side goal. `X³ − X` over `MvPolynomial (Fin 1) (ZMod 3)`
has unconditional rank 1; interpreting its variable as an element of `ZMod 3`
still leaves the required `x ^ 3 - x ≠ 0` condition.

## Fresh-module measurements

The [complete record](bench-results/hex-generic-rank-residue-probes.json.gz)
contains 90 adjacent baseline/candidate pairs (15 probes × six trials), using
`scripts/bench/generic_rank_sweep.py`. The fixed trial-major schedule rotates
cases and alternates AB/BA order. All samples and host observations are retained;
there were no failed builds, timeouts, or provenance exceptions. Each theorem
reports only `propext`, `Classical.choice`, and `Quot.sound`, and each full proof
build passed its 30-second ceiling. The cleanup timeout is 120 seconds.

Source commit: `a73104154c6d77e8af813ade9cd7993e0ffa2596`. Host: `chungus2`, AMD EPYC 9455 48-Core Processor,
leanprover/lean4:v4.34.0. One Lean worker was pinned to automatically leased logical CPU
67. Concurrent monorepo compilation and other shared-host activity are
recorded context; absolute timings describe this host. No samples were discarded.

The table gives six-sample medians of Lean's profiler categories. The header,
pivot, and all-column categories include their synchronous kernel declaration
checks, with nested profiling disabled. Boolean proof construction is outside
those categories. Full-build columns include process startup, imports,
elaboration, all proof construction/checking, linting, and serialization; they
are not isolated tactic times. Proof-node counts describe the provider's shared
outputs, while the reflection batch accounts for its reconstruction separately.

Comparator: **no-comparable-surface-in-named-comparator**. Mathlib's numeric
`eval_rank` does not provide these symbolic or conditional outputs. Import-only
baselines and signed deltas are retained in the raw record; no speedup claim is
made from them.

| Case | Full build median/max (s) | Batch (ms) | Producer (ms) | Header kernel (ms) | Pivot kernel (ms) | All-column kernel (ms) | Proof nodes | .olean bytes |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| FiniteGeneric | 4.814 / 7.201 | 89.300 | 1.253 | 5.435 | 3.265 | 7.600 | 1717 | 54256 |
| FiniteHypothesis | 4.528 / 7.512 | 34.350 | 1.365 | 3.755 | 2.930 | 6.500 | 1640 | 87752 |
| FiniteSideGoal | 5.201 / 7.278 | 51.450 | 1.290 | 3.915 | 2.640 | 6.520 | 1640 | 88168 |
| Full2Generic | 4.127 / 7.824 | 35.000 | 1.890 | 3.225 | 4.675 | 6.875 | 1544 | 65112 |
| Full2Hypothesis | 3.731 / 6.446 | 7.710 | 1.580 | 2.365 | 4.855 | 6.405 | 1390 | 78480 |
| Full2SideGoal | 4.302 / 6.961 | 6.360 | 1.415 | 2.335 | 4.455 | 6.455 | 1390 | 78992 |
| Low2Generic | 4.270 / 7.716 | 33.100 | 1.245 | 3.080 | 1.690 | 5.480 | 1605 | 67360 |
| Low2Hypothesis | 4.796 / 8.130 | 8.775 | 1.905 | 2.710 | 2.190 | 6.340 | 1423 | 79936 |
| Low2SideGoal | 4.869 / 7.224 | 9.660 | 1.225 | 2.230 | 1.650 | 5.070 | 1423 | 80448 |
| QuadraticGeneric | 4.996 / 8.796 | 30.200 | 1.825 | 3.860 | 5.905 | 13.950 | 1642 | 58792 |
| QuadraticHypothesis | 6.490 / 9.229 | 10.330 | 2.650 | 3.675 | 8.790 | 18.450 | 1540 | 84528 |
| QuadraticSideGoal | 5.212 / 8.021 | 7.335 | 1.685 | 3.795 | 6.560 | 13.350 | 1540 | 85072 |
| VariableGeneric | 4.761 / 7.611 | 34.350 | 1.089 | 2.665 | 1.745 | 2.580 | 1291 | 52960 |
| VariableHypothesis | 4.089 / 8.642 | 6.840 | 0.960 | 1.755 | 1.765 | 3.050 | 1204 | 70632 |
| VariableSideGoal | 5.167 / 9.245 | 4.885 | 0.859 | 1.655 | 1.790 | 2.515 | 1204 | 71144 |
