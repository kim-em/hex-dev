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

Source commit: `6c803e229b1e9a65275714eaf1e279e1a04a9f06`. Host: `chungus2`, AMD EPYC 9455 48-Core Processor,
leanprover/lean4:v4.34.0. One Lean worker was pinned to automatically leased logical CPU
10. Other shared-host activity is recorded as context; absolute timings describe this host. No samples were discarded.

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
made from them. The [earlier revision](bench-results/hex-generic-rank-residue-initial.json.gz)
retains every completed sample from the initial implementation.

| Case | Full build median/max (s) | Batch (ms) | Producer (ms) | Header kernel (ms) | Pivot kernel (ms) | All-column kernel (ms) | Proof nodes | .olean bytes |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| FiniteGeneric | 4.080 / 6.061 | 58.900 | 1.105 | 3.045 | 2.315 | 4.940 | 1717 | 54256 |
| FiniteHypothesis | 4.154 / 4.796 | 31.100 | 0.943 | 2.380 | 2.165 | 4.700 | 1640 | 87752 |
| FiniteSideGoal | 3.956 / 8.158 | 30.850 | 1.015 | 2.240 | 2.155 | 4.320 | 1640 | 88168 |
| Full2Generic | 4.375 / 5.701 | 34.600 | 1.555 | 3.880 | 4.785 | 8.605 | 1544 | 65112 |
| Full2Hypothesis | 4.015 / 6.854 | 8.275 | 1.720 | 3.120 | 5.435 | 8.180 | 1390 | 78480 |
| Full2SideGoal | 4.089 / 6.338 | 7.160 | 1.735 | 2.700 | 4.650 | 6.960 | 1390 | 78992 |
| Low2Generic | 4.358 / 6.037 | 41.650 | 1.570 | 3.210 | 1.865 | 5.470 | 1605 | 67360 |
| Low2Hypothesis | 4.174 / 7.078 | 9.510 | 1.525 | 2.400 | 1.735 | 5.540 | 1423 | 79936 |
| Low2SideGoal | 4.187 / 5.255 | 8.995 | 1.255 | 2.580 | 1.985 | 7.010 | 1423 | 80448 |
| QuadraticGeneric | 3.248 / 7.786 | 22.700 | 1.770 | 3.010 | 4.220 | 9.450 | 1642 | 58792 |
| QuadraticHypothesis | 3.846 / 7.582 | 5.605 | 1.655 | 2.700 | 4.910 | 9.400 | 1540 | 84528 |
| QuadraticSideGoal | 4.731 / 8.704 | 5.920 | 2.040 | 2.585 | 5.025 | 8.925 | 1540 | 85072 |
| VariableGeneric | 3.740 / 5.998 | 19.750 | 0.880 | 1.875 | 1.480 | 2.065 | 1291 | 52960 |
| VariableHypothesis | 3.965 / 5.740 | 4.205 | 0.788 | 1.585 | 1.595 | 2.230 | 1204 | 70632 |
| VariableSideGoal | 3.523 / 8.889 | 4.015 | 0.768 | 1.620 | 1.515 | 2.105 | 1204 | 71144 |
