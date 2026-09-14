# HexGenericRankMathlib performance

## Preregistered proof measurements

`scripts/bench/generic_rank_sweep.py` specifies fourteen fresh-module probes,
with six adjacent baseline/candidate pairs each, alternating AB/BA order.
Every probe has a 30 second full-proof-build ceiling and a 120 second cleanup
timeout. The import baseline matches each candidate's imports. All completed
samples are retained on the shared host; CPU placement is selected automatically.

The full/low 2×2 workloads at one variable, degree one and factor support one,
and the `[x]` and quadratic examples each have generic, hypothesis-discharge,
and visible-side-goal probes. The finite-field example has hypothesis and
side-goal probes; its positive-characteristic polynomial-ring output-1 probe
is a documented non-test until the shared Nat residue encoding (#10257) lands.
The field fallback checks balanced integer representatives modulo p with the
existing polynomial-list arithmetic, without reducing through ZMod64.

Lean's cumulative profiler records batch reification/conversion, compiled
certificate production, and synchronous declaration checks separately for the
header, pivot-block identity and all-column identity. Nested profiler categories
are disabled inside those three checks so their named categories include the
kernel's work. Boolean proof-term construction is outside those categories;
the external full-build time includes it and all other elaboration. No library
or probe reads an in-process clock. A trace records distinct expression nodes
across the provider's shared output proofs; the reflection batch additionally
charges its own reconstruction.

Comparator: **no-comparable-surface-in-named-comparator**. Mathlib's numeric
`eval_rank` does not provide these symbolic or conditional outputs.

The [diagnostic clock-instrumented sweep](data/hex-generic-rank-diagnostic-clock-probes.json.gz)
retains all 84 pairs collected before replacing direct clock reads with Lean's
profiler. Its build and axiom checks passed, but that instrumentation violated
the build-only probe policy. It is diagnostic evidence only; the accepted
measurements below use the profiler-based implementation.

The [initial profiler sweep](data/hex-generic-rank-initial-profiler-probes.json.gz)
and [quoted-list refinement sweep](data/hex-generic-rank-quoted-list-probes.json.gz)
retain 84 complete pairs each for their recorded source revisions. Their
measurements precede the final diagnostic and probe-limit refinements; the
accepted evidence below measures the final implementation.

The profiler and trace options are explicit in the checked-in probe sources,
so ordinary builds and the sweep use the same instrumentation. Heartbeat limits
are disabled in the probes; the sweep enforces the registered wall-time ceiling.

## Accepted fresh-module evidence

The [complete sweep](data/hex-generic-rank-mathlib-probes.json.gz) records all
84 pairs (168 fresh builds) at commit 60668765c, pinned to automatically
selected logical CPU 7 on chungus2, AMD EPYC 9455, Linux, Lean 4.34.0-rc2.
Every candidate passed its 30 s ceiling and every theorem reported exactly
`propext`, `Classical.choice` and `Quot.sound`. The slowest full build was
3.69 s. There were no incomplete pairs, timeouts or provenance failures.
All completed samples, host activity and signed baseline deltas are retained.

The table gives six-sample medians for each named profiler category; build
columns include the entire fresh-module process, including startup, elaboration,
checking, linting and serialization. They are not isolated tactic timings.

| Case | Full build median/max (s) | Batch (ms) | Producer (ms) | Pivot kernel (ms) | All-column kernel (ms) | Proof nodes | .olean bytes |
|---|---:|---:|---:|---:|---:|---:|---:|
| FiniteHypothesis | 2.902 / 3.385 | 25.300 | 0.484 | 2.355 | 4.625 | 1849 | 100728 |
| FiniteSideGoal | 2.862 / 3.686 | 25.300 | 0.494 | 2.360 | 4.585 | 1849 | 101144 |
| Full2Generic | 2.898 / 2.954 | 24.900 | 0.833 | 3.635 | 5.740 | 1540 | 64960 |
| Full2Hypothesis | 2.812 / 3.097 | 5.725 | 0.839 | 3.680 | 5.830 | 1374 | 77696 |
| Full2SideGoal | 2.802 / 2.831 | 5.790 | 0.831 | 3.645 | 5.690 | 1374 | 78208 |
| Low2Generic | 2.966 / 3.404 | 28.100 | 0.716 | 1.495 | 4.210 | 1603 | 67208 |
| Low2Hypothesis | 2.798 / 2.956 | 6.815 | 0.681 | 1.520 | 4.235 | 1409 | 79216 |
| Low2SideGoal | 2.873 / 3.400 | 6.810 | 0.685 | 1.500 | 4.340 | 1409 | 79728 |
| QuadraticGeneric | 2.954 / 3.506 | 22.050 | 0.960 | 4.065 | 7.660 | 1640 | 58640 |
| QuadraticHypothesis | 2.831 / 3.422 | 4.995 | 0.913 | 3.985 | 7.460 | 1526 | 83808 |
| QuadraticSideGoal | 2.817 / 3.314 | 5.005 | 0.915 | 4.010 | 7.460 | 1526 | 84352 |
| VariableGeneric | 2.805 / 3.060 | 18.400 | 0.413 | 1.410 | 1.960 | 1289 | 52808 |
| VariableHypothesis | 2.803 / 3.066 | 3.870 | 0.413 | 1.460 | 2.095 | 1190 | 69912 |
| VariableSideGoal | 2.811 / 3.202 | 3.910 | 0.407 | 1.425 | 2.040 | 1190 | 70424 |

Header-check medians range from 1.40 to 2.70 ms and are retained separately
in the [summary](data/hex-generic-rank-mathlib-summary.json) and every raw
sample. The `.olean` contains both the accepted theorem and its auxiliary
closed check declarations; no theorem depends on a producer computation.
The declaration categories include synchronous declaration registration and
checking, so they bound rather than isolate the kernel's reduction cost.

At these required small rungs, the list-form pivot and all-column checks fit
comfortably within the full-build ceiling. This supports the implemented
list representation at those rungs; it makes no performance claim about
larger symbolic proof matrices. The pending Nat residue representation needs
its own positive-characteristic output-1 measurement when enabled.

Reproduce with
`python3 scripts/bench/generic_rank_sweep.py --shared-host --cpu "$(python3 scripts/bench/idle_core.py)" --output /tmp/generic-rank-proofs.json`.
The manifest fixes six samples, rejects missing phase profiles, records emitted
artifact sizes and enforces the 120 s cleanup timeout and 30 s full-build ceiling.
