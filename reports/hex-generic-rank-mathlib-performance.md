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
84 pairs (168 fresh builds) at commit da49ea72a, pinned to automatically
selected logical CPU 1 on chungus2, AMD EPYC 9455, Linux, Lean 4.34.0-rc2.
Every candidate passed its 30 s ceiling and every theorem reported exactly
`propext`, `Classical.choice` and `Quot.sound`. The slowest full build was
6.58 s. There were no incomplete pairs, timeouts or provenance failures.
All completed samples, host activity and signed baseline deltas are retained.

The table gives six-sample medians for each named profiler category; build
columns include the entire fresh-module process, including startup, elaboration,
checking, linting and serialization. They are not isolated tactic timings.

| Case | Full build median/max (s) | Batch (ms) | Producer (ms) | Pivot kernel (ms) | All-column kernel (ms) | Proof nodes | .olean bytes |
|---|---:|---:|---:|---:|---:|---:|---:|
| FiniteHypothesis | 3.073 / 3.765 | 27.450 | 0.530 | 2.505 | 4.720 | 1841 | 100776 |
| FiniteSideGoal | 3.038 / 3.558 | 26.050 | 0.502 | 2.460 | 4.805 | 1841 | 101192 |
| Full2Generic | 3.203 / 3.740 | 27.300 | 0.905 | 3.875 | 6.395 | 1527 | 64880 |
| Full2Hypothesis | 3.151 / 3.831 | 6.590 | 0.883 | 4.125 | 6.340 | 1361 | 77616 |
| Full2SideGoal | 3.017 / 3.853 | 6.045 | 0.863 | 3.700 | 6.395 | 1361 | 78128 |
| Low2Generic | 3.149 / 4.788 | 29.300 | 0.746 | 1.520 | 4.355 | 1590 | 67128 |
| Low2Hypothesis | 3.046 / 4.529 | 7.210 | 0.704 | 1.555 | 4.530 | 1396 | 79136 |
| Low2SideGoal | 3.039 / 6.577 | 7.420 | 0.712 | 1.720 | 4.535 | 1396 | 79648 |
| QuadraticGeneric | 3.230 / 3.860 | 22.200 | 0.969 | 4.095 | 8.030 | 1633 | 58688 |
| QuadraticHypothesis | 3.031 / 3.921 | 5.045 | 0.936 | 4.245 | 7.795 | 1519 | 83856 |
| QuadraticSideGoal | 3.238 / 3.685 | 5.055 | 0.936 | 4.215 | 7.840 | 1519 | 84400 |
| VariableGeneric | 3.108 / 4.420 | 20.600 | 0.439 | 1.540 | 2.090 | 1285 | 52920 |
| VariableHypothesis | 2.940 / 3.847 | 4.270 | 0.407 | 1.525 | 2.060 | 1186 | 70024 |
| VariableSideGoal | 3.038 / 3.746 | 4.095 | 0.418 | 1.495 | 2.085 | 1186 | 70536 |

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
