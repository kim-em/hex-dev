# Rational root-production anchors

These compiled, Mathlib-free fixed benchmarks exercise three stages of the
rational root producer. They are functional timing anchors on one input, not
scaling evidence or measurements of a tower.

`Hex.RealClosure.Bench.runYun` removes the zero factor from
`-3X²(X²−2)³(X−3)⁵` and runs the raw-coefficient Yun recurrence on the
nonzero quotient. It checks the two resulting multiplicities, 3 and 5.
`runIsolation` applies capped Sturm isolation and descriptor completion to
`(X²−2)(X−3)`, checking that it produces three real roots. `runAssembly`
extracts zero, runs Yun, isolates the actual factors and checks four real
root entries with multiplicities 2, 3, 3 and 5. The benchmark inputs pass
through `IO.Ref` so their production work occurs inside the timed calls.

The clean-commit run on the shared host `chungus2` used CPU 19 selected by the
CPU lease. Each registration had ten measured calls; every
completed call returned the expected hash `0x1`.

| Stage | Median | Observed range |
| --- | ---: | ---: |
| Yun recurrence | 60.228 µs | 59.075–60.797 µs |
| Isolation and completion | 272.311 µs | 269.274–274.129 µs |
| Root assembly | 198.364 µs | 195.448–203.237 µs |

The [export](isolation-anchors.json) retains all measured durations and
runner metadata. The [log](isolation-anchors.log) records the harness output.
The [context](isolation-anchors-context.json) records CPU affinity, host load,
the exact command, and source and executable hashes. Peak RSS across the
measured child processes was 68,360–69,028 kB; this is process memory, not an
allocation count for each operation. The recorded commit was `0f3fe0b`.

All earlier completed samples are also retained: the initial
[development export](isolation-anchors-development.json), the
[corrected development export](isolation-anchors-development-fixed.json),
and the [unpinned export](isolation-anchors-unpinned.json). The initial
development isolation result, about 32 ns, measured a constant-folded call
before its input moved through `IO.Ref`; it is invalid as isolation timing
evidence. The corrected development and unpinned runs are context, not
additional trials of the pinned clean-commit measurement.

Run `lake build hexrealclosure_bench`, then
`.lake/build/bin/hexrealclosure_bench run Hex.RealClosure.Bench.runYun Hex.RealClosure.Bench.runIsolation Hex.RealClosure.Bench.runAssembly`.

The formal #10378 performance evaluation still requires the specified depth
and coefficient families, nested sign and zero queries, BKR counts, splitting
and transport, clean/eager comparisons on identical semantic inputs, tower8
and MetiTarski workloads, and representative attribution.
