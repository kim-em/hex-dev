# Root-production timing anchors

## Rational producer calls

These compiled, Mathlib-free fixed benchmarks exercise three distinct calls
in the rational root producer. They are functional timing anchors on one input,
not scaling evidence or measurements of a tower.

`Hex.RealClosure.Bench.runYun` removes the zero factor from
`-3X²(X²−2)³(X−3)⁵` and runs the raw-coefficient Yun recurrence on the
nonzero quotient. It checks the two resulting multiplicities, 3 and 5.
`runIsolation` applies capped Sturm isolation and descriptor completion to
`(X²−2)(X−3)`, checking that it produces three real roots. `runAssembly`
extracts zero, runs Yun, isolates the actual factors and checks four real
root entries with multiplicities 2, 3, 3 and 5. The benchmark inputs pass
through `IO.Ref` so their production work occurs inside the timed calls.
Assembly isolates Yun's squarefree factors separately, while `runIsolation`
isolates their degree-three product. The three timings should not be added or
subtracted. Each registration returns a fixed success hash after checking the
properties just described; the hash does not encode the full result.

The clean-commit run on the shared host `chungus2` used CPU 19 selected by the
CPU lease. Each registration had ten measured calls; every
completed call returned the expected hash `0x1`.

| Registration | Median | Observed range |
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
additional trials of the pinned clean-commit measurement. The unpinned clean
run omitted CPU pinning, so it was followed by one pinned run with unchanged
source; both completed runs are retained. The rational `Bench.lean` hash in
its context file belongs to the version before `runNested` was added; the
three rational benchmark bodies were unchanged by that addition.

## Nested selected-root call

`runNested` validates a descriptor selecting `√2` from the reducible
`(X²−2)(X−3)`, then validates the positive root `β` of `Y²−√2` over the
first level's stored values. It checks `β > 0`, `β² = √2`, and
`ββ⁻¹ = 1` through the actual selected-root sign queries. The first raw
descriptor is read from `IO.Ref` inside the timed call. This measures both
validations and the nested arithmetic; its duration is not directly
comparable to the three stage-specific rational anchors above.

On `chungus2`, CPU 10 was selected by the shared-host CPU lease. The ten
measured calls all returned the expected hash `0x1`. The median was
**144.388 ms**, with an observed range of **143.541–146.707 ms**. Peak RSS
across the measured child processes was 68,376–69,164 kB. The
[export](nested-anchor.json), [log](nested-anchor.log), and
[context](nested-anchor-context.json) retain all samples, the command,
host conditions, and source and executable hashes. The source commit was
`04f7262`; the runner marked the working tree dirty, but the context did not
record which paths caused that status. Source and executable hashes identify
the recorded artifacts; the dirty flag is retained as a limitation.

To remeasure the current registrations, run `lake build hexrealclosure_bench`
and use an automatically selected CPU for each of these separate calls:

```sh
taskset -c "$(python3 scripts/bench/idle_core.py)" .lake/build/bin/hexrealclosure_bench run Hex.RealClosure.Bench.runYun Hex.RealClosure.Bench.runIsolation Hex.RealClosure.Bench.runAssembly --export-file /tmp/hex-real-closure-rational-rerun.json
taskset -c "$(python3 scripts/bench/idle_core.py)" .lake/build/bin/hexrealclosure_bench run Hex.RealClosure.Bench.runNested --export-file /tmp/hex-real-closure-nested-rerun.json
```

The context files record the original source commits and selected CPUs; a
rerun on current source is a new observation, not an extension of those runs.

The formal #10378 performance evaluation still requires the specified depth
and coefficient families, systematic nested sign and zero counts, BKR counts, splitting
and transport, clean/eager comparisons on identical semantic inputs, tower8
and MetiTarski workloads, and representative attribution.
