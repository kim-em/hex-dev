# Root-production timing anchors

## Rational producer calls

These compiled, Mathlib-free fixed benchmarks exercise three distinct calls
in the rational root producer. They are functional timing anchors on one input,
not scaling evidence or measurements of a tower.

`Hex.RealClosure.Bench.runYun` removes the zero factor from
`-3X²(X²−2)³(X−3)⁵` and runs the raw-coefficient Yun recurrence on the
nonzero quotient. It checks the extracted zero multiplicity 2 and the two
resulting nonzero multiplicities, 3 and 5.
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
CPU lease. Each registration had ten measured repeats averaging 32 Yun, 4
isolation, or 8 assembly calls per repeat; every completed repeat returned the
expected hash `0x1`. The observed ranges below are ranges of repeat means.

| Registration | Median | Observed range |
| --- | ---: | ---: |
| Yun recurrence | 60.228 µs | 59.075–60.797 µs |
| Isolation and completion | 272.311 µs | 269.274–274.129 µs |
| Root assembly | 198.364 µs | 195.448–203.237 µs |

The [export](isolation-anchors.json) retains all repeat durations and
runner metadata. The [log](isolation-anchors.log) records the harness output.
The [context](isolation-anchors-context.json) records CPU affinity, host load,
the exact command, and source and executable hashes. Peak RSS across the
measured child processes was 68,360–69,028 kB; this is process memory, not an
allocation count for each operation. The recorded commit was `0f3fe0b`.

All earlier completed samples are also retained: the initial
[development export](isolation-anchors-development.json), the
[corrected development export](isolation-anchors-development-fixed.json),
and the [unpinned export](isolation-anchors-unpinned.json). The initial
development isolation result, 31 ns median, measured a constant-folded call
before its input moved through `IO.Ref`; it is invalid as isolation timing
evidence. The corrected development and unpinned runs are context, not
additional trials of the pinned clean-commit measurement. The unpinned clean
run omitted CPU pinning, so it was followed by one pinned run with unchanged
source; both completed runs are retained. The pinned run was slightly slower
for all three registrations and is the reported measurement. The rational
`Bench.lean` hash in its context file belongs to the version before
`runNested` was added; the three rational benchmark bodies were unchanged by
that addition.

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
and record the selected CPU from this command's output. Each call holds a CPU
lease until its measurement finishes:

```sh
python3 - <<'PY'
import subprocess
from scripts.bench.cpu_lease import cpu_lease

for names, output in [
    (["Hex.RealClosure.Bench.runYun", "Hex.RealClosure.Bench.runIsolation",
      "Hex.RealClosure.Bench.runAssembly"], "/tmp/hex-real-closure-rational-rerun.json"),
    (["Hex.RealClosure.Bench.runNested"], "/tmp/hex-real-closure-nested-rerun.json"),
    (["Hex.RealClosure.Bench.runNativeRoots"], "/tmp/hex-real-closure-native-roots-rerun.json"),
]:
    cpu, lease = cpu_lease()
    try:
        print(f"selected CPU {cpu} for {output}", flush=True)
        subprocess.run(["taskset", "-c", str(cpu),
                        ".lake/build/bin/hexrealclosure_bench", "run", *names,
                        "--export-file", output], check=True)
    finally:
        lease.close()
PY
```

The exports record the source commits, and the context files record the
selected CPUs. The nested context file also records its source commit; a
rerun on current source is a new observation, not an extension of those runs.

The formal #10378 performance evaluation still requires the specified depth
and coefficient families, systematic nested sign and zero counts, BKR counts, splitting
and transport, clean/eager comparisons on identical semantic inputs, tower8
and MetiTarski workloads, and representative attribution.

## Complete native root construction

`runNativeRoots` executes the diagnostic complete producer and eagerly
materializes each selected native child for `-3X²(X²−2)³(X−3)⁵`. The timed
call includes zero extraction, Yun, isolation, global sorting, descriptor
encoding and prepared-domain construction for the returned children. Native
polynomial construction is outside the timed region; the input is read from
`IO.Ref`. The result check inspects ordered multiplicities `[3,2,3,5]` and
each actual child context's base identity and root depth.

The shared-host measurement on `chungus2`, CPU 14 selected by the CPU lease,
retains ten completed calls from clean source commit `1fdfd2886`. The median
was **10.667 ms**, with an observed range of **10.478–10.764 ms**; every call
returned the expected hash `0x1`. Peak child-process RSS was 69,268–70,036 kB.
The [export](native-roots-anchor.json), [log](native-roots-anchor.log), and
[context](native-roots-anchor-context.json) retain every sample, the exact
command, CPU affinity, host load, source revision and source/executable hashes. The export is a byte-for-byte copy of the path
named in the recorded command; its SHA-256 is recorded in the context.
The measurement preceded the rebase: `1fdfd2886` used base `321764a1f`,
and its patch is unchanged at `849923d67` over merged base `afdb1f7f0`.
The range comparison verifies all six native-root patches were unchanged;
the current benchmark source SHA-256 matches the measured source.
The executable hash identifies the measured pre-rebase build.

This fixed anchor measures the complete native operation on one rational input.
It establishes neither a scaling bound nor an overhead ratio against the
generic producer; those comparisons require adjacent measurements. The native
wrapper eagerly prepares each selected child even when the caller only needs
order or multiplicities. Full tower Phase-4 evaluation remains required.
