# HexGramSchmidt Performance Report

## Bench Targets

- `Hex.GramSchmidtBench.runGramDetVecChecksum`: `gramSurfaceComplexity n`
- `Hex.GramSchmidtBench.runScaledCoeffsChecksum`: `scaledCoeffSurfaceComplexity n`
- `Hex.GramSchmidtBench.runSizeReduceChecksum`: `rowUpdateComplexity n`
- `Hex.GramSchmidtBench.runAdjacentSwapChecksum`: `rowUpdateComplexity n`
- `Hex.GramSchmidtBench.runAdjacentSwapDenom`: `updateGramComplexity n`
- `Hex.GramSchmidtBench.runAdjacentSwapPivotCoeff`: `updateScaledCoeffComplexity n`
- `Hex.GramSchmidtBench.runAdjacentSwapGramDetNumerator`: `updateScaledCoeffComplexity n`
- `Hex.GramSchmidtBench.runAdjacentSwapGramDetQuotient`: `updateScaledCoeffComplexity n`
- `Hex.GramSchmidtBench.runAdjacentSwapScaledCoeffAbovePrevNumerator`: `updateScaledCoeffComplexity n`
- `Hex.GramSchmidtBench.runAdjacentSwapScaledCoeffAboveCurrNumerator`: `updateScaledCoeffComplexity n`

## Verdicts

Scientific run at commit `33b7f720dcce514b455e26d27c402b415c192cd8` on
`carica` (Apple M2 Ultra, macOS 14.6.1), command:

```sh
lake exe hexgramschmidt_bench run Hex.GramSchmidtBench.runAdjacentSwapScaledCoeffAboveCurrNumerator Hex.GramSchmidtBench.runAdjacentSwapGramDetQuotient Hex.GramSchmidtBench.runAdjacentSwapGramDetNumerator Hex.GramSchmidtBench.runAdjacentSwapDenom Hex.GramSchmidtBench.runScaledCoeffsChecksum Hex.GramSchmidtBench.runSizeReduceChecksum Hex.GramSchmidtBench.runGramDetVecChecksum Hex.GramSchmidtBench.runAdjacentSwapChecksum Hex.GramSchmidtBench.runAdjacentSwapPivotCoeff Hex.GramSchmidtBench.runAdjacentSwapScaledCoeffAbovePrevNumerator --export-file reports/bench-results/hex-gram-schmidt-33b7f720dcce.json
```

The run used deterministic benchmark inputs from `HexGramSchmidt/Bench.lean`;
random seeds are not involved. The harness recorded `33b7f72-dirty` because
this worktree had an unrelated pre-existing `.claude/CLAUDE.md` modification.
Export artefact: `reports/bench-results/hex-gram-schmidt-33b7f720dcce.json`.

- `Hex.GramSchmidtBench.runAdjacentSwapScaledCoeffAboveCurrNumerator`:
  consistent with declared complexity (parameters `4..12`, final hash `0x0`).
- `Hex.GramSchmidtBench.runAdjacentSwapGramDetQuotient`: consistent with
  declared complexity (parameters `8..16`, final hash `0x0`).
- `Hex.GramSchmidtBench.runAdjacentSwapGramDetNumerator`: consistent with
  declared complexity (parameters `3..6`, final hash `0x0`).
- `Hex.GramSchmidtBench.runAdjacentSwapDenom`: consistent with declared
  complexity (parameters `3..6`, final hash `0x0`).
- `Hex.GramSchmidtBench.runScaledCoeffsChecksum`: consistent with declared
  complexity (parameters `16..28`, final hash `0x1faa927eed9457c0`).
- `Hex.GramSchmidtBench.runSizeReduceChecksum`: consistent with declared
  complexity (parameters `64..192`, final hash `0xcc0cc58a0103fffd`).
- `Hex.GramSchmidtBench.runGramDetVecChecksum`: consistent with declared
  complexity (parameters `24..40`, final hash `0x44081a7e58a8d145`).
- `Hex.GramSchmidtBench.runAdjacentSwapChecksum`: consistent with declared
  complexity (parameters `64..192`, final hash `0x5824c79201060000`).
- `Hex.GramSchmidtBench.runAdjacentSwapPivotCoeff`: consistent with declared
  complexity (parameters `8..16`, final hash `0x0`).
- `Hex.GramSchmidtBench.runAdjacentSwapScaledCoeffAbovePrevNumerator`:
  consistent with declared complexity (parameters `4..12`, final hash `0x0`).

Smoke wiring was also checked with:

```sh
lake exe hexgramschmidt_bench list
lake exe hexgramschmidt_bench verify
```

`verify` passed all 10 registered benchmarks at the same commit.

## Comparator Ratios

`SPEC/Libraries/hex-gram-schmidt.md` does not name an external Phase-4
performance comparator for `HexGramSchmidt`, so there are no comparator ratios
to record in this snapshot.

## Profile

Profiles were recorded on `carica` (Apple M2 Ultra, macOS 15.6) with
`scripts/profile/run_profile.sh`, which runs `samply 0.13.1` and filters the
Firefox Profiler JSON to samples on the bench thread inside lean-bench timed
regions. The raw filtered JSON artefacts are developer-local and are not
committed.

### `integer-gram-surface`

Command:

```sh
scripts/profile/run_profile.sh ./.lake/build/bin/hexgramschmidt_bench Hex.GramSchmidtBench.runGramDetVecChecksum 40 5000000000
```

Diagnostics:

```json
{
  "schema": 1,
  "regions_total": 3,
  "total_timed_ms": 4237.883584,
  "expected_samples_bench_thread": 4233.6,
  "retained_samples_bench_thread": 4232,
  "rejected_samples_bench_thread": 10,
  "off_bench_thread_samples_in_window": 2,
  "samply_interval_ms": 1.001001,
  "spawn_anchor_wall_ns": 1780142549751865000,
  "spawn_anchor_mono_ns": 330583671875291,
  "sidecar_mono_anchor_ns": 330584940211208,
  "samply_meta_start_time_ms": 1780142549768.282
}
```

Representative case: deterministic `40 x 81` integer bases, no seed. Leaf
samples were allocation/free 39.9%, Lean runtime/system 23.1%, GMP big-integer
arithmetic 19.6%, and Hex/Lean own code 17.4%. Inclusive HexGramSchmidt cost was
led by `runGramDetVecChecksum` (100.0%), `GramSchmidt.Int.gramDetVec` (99.0%),
`GramSchmidt.Int.data` (98.7%), `GramSchmidt.Int.scaledCoeffRows` (98.5%), the
private `scaledCoeffArrayLoop` (73.8%), the HexMatrix step-array path (67.4%),
the Gram-row construction maps (24.4% and 24.2%), vector dot products (24.1%),
and `Matrix.exactDiv` (10.2%).

The dominant work is the registered Gram determinant vector target. The newly
visible split is mostly allocation, Lean runtime dispatch/refcounting, and GMP
integer traffic inside the same `gramDetVec`/`scaledCoeffRows` computation; no
unregistered dominant helper appears.

### `row-update-helpers`

Command:

```sh
scripts/profile/run_profile.sh ./.lake/build/bin/hexgramschmidt_bench Hex.GramSchmidtBench.runAdjacentSwapChecksum 192 5000000000
```

Diagnostics:

```json
{
  "schema": 1,
  "regions_total": 7,
  "total_timed_ms": 2945.091875,
  "expected_samples_bench_thread": 2942.1,
  "retained_samples_bench_thread": 2942,
  "rejected_samples_bench_thread": 10,
  "off_bench_thread_samples_in_window": 2,
  "samply_interval_ms": 1.001001,
  "spawn_anchor_wall_ns": 1780142624851832000,
  "spawn_anchor_mono_ns": 330658772665250,
  "sidecar_mono_anchor_ns": 330659019675250,
  "samply_meta_start_time_ms": 1780142624859.801
}
```

Representative case: deterministic small-entry update fixture at parameter
`192`, no seed. Leaf samples were allocation/free 63.2%, GMP big-integer
arithmetic 22.9%, Lean runtime/system 10.8%, and Hex/Lean own code 3.1%.
Inclusive HexGramSchmidt cost was led by `runAdjacentSwapChecksum` (99.8%),
`intRowPairChecksum` (99.6%), and the nested `intRowChecksum` fold (96.7%).

The profile shows that the timed region is dominated by the registered
adjacent-swap checksum target's affected-row checksum over `Int` entries, with
GMP limb copies and allocator traffic accounting for most leaf samples. That
cost is part of the registered benchmark surface and is not an unattributed
production helper.

### `adjacent-swap-scalars`

Command:

```sh
scripts/profile/run_profile.sh ./.lake/build/bin/hexgramschmidt_bench Hex.GramSchmidtBench.runAdjacentSwapGramDetQuotient 16 5000000000
```

Diagnostics:

```json
{
  "schema": 1,
  "regions_total": 6,
  "total_timed_ms": 3552.032542,
  "expected_samples_bench_thread": 3548.5,
  "retained_samples_bench_thread": 3549,
  "rejected_samples_bench_thread": 7,
  "off_bench_thread_samples_in_window": 2,
  "samply_interval_ms": 1.001001,
  "spawn_anchor_wall_ns": 1780142638224799000,
  "spawn_anchor_mono_ns": 330672145779416,
  "sidecar_mono_anchor_ns": 330672393369416,
  "samply_meta_start_time_ms": 1780142638231.257
}
```

Representative case: adjacent-swap scalar helper formula at parameter `16`, no
seed. Leaf samples were Lean runtime/system 46.5%, Hex/Lean own code 37.4%, and
allocation/free 16.2%; GMP did not appear as a separate dominant leaf category
in this run. Inclusive HexGramSchmidt cost was led by
`adjacentSwapGramDetQuotient` (100.0%), vector dot products (91.2%),
`adjacentSwapGramDetNumerator` (75.9%), `GramSchmidt.Int.gramDet` (72.4%),
leading Gram-matrix construction (66.6%), `adjacentSwapPivotCoeff` (27.5%),
`scaledCoeffs`/`data` (27.5%), and `scaledCoeffRows` (27.0%).

The dominant work maps to the registered adjacent-swap scalar helper target and
its registered supporting scalar targets. The filtered profile makes Lean
closure dispatch/refcounting and allocation visible, but the inclusive hot path
remains the quotient/numerator/Gram-determinant computation covered by the
existing registrations.

## Concerns

No Attribution-rule concern surfaced in the filtered profiles.
