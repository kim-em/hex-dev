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

Profiles were recorded with `samply record --save-only` at the same commit on
`carica` (Apple M2 Ultra, macOS 14.6.1), at the default 1 kHz sampling rate.
The raw Firefox Profiler JSON artefacts are developer-local and are not
committed.

### `integer-gram-surface`

Command:

```sh
samply record --save-only -o reports/bench-results/profiles/hex-gram-schmidt-gram-surface-33b7f720dcce.json -- lake exe hexgramschmidt_bench run Hex.GramSchmidtBench.runGramDetVecChecksum
```

Representative case: deterministic `n x (2n + 1)` integer bases, parameters
`24..40`, no seed. Leaf samples were own compiled code 86.4%, kernel/syscall
wait 9.3%, allocation/free 3.7%, and loader/runtime remainder 0.6%. Inclusive
HexGramSchmidt cost was led by `runGramDetVecChecksum` (71.2%),
`GramSchmidt.Int.gramDetVec` (55.0%), `Matrix.bareissNoPivotData` (55.0%),
and the Gram-matrix construction path (16.1%). The dominant work maps to the
registered Gram determinant vector target.

### `row-update-helpers`

Command:

```sh
samply record --save-only -o reports/bench-results/profiles/hex-gram-schmidt-row-update-33b7f720dcce.json -- lake exe hexgramschmidt_bench run Hex.GramSchmidtBench.runAdjacentSwapChecksum
```

Representative case: deterministic small-entry update fixtures, parameters
`64..192`, no seed. Leaf samples were own compiled code 87.2%, kernel/syscall
wait 11.0%, allocation/free 1.2%, and runtime remainder 0.6%. Inclusive
HexGramSchmidt cost was led by `runAdjacentSwapChecksum` (69.6%) and the
checksum folds over the two affected rows (34.1% and 32.9%). The row operation
itself is registered directly, and the observed checksum cost is part of the
registered benchmark target rather than an unattributed production helper.

### `adjacent-swap-scalars`

Command:

```sh
samply record --save-only -o reports/bench-results/profiles/hex-gram-schmidt-swap-scalar-33b7f720dcce.json -- lake exe hexgramschmidt_bench run Hex.GramSchmidtBench.runAdjacentSwapGramDetQuotient
```

Representative case: adjacent-swap scalar helper formulas, parameters `8..16`,
no seed. Leaf samples were own compiled code 83.6%, kernel/syscall wait 9.4%,
loader/runtime 3.7%, allocation/free 2.5%, and other system 0.8%. Inclusive
HexGramSchmidt cost was led by `adjacentSwapGramDetQuotient` (51.9%),
`GramSchmidt.Int.gramDet` (48.3%), leading Gram-matrix construction (47.6%),
integer row dot products (31.1% and 26.3%), and `scaledCoeffs` under the pivot
coefficient path (17.2%). These costs map to the registered adjacent-swap
scalar helper targets.

## Concerns
