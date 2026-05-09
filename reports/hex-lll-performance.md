# HexLLL Performance

Snapshot: commit `e211854d1435fbd3db4739cd6dec5be66da2f857` on host `carica`
(`arm64-apple-darwin24.6.0`, Lean `4.30.0-rc2`). Repair artefact:
`reports/bench-results/hex-lll-e211854d1435-repair-fixed.json`.

## Bench Targets

Parametric registrations from `HexLLL/Bench.lean`:

- `runOfBasisBzRecombinationChecksum n => ofBasisBzRecombinationComplexity n`
- `runOfBasisRandomBoundedChecksum n => ofBasisRandomBoundedComplexity n`
- `runOfBasisHarshCubicChecksum n => ofBasisHarshCubicComplexity n`
- `runSizeReduceColumnChecksum n => sizeReduceColumnComplexity n`
- `runSizeReduceChecksum n => sizeReduceComplexity n`
- `runSwapStepChecksum n => swapStepComplexity n`
- `runGramSchmidtCoeffLoopChecksum n => gramSchmidtCoeffComplexity n`
- `runPotential n => potentialComplexity n`
- `runFirstShortVectorRandomBoundedChecksum n => firstShortVectorRandomBoundedComplexity n`
- `runFirstShortVectorHarshCubicChecksum n => firstShortVectorHarshCubicComplexity n`

Fixed registrations include the BZ recombination first-short-vector hot path,
the bottom-rung Lean/fpylll comparisons, and the Lean/verified-Isabelle
norm-squared comparator rungs listed by `lake exe hexlll_bench list`.

## Verdicts

The repair run targeted the registrations named in #2809:

- `runSizeReduceChecksum`: consistent with declared complexity. Command:
  `lake exe hexlll_bench run Hex.LLLBench.runSizeReduceChecksum --export-file reports/bench-results/hex-lll-e211854d1435-repair-size-reduce.json`;
  params `80, 96, 112, 128, 144`; artefact row path merged into
  `reports/bench-results/hex-lll-e211854d1435-repair-fixed.json`, result
  `cMin=6.578`, `cMax=8.936`.
- `runGramSchmidtCoeffLoopChecksum`: consistent with declared complexity.
  Command: `lake exe hexlll_bench run Hex.LLLBench.runGramSchmidtCoeffLoopChecksum --export-file reports/bench-results/hex-lll-e211854d1435-repair-gram.json`;
  params `32, 64, 96, 128`; result `cMin=355924291.000`,
  `cMax=395213000.000`. This replaces the sub-resolution
  `runGramSchmidtCoeffChecksum` sweep with a fixed-iteration wrapper around
  the same projection.
- `runOfBasisHarshCubicChecksum`: consistent with declared complexity.
  Command: `lake exe hexlll_bench run Hex.LLLBench.runOfBasisHarshCubicChecksum --export-file reports/bench-results/hex-lll-e211854d1435-repair-ofbasis-harsh.json`;
  params `12, 18, 24, 30, 36`; result `cMin=7.609`, `cMax=10.024`.
- `runFirstShortVectorRandomBoundedChecksum`: consistent with declared
  complexity. Command:
  `lake exe hexlll_bench run Hex.LLLBench.runFirstShortVectorRandomBoundedChecksum --export-file reports/bench-results/hex-lll-e211854d1435-repair-random.json`;
  seed `randomBoundedSwapSeed = 8`; params `30, 60, 120, 240`; result
  `cMin=42.650`, `cMax=63.288`.
- `runFirstShortVectorHarshCubicChecksum`: consistent with declared
  complexity. Command:
  `lake exe hexlll_bench run Hex.LLLBench.runFirstShortVectorHarshCubicChecksum --export-file reports/bench-results/hex-lll-e211854d1435-repair-harsh.json`;
  params `15, 30, 45`; result `cMin=1.470`, `cMax=1.703`.

## Comparator Ratios

The verified-Isabelle comparator remains the gating comparator for HexLLL.
This repair did not rerun comparator ratios; #2810 tracks recording fpLLL
ratios on a fpylll-equipped benchmark host. HexLLL remains at
`done_through: 3` until comparator evidence and the remaining report concerns
are closed.

## Profile

No new profile was collected in this repair run. The relevant previously filed
profile finding was the redundant Bareiss pass in `LLLState.ofBasis`, tracked
by #2689; the current `ofBasis` bench model and implementation use the shared
`GramSchmidt.Int.data` path. A full Phase-4 profile snapshot still needs one
representative case per `phase4.input_families` entry before re-promotion.

## Concerns

- #2810: record fpLLL comparator ratios on a fpylll-equipped benchmark host.
- Full Phase-4 re-promotion is still blocked until the comparator ratios and
  representative profile artefacts are present in this report.
