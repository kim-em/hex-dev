# HexBerlekampZassenhaus Performance Report

## Bench Targets

- `Hex.BerlekampZassenhausBench.runFactorChecksum`:
  `bzClassicalSmokeComplexity n = n^9 + n^7 * log2(n + 2)^2`
- `Hex.BerlekampZassenhausBench.runFactorFastChecksum`:
  `bzClassicalSmokeComplexity n`
- `Hex.BerlekampZassenhausBench.runFactorSlowChecksum`:
  `2^n * bzClassicalSmokeComplexity n`
- `Hex.BerlekampZassenhausBench.runFactorDegreeHeightChecksum`:
  `bzClassicalDegreeHeightComplexity param = n^9 + n^7 * log2(height + 2)^2`
- `Hex.BerlekampZassenhausBench.runFactorFastDegreeHeightChecksum`:
  `bzClassicalDegreeHeightComplexity param`
- `Hex.BerlekampZassenhausBench.runFactorSlowDegreeHeightChecksum`:
  `bzSlowDegreeHeightComplexity param = 2^n * bzClassicalDegreeHeightComplexity param`
- `Hex.BerlekampZassenhausBench.runFactorAdvX4Plus1Checksum`: `n + 1`
- `Hex.BerlekampZassenhausBench.runFactorFastSetupAdvX4Plus1Checksum`: `n + 1`
- `Hex.BerlekampZassenhausBench.runFactorAdvQuadSqrt2Sqrt3Checksum`: `n + 1`
- `Hex.BerlekampZassenhausBench.runFactorFastAdvQuadSqrt2Sqrt3Checksum`: `n + 1`
- `Hex.BerlekampZassenhausBench.runFactorAdvPhi15Checksum`: `n + 1`
- `Hex.BerlekampZassenhausBench.runFactorFastSetupAdvPhi15Checksum`: `n + 1`
- `Hex.BerlekampZassenhausBench.runAdvSwinnertonDyerSD3ModularSplitChecksum`: `n + 1`

## Verdicts

Scientific run at commit `53771741e259` on `carica` (Apple M2 Ultra,
macOS 14.6.1), command:

```sh
lake exe hexbz_bench run \
    Hex.BerlekampZassenhausBench.runFactorChecksum \
    Hex.BerlekampZassenhausBench.runFactorFastChecksum \
    Hex.BerlekampZassenhausBench.runFactorSlowChecksum \
    Hex.BerlekampZassenhausBench.runFactorDegreeHeightChecksum \
    Hex.BerlekampZassenhausBench.runFactorFastDegreeHeightChecksum \
    Hex.BerlekampZassenhausBench.runFactorSlowDegreeHeightChecksum \
    Hex.BerlekampZassenhausBench.runFactorAdvX4Plus1Checksum \
    Hex.BerlekampZassenhausBench.runFactorFastSetupAdvX4Plus1Checksum \
    Hex.BerlekampZassenhausBench.runFactorAdvQuadSqrt2Sqrt3Checksum \
    Hex.BerlekampZassenhausBench.runFactorFastAdvQuadSqrt2Sqrt3Checksum \
    Hex.BerlekampZassenhausBench.runFactorAdvPhi15Checksum \
    Hex.BerlekampZassenhausBench.runFactorFastSetupAdvPhi15Checksum \
    Hex.BerlekampZassenhausBench.runAdvSwinnertonDyerSD3ModularSplitChecksum \
    --export-file reports/bench-results/hex-berlekamp-zassenhaus-5377174.json
```

Export artefact:
`reports/bench-results/hex-berlekamp-zassenhaus-5377174.json`,
SHA-256
`c8ff1c722a08cf167650fee2c657888c1acef3f29db6d005e399afc7473648eb`.
The harness recorded `5377174-dirty` because this worktree carried a
pre-existing `.claude/CLAUDE.md` modification outside this report package.
No random seeds are involved; all inputs are deterministic fixtures from
`HexBerlekampZassenhaus/Bench.lean`.

All timing verdicts were inconclusive, so this report is evidence for the
current benchmark surface, not a Phase 4 completion claim.

- `runFactorChecksum`: inconclusive (`cMin=2.627`, `cMax=349.381`,
  parameters `1..4`, final hash `0xa8661221fc80f3ce`).
- `runFactorFastChecksum`: inconclusive (`cMin=2.635`,
  `cMax=342.306`, parameters `1..4`, final hash
  `0x2bd50d22a8975715`).
- `runFactorSlowChecksum`: inconclusive (`cMin=0.345`,
  `cMax=109.951`, parameters `1..4`, final hash
  `0xa8661221fc80f3ce`).
- `runFactorDegreeHeightChecksum`: inconclusive (`cMin=1.120`,
  `cMax=42.206`, encoded parameters `3002..6032`, final hash
  `0x32829c6a8f776a64`).
- `runFactorFastDegreeHeightChecksum`: inconclusive (`cMin=1.109`,
  `cMax=43.058`, encoded parameters `3002..6032`, final hash
  `0x9e9f6f21a6040eef`).
- `runFactorSlowDegreeHeightChecksum`: inconclusive; parameters
  `2002` and `3008` completed, while `4008` hit the
  `maxSecondsPerCall = 4.0s` cap.
- The seven singleton HO-2 adversarial/setup registrations all ran and
  produced stable hashes, but each has only the pinned `n = 0` row and
  therefore no verdict-eligible scaling ladder.

Smoke wiring was checked at the same commit with:

```sh
lake exe hexbz_bench list
lake exe hexbz_bench verify
```

`verify` passed all thirteen registered benchmarks.

## Comparator Ratios

`SPEC/Libraries/hex-berlekamp-zassenhaus.md` does not currently name an
external Phase-4 performance comparator in `libraries.yml` metadata, so
there are no external comparator ratios to record in this first report.

The internal fast/slow/public registrations are not yet a valid
`compare` group: they overlap on smoke fixtures, but the benchmark module
does not declare a shared scientific comparison domain for
LLL-assisted recombination versus exhaustive recombination.

## Profile

A representative `degree-height-matrix` profile was recorded with
`samply record --save-only --unstable-presymbolicate` at commit
`06d996d749e3` on `carica` (Apple M2 Ultra, macOS 14.6.1), sampling at
1 kHz. The worktree was dirty only because `.claude/CLAUDE.md` carried a
pre-existing agent-context change outside this report package. The raw
Firefox Profiler JSON and `.syms.json` sidecar are developer-local at
`/tmp/hex-profiles/hex-bz-degree-height-child-06d996d.{json,syms.json}`.

```sh
samply record --save-only --unstable-presymbolicate --include-args=6 \
    --rate 1000 \
    -o /tmp/hex-profiles/hex-bz-degree-height-child-06d996d.json -- \
    .lake/build/bin/hexbz_bench _child \
        --bench Hex.BerlekampZassenhausBench.runFactorDegreeHeightChecksum \
        --param 6032 --target-nanos 1000000000
```

The profiled child row was encoded degree/height parameter `6032`
(`degree = 6`, `height = 32`), with `inner_repeats=32`,
`per_call_nanos=19,006,277.343750`, and result hash
`0x32829c6a8f776a64`. The profile's main worker thread contained `635`
sample rows with total sample weight `679`; the sidecar symbol table was
used for Lean-name attribution because the Firefox JSON itself keeps
address strings.

Leaf self-time categories for that worker thread:

- Lean own code: `51 / 679 = 7.5%`.
- GMP big-integer arithmetic: `60 / 679 = 8.8%`.
- Allocation / free: `222 / 679 = 32.7%`.
- Lean runtime and dispatch: `200 / 679 = 29.5%`.
- Other system frames: `146 / 679 = 21.5%`, dominated by profiler I/O
  and platform frames such as `__read_nocancel` and thread-local lookup.

Top inclusive BZ-library costs:

- `Hex.factorWithBound`: `621 / 679 = 91.5%`.
- `Hex.factorFastWithBound`: `621 / 679 = 91.5%`.
- `Hex.factorFastFactorsWithBound`: `621 / 679 = 91.5%`.
- `Hex.choosePrimeData?`: `586 / 679 = 86.3%`.
- `Hex.primeChoiceDataScore`: `586 / 679 = 86.3%`.
- `Hex.berlekampFactorsModP`: `574 / 679 = 84.5%`.
- `Hex.factorFastCoreWithBound`: `32 / 679 = 4.7%`.
- `Hex.bhksRecoverClassified`: `23 / 679 = 3.4%`.
- `Hex.bhksLatticeBasis`: `18 / 679 = 2.7%`.

The dominant inclusive path is the public `factorWithBound` call through
the fast-path attempt, especially prime selection and modular
factorization (`choosePrimeData?`, `primeChoiceDataScore`, and
`berlekampFactorsModP`). The BHKS recombination body is present but much
smaller on this split degree/height case. This profile therefore maps its
dominant BZ costs to the registered
`runFactorDegreeHeightChecksum`/`runFactorFastDegreeHeightChecksum`
targets and leaves the broader Phase 4 verdict/schedule concerns below
unchanged.

## Concerns

- Phase 4 is not complete: every scientific verdict in this run was
  inconclusive.
- The current parametric schedules are still smoke-sized. The public,
  fast, and slow split-family schedules cover only `n = 1..4`, which
  is below the signal needed for a meaningful BHKS scaling verdict.
- The singleton HO-2 adversarial registrations are valuable fixed-shape
  coverage, but their `#[0]` schedules cannot produce verdict-eligible
  scaling rows.
- `runFactorSlowDegreeHeightChecksum` hit the four-second cap at encoded
  parameter `4008`; the slow diagnostic needs either a smaller
  scientific subset or an explicitly larger timing budget.
- `libraries.yml` now records `phase4.input_families` for
  `HexBerlekampZassenhaus`, but it still has no comparator metadata;
  final Phase 4 coverage should add or explicitly justify comparator
  metadata before bumping `done_through`.
- HO-3 remains open as a complexity-evidence concern: this report adds
  the first benchmark/profile slice, but it does not yet establish the
  full Phase 4 verdict, comparator, and profile coverage required for
  the BZ implementation.
