# HexBerlekampZassenhaus Performance Report

## Bench Targets

- `Hex.BerlekampZassenhausBench.runFactorChecksum`:
  `bzClassicalSmokeComplexity n = n^9 + n^7 * log2(n + 2)^2`
- `Hex.BerlekampZassenhausBench.runFactorFastChecksum`:
  `bzClassicalSmokeComplexity n`
- `Hex.BerlekampZassenhausBench.runFactorSlowChecksum`:
  `2^n * bzClassicalSmokeComplexity n`
- `Hex.BerlekampZassenhausBench.runFactorCompareChecksum`:
  `bzClassicalSmokeComplexity n`
- `Hex.BerlekampZassenhausBench.runFactorSlowCompareChecksum`:
  `2^n * bzClassicalSmokeComplexity n`
- `Hex.BerlekampZassenhausBench.runFactorFastCompareChecksum`:
  `bzClassicalSmokeComplexity n`
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

`verify` passed the registered benchmarks. With the shared-domain compare
registrations included, the current smoke suite has seventeen registered
benchmarks and `lake exe hexbz_bench verify` passes all seventeen.

## Comparator Ratios

`SPEC/Libraries/hex-berlekamp-zassenhaus.md` does not currently name an
external Phase-4 performance comparator in `libraries.yml` metadata, so
there are no external comparator ratios to record in this first report.

The internal fast/slow/public registrations are not yet a valid
`compare` group for the full scientific Phase 4 domain, but
`HexBerlekampZassenhaus/Bench.lean` now declares a narrow shared compare
domain over the deterministic split smoke family `smokeInput n` for
`n = 1..4`.

The public combinator versus exhaustive backstop check is:

```sh
lake exe hexbz_bench compare \
    Hex.BerlekampZassenhausBench.runFactorCompareChecksum \
    Hex.BerlekampZassenhausBench.runFactorSlowCompareChecksum
```

At commit `dcc0ed9-dirty` on `carica`, the harness reported common
parameters `1, 2, 3, 4` and `agreement: all functions agree on common
params`. The timing verdicts remained inconclusive, as expected for this
smoke-sized domain.

The same domain also admits the proof-facing fast path without hiding
fast-path misses:

```sh
lake exe hexbz_bench compare \
    Hex.BerlekampZassenhausBench.runFactorCompareChecksum \
    Hex.BerlekampZassenhausBench.runFactorSlowCompareChecksum \
    Hex.BerlekampZassenhausBench.runFactorFastCompareChecksum
```

`runFactorFastCompareChecksum` returns the same factorization checksum
when `factorFast` succeeds and an input-dependent sentinel on `none`.
The three-way check at commit `dcc0ed9-dirty` also reported common
parameters `1, 2, 3, 4` and `agreement: all functions agree on common
params`.

## Profile

A representative profile was recorded with `samply record --save-only
--unstable-presymbolicate` at commit `53771741e259` on `carica`
(Apple M2 Ultra, macOS 14.6.1), sampling at samply's default 1 kHz:

```sh
lake exe hexbz_bench profile \
    Hex.BerlekampZassenhausBench.runFactorDegreeHeightChecksum \
    --param 6032 --target-inner-nanos 1000000000 \
    --profiler "samply record --save-only --unstable-presymbolicate \
        -o reports/bench-results/profiles/hex-berlekamp-zassenhaus-factor-degree-height-5377174.json --"
```

Profile artefact:
`reports/bench-results/profiles/hex-berlekamp-zassenhaus-factor-degree-height-5377174.json`.
Samply also emitted the sidecar symbol table
`reports/bench-results/profiles/hex-berlekamp-zassenhaus-factor-degree-height-5377174.syms.json`.
The profiled child row was encoded degree/height parameter `6032`
(`degree = 6`, `height = 32`), with `inner_repeats=32`,
`per_call_nanos=19,662,252.625`, and result hash
`0x32829c6a8f776a64`.

The profile sampled the benchmark child, but the generated Firefox
Profiler JSON in this optimized macOS build retained address-only frame
names rather than demangled Lean names. The largest sampled worker
thread contained `658` samples; without symbol names, the leaf-cost
categories and inclusive `Hex.BerlekampZassenhaus.*` function ranking
cannot be reported to the standard required by `SPEC/profiling.md`.
The recorded sample still confirms that the representative public
degree/height target is profileable through the lean-bench child path.

## Concerns

- Phase 4 is not complete: every scientific verdict in this run was
  inconclusive.
- The current parametric schedules are still smoke-sized. The public,
  fast, and slow split-family schedules cover only `n = 1..4`, which
  is below the signal needed for a meaningful BHKS scaling verdict.
- The singleton HO-2 adversarial registrations are valuable fixed-shape
  coverage, but their `#[0]` schedules cannot produce verdict-eligible
  scaling rows.
- The new public/slow/fast compare surface is intentionally smoke-sized;
  it does not replace a full scientific-domain LLL-assisted versus
  exhaustive recombination comparison.
- `runFactorSlowDegreeHeightChecksum` hit the four-second cap at encoded
  parameter `4008`; the slow diagnostic needs either a smaller
  scientific subset or an explicitly larger timing budget.
- The profile artefact is address-only on this host, so the required
  leaf category split and inclusive Lean-function ranking remain open.
- `libraries.yml` has no `phase4.input_families` or comparator metadata
  for `HexBerlekampZassenhaus`; final Phase 4 coverage should add or
  explicitly justify that metadata before bumping `done_through`.
- HO-3 remains open as a complexity-evidence concern: this report adds
  the first benchmark/profile slice, but it does not yet establish the
  full Phase 4 verdict, comparator, and profile coverage required for
  the BZ implementation.
