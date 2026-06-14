# HexLLL Performance Report

## Bench Targets

- `Hex.LLLBench.runSwapStepChecksum`: `swapStepComplexity n`
- `Hex.LLLBench.runSizeReduceChecksum`: `sizeReduceComplexity n`
- `Hex.LLLBench.runOfBasisRandomBoundedChecksum`: `ofBasisRandomBoundedComplexity n`
- `Hex.LLLBench.runOfBasisBzRecombinationChecksum`: `ofBasisBzRecombinationComplexity n`
- `Hex.LLLBench.runGramSchmidtCoeffChecksum`: `gramSchmidtCoeffComplexity n`
- `Hex.LLLBench.runFirstShortVectorHarshCubicChecksum`: `firstShortVectorHarshCubicComplexity n`
- `Hex.LLLBench.runPotential`: `potentialComplexity n`
- `Hex.LLLBench.runOfBasisHarshCubicChecksum`: `ofBasisHarshCubicComplexity n`
- `Hex.LLLBench.runFirstShortVectorRandomBoundedChecksum`: `firstShortVectorRandomBoundedComplexity n`
- `Hex.LLLBench.runSizeReduceColumnChecksum`: `sizeReduceColumnComplexity n`
- `Hex.LLLBench.runFpylllFirstShortVectorBZRecombinationChecksum`: fixed, repeats `5`
- `Hex.LLLBench.runIsabelleHarshCubicNormSq15`: fixed, repeats `3`
- `Hex.LLLBench.runFirstShortVectorBZRecombinationNormSq`: fixed, repeats `3`
- `Hex.LLLBench.runIsabelleHarshCubicNormSq45`: fixed, repeats `3`
- `Hex.LLLBench.runFirstShortVectorBZRecombinationChecksum`: fixed, repeats `5`
- `Hex.LLLBench.runIsabelleHarshCubicNormSq30`: fixed, repeats `3`
- `Hex.LLLBench.runFirstShortVectorHarshCubic15Checksum`: fixed, repeats `5`
- `Hex.LLLBench.runIsabelleRandomBoundedNormSq120`: fixed, repeats `3`
- `Hex.LLLBench.runFirstShortVectorRandomBoundedNormSq30`: fixed, repeats `3`
- `Hex.LLLBench.runFirstShortVectorRandomBoundedNormSq120`: fixed, repeats `3`
- `Hex.LLLBench.runFirstShortVectorHarshCubicNormSq30`: fixed, repeats `3`
- `Hex.LLLBench.runFirstShortVectorRandomBounded30Checksum`: fixed, repeats `5`
- `Hex.LLLBench.runFirstShortVectorRandomBoundedNormSq45`: fixed, repeats `3`
- `Hex.LLLBench.runFirstShortVectorHarshCubicNormSq45`: fixed, repeats `3`
- `Hex.LLLBench.runFirstShortVectorRandomBoundedNormSq75`: fixed, repeats `3`
- `Hex.LLLBench.runFirstShortVectorRandomBoundedNormSq90`: fixed, repeats `3`
- `Hex.LLLBench.runFirstShortVectorRandomBoundedNormSq150`: fixed, repeats `3`
- `Hex.LLLBench.runFirstShortVectorRandomBoundedNormSq180`: fixed, repeats `3`
- `Hex.LLLBench.runFpylllFirstShortVectorHarshCubic15Checksum`: fixed, repeats `5`
- `Hex.LLLBench.runFirstShortVectorHarshCubicNormSq20`: fixed, repeats `3`
- `Hex.LLLBench.runFirstShortVectorHarshCubicNormSq25`: fixed, repeats `3`
- `Hex.LLLBench.runIsabelleRandomBoundedNormSq30`: fixed, repeats `3`
- `Hex.LLLBench.runIsabelleRandomBoundedNormSq45`: fixed, repeats `3`
- `Hex.LLLBench.runIsabelleRandomBoundedNormSq60`: fixed, repeats `3`
- `Hex.LLLBench.runIsabelleRandomBoundedNormSq75`: fixed, repeats `3`
- `Hex.LLLBench.runIsabelleRandomBoundedNormSq90`: fixed, repeats `3`
- `Hex.LLLBench.runIsabelleRandomBoundedNormSq120`: fixed, repeats `3`
- `Hex.LLLBench.runIsabelleRandomBoundedNormSq150`: fixed, repeats `3`
- `Hex.LLLBench.runIsabelleRandomBoundedNormSq180`: fixed, repeats `3`
- `Hex.LLLBench.runFpylllFirstShortVectorRandomBounded30Checksum`: fixed, repeats `5`
- `Hex.LLLBench.runFpylllFirstShortVectorRandomBounded45Checksum`: fixed, repeats `5`
- `Hex.LLLBench.runFpylllFirstShortVectorRandomBounded60Checksum`: fixed, repeats `5`
- `Hex.LLLBench.runFpylllFirstShortVectorRandomBounded75Checksum`: fixed, repeats `5`
- `Hex.LLLBench.runFpylllFirstShortVectorRandomBounded90Checksum`: fixed, repeats `5`
- `Hex.LLLBench.runFpylllFirstShortVectorRandomBounded120Checksum`: fixed, repeats `5`
- `Hex.LLLBench.runFpylllFirstShortVectorRandomBounded150Checksum`: fixed, repeats `5`
- `Hex.LLLBench.runFpylllFirstShortVectorRandomBounded180Checksum`: fixed, repeats `5`
- `Hex.LLLBench.runFpylllFirstShortVectorHarshCubic20Checksum`: fixed, repeats `5`
- `Hex.LLLBench.runFpylllFirstShortVectorHarshCubic25Checksum`: fixed, repeats `5`
- `Hex.LLLBench.runFpylllFirstShortVectorHarshCubic30Checksum`: fixed, repeats `5`
- `Hex.LLLBench.runFpylllFirstShortVectorHarshCubic35Checksum`: fixed, repeats `5`
- `Hex.LLLBench.runFpylllFirstShortVectorHarshCubic40Checksum`: fixed, repeats `5`
- `Hex.LLLBench.runFpylllFirstShortVectorHarshCubic45Checksum`: fixed, repeats `5`
- `Hex.LLLBench.runFpylllFirstShortVectorHarshCubic50Checksum`: fixed, repeats `5`
- `Hex.LLLBench.runFpylllFirstShortVectorHarshCubic55Checksum`: fixed, repeats `5`
- `Hex.LLLBench.runCertifiedFirstShortVectorRandomBounded{30,45,60,75,90,120,150,180}Checksum`: fixed, repeats `3`
- `Hex.LLLBench.runCertifiedCheckerRandomBounded{30,45,60,75,90,120,150,180}Checksum`: fixed, repeats `3`
- `Hex.LLLBench.runCertifiedFirstShortVectorHarshCubic{15,20,25,30,35,40,45,50,55,60,65}Checksum`: fixed, repeats `3`
- `Hex.LLLBench.runCertifiedCheckerHarshCubic{15,20,25,30,35,40,45,50,55,60,65}Checksum`: fixed, repeats `3`
- `Hex.LLLBench.runDispatchedFirstShortVectorRandomBounded30Checksum`: fixed, repeats `3`
- `Hex.LLLBench.runDispatchedFirstShortVectorHarshCubic15Checksum`: fixed, repeats `3`
- `Hex.LLLBench.runFirstShortVectorHarshCubicNormSq15`: fixed, repeats `3`
- `Hex.LLLBench.runFirstShortVectorHarshCubicNormSq35`: fixed, repeats `3`
- `Hex.LLLBench.runFirstShortVectorHarshCubicNormSq40`: fixed, repeats `3`
- `Hex.LLLBench.runFirstShortVectorHarshCubicNormSq50`: fixed, repeats `3`
- `Hex.LLLBench.runFirstShortVectorHarshCubicNormSq55`: fixed, repeats `3`
- `Hex.LLLBench.runIsabelleBZRecombinationNormSq`: fixed, repeats `3`
- `Hex.LLLBench.runIsabelleHarshCubicNormSq20`: fixed, repeats `3`
- `Hex.LLLBench.runIsabelleHarshCubicNormSq25`: fixed, repeats `3`
- `Hex.LLLBench.runIsabelleHarshCubicNormSq35`: fixed, repeats `3`
- `Hex.LLLBench.runIsabelleHarshCubicNormSq40`: fixed, repeats `3`
- `Hex.LLLBench.runIsabelleHarshCubicNormSq50`: fixed, repeats `3`
- `Hex.LLLBench.runIsabelleHarshCubicNormSq55`: fixed, repeats `3`
- `Hex.LLLBench.runFirstShortVectorRandomBoundedNormSq60`: fixed, repeats `3`
- `Hex.LLLBench.runIsabelleCertifiedRandomBoundedNormSq{30,45,60,75,90,120,150,180}`: fixed, repeats `3`
- `Hex.LLLBench.runIsabelleCertifiedHarshCubicNormSq{15,20,25,30,35,40,45,50,55,60,65}`: fixed, repeats `3`

## Verdicts

Scientific run at commit `885431ee1d594b5f6a480cbcfa8f4389e3e3383d` on
`carica` (Apple M2 Ultra, macOS 14.6.1), command:

```sh
lake exe hexlll_bench run Hex.LLLBench.runSwapStepChecksum Hex.LLLBench.runSizeReduceChecksum Hex.LLLBench.runOfBasisRandomBoundedChecksum Hex.LLLBench.runOfBasisBzRecombinationChecksum Hex.LLLBench.runGramSchmidtCoeffChecksum Hex.LLLBench.runFirstShortVectorHarshCubicChecksum Hex.LLLBench.runPotential Hex.LLLBench.runOfBasisHarshCubicChecksum Hex.LLLBench.runFirstShortVectorRandomBoundedChecksum Hex.LLLBench.runSizeReduceColumnChecksum Hex.LLLBench.runFirstShortVectorBZRecombinationChecksum Hex.LLLBench.runFirstShortVectorHarshCubic15Checksum Hex.LLLBench.runFirstShortVectorRandomBounded30Checksum Hex.LLLBench.runFirstShortVectorBZRecombinationNormSq Hex.LLLBench.runFirstShortVectorRandomBoundedNormSq30 Hex.LLLBench.runFirstShortVectorRandomBoundedNormSq60 Hex.LLLBench.runFirstShortVectorRandomBoundedNormSq120 Hex.LLLBench.runFirstShortVectorRandomBoundedNormSq240 Hex.LLLBench.runFirstShortVectorHarshCubicNormSq15 Hex.LLLBench.runFirstShortVectorHarshCubicNormSq30 Hex.LLLBench.runFirstShortVectorHarshCubicNormSq45 --export-file reports/bench-results/hex-lll-885431e.json
```

The run used deterministic inputs from `HexLLL/Bench.lean`; the
random-bounded family uses committed seed `8`. The harness recorded
`885431e-dirty` because this worktree had an unrelated pre-existing
`.claude/CLAUDE.md` modification. Export artefact:
`reports/bench-results/hex-lll-885431e.json`.

- `Hex.LLLBench.runSwapStepChecksum`: consistent with declared complexity
  (parameters `96..160`, final per-call `521.412 us`).
- `Hex.LLLBench.runSizeReduceChecksum`: consistent with declared complexity
  (parameters `128..160`, final per-call `495.222 us`).
- `Hex.LLLBench.runOfBasisRandomBoundedChecksum`: consistent with declared
  complexity (parameters `48..144`, final verdict-row per-call `190.800 ms`
  at `n = 120`; the `n = 144` row was below the signal floor and excluded).
- `Hex.LLLBench.runOfBasisBzRecombinationChecksum`: consistent with declared
  complexity (parameters `24..72`, final verdict-row per-call `42.606 ms`
  at `n = 60`; the `n = 72` row was below the signal floor and excluded).
- `Hex.LLLBench.runGramSchmidtCoeffChecksum`: consistent with declared
  complexity (parameters `32..128`, final per-call `1.168 us`).
- `Hex.LLLBench.runFirstShortVectorHarshCubicChecksum`: consistent with
  declared complexity (parameters `15..45`, final per-call `178.802 ms`).
- `Hex.LLLBench.runPotential`: consistent with declared complexity
  (parameters `192..216`, final per-call `5.552 ms`).
- `Hex.LLLBench.runOfBasisHarshCubicChecksum`: consistent with declared
  complexity (parameters `12..36`, final per-call `35.258 ms`).
- `Hex.LLLBench.runFirstShortVectorRandomBoundedChecksum`: consistent with
  declared complexity (parameters `30..240`, final per-call `6.060 s`).
- `Hex.LLLBench.runSizeReduceColumnChecksum`: consistent with declared
  complexity (parameters `96..160`, final per-call `439.083 us`).
- `Hex.LLLBench.runFirstShortVectorBZRecombinationChecksum`: median
  `6.334 us`, observed hash `0x3c0064007a0036`, expected hash matches.
- `Hex.LLLBench.runFirstShortVectorHarshCubic15Checksum`: median `1.170 ms`,
  observed hash `0x949fde47fa1fffb4`, expected hash matches.
- `Hex.LLLBench.runFirstShortVectorRandomBounded30Checksum`: median
  `5.602 ms`, observed hash `0xf977db3a0120001a`, expected hash matches.
- `Hex.LLLBench.runFirstShortVectorBZRecombinationNormSq`: median
  `5.500 us`, observed hash `0x4e6`, expected hash matches.
- `Hex.LLLBench.runFirstShortVectorRandomBoundedNormSq30`: median
  `5.425 ms`, observed hash `0x3a52`, expected hash matches.
- `Hex.LLLBench.runFirstShortVectorRandomBoundedNormSq60`: median
  `68.697 ms`, observed hash `0x98cc`, expected hash matches.
- `Hex.LLLBench.runFirstShortVectorRandomBoundedNormSq120`: median
  `800.045 ms`, observed hash `0x11860`, expected hash matches.
- `Hex.LLLBench.runFirstShortVectorRandomBoundedNormSq240`: median
  `11.737 s`, observed hash `0x2454a`, expected hash matches.
- `Hex.LLLBench.runFirstShortVectorHarshCubicNormSq15`: median `1.220 ms`,
  observed hash `0x700000000033a4`, expected hash matches.
- `Hex.LLLBench.runFirstShortVectorHarshCubicNormSq30`: median `24.046 ms`,
  observed hash `0x37cc`, expected hash matches.
- `Hex.LLLBench.runFirstShortVectorHarshCubicNormSq45`: median `186.514 ms`,
  observed hash `0x6d1e`, expected hash matches.

Smoke wiring was also checked with:

```sh
lake exe hexlll_bench list
lake exe hexlll_bench verify
```

At current worktree commit `924910079376c876da2e2fe9d94915505dd477e4`,
the smoke verifier succeeds for all 52 registered HexLLL benchmarks, including
the densified Isabelle ladder added after the scientific run below.

Current scientific rerun for the five formerly inconclusive parametric
registrations at commit `924910079376c876da2e2fe9d94915505dd477e4` on
`carica` (Apple M2 Ultra, macOS), command:

```sh
lake exe hexlll_bench run Hex.LLLBench.runSizeReduceChecksum Hex.LLLBench.runGramSchmidtCoeffChecksum Hex.LLLBench.runFirstShortVectorHarshCubicChecksum Hex.LLLBench.runOfBasisHarshCubicChecksum Hex.LLLBench.runFirstShortVectorRandomBoundedChecksum --export-file reports/bench-results/hex-lll-924910079376c-clean.json
```

The harness recorded `9249100-dirty` because this worktree carried a
pre-existing local `.claude/CLAUDE.md` modification outside this evidence
package. Export artefact:
`reports/bench-results/hex-lll-924910079376c-clean.json`, SHA-256
`9e57bc8c2653e8ce7c8311b7592197068338c7dcdf8e235a6f0f3e1189768e7d`.

- `Hex.LLLBench.runSizeReduceChecksum`: consistent with declared complexity
  (parameters `128..160`, final per-call `220.548 us`).
- `Hex.LLLBench.runGramSchmidtCoeffChecksum`: consistent with declared
  complexity (parameters `32..128`, final per-call `7.363 us`).
- `Hex.LLLBench.runFirstShortVectorHarshCubicChecksum`: consistent with
  declared complexity (parameters `15..55`, final per-call `662.056 ms`).
- `Hex.LLLBench.runOfBasisHarshCubicChecksum`: consistent with declared
  complexity (parameters `12..36`, final per-call `86.523 ms`).
- `Hex.LLLBench.runFirstShortVectorRandomBoundedChecksum`: consistent with
  declared complexity (parameters `30..180`, final per-call `6.178 s`).

The earlier `reports/bench-results/hex-lll-e211854d1435.json` inconclusive
verdicts were measurement/model-registration findings. The current run resolves
the parametric-verdict blocker, but the densified Lean/Isabelle comparator
Concern below still prevents a Phase 4 promotion.

Current-head rerun for the same five formerly inconclusive parametric
registrations at commit `14537a67ebf1bd51b2275c8840562bb33ce813c1` on
`carica` (Apple M2 Ultra, macOS), command:

```sh
lake exe hexlll_bench run Hex.LLLBench.runSizeReduceChecksum Hex.LLLBench.runGramSchmidtCoeffChecksum Hex.LLLBench.runFirstShortVectorHarshCubicChecksum Hex.LLLBench.runOfBasisHarshCubicChecksum Hex.LLLBench.runFirstShortVectorRandomBoundedChecksum --export-file reports/bench-results/hex-lll-14537a67ebf1-parametric-rerun.json
```

The harness recorded `14537a6-dirty` because this worktree carried a
pre-existing local `.claude/CLAUDE.md` modification outside this evidence
package. Export artefact:
`reports/bench-results/hex-lll-14537a67ebf1-parametric-rerun.json`, SHA-256
`694775b6112456dab8e9f099e05a18997fdfd9e01a439e707ebf819c712472bc`.

- `Hex.LLLBench.runSizeReduceChecksum`: consistent with declared complexity
  (parameters `128..160`, final per-call `220.814 us`).
- `Hex.LLLBench.runGramSchmidtCoeffChecksum`: consistent with declared
  complexity (parameters `32..128`, final per-call `7.256 us`).
- `Hex.LLLBench.runFirstShortVectorHarshCubicChecksum`: consistent with
  declared complexity (parameters `15..55`, final per-call `663.375 ms`).
- `Hex.LLLBench.runOfBasisHarshCubicChecksum`: consistent with declared
  complexity (parameters `12..36`, final per-call `86.898 ms`).
- `Hex.LLLBench.runFirstShortVectorRandomBoundedChecksum`: consistent with
  declared complexity (parameters `30..180`, final per-call `6.073 s`).

Row-mutating `scaledCoeffRows` fixed harsh-cubic comparator check at commit
`af2d0a7dd05342c4a0f965cad83c54e86bb8afa5` on `carica` (Apple M2 Ultra,
macOS), command:

```sh
lake exe hexlll_bench run Hex.LLLBench.runFirstShortVectorHarshCubicNormSq45 Hex.LLLBench.runFirstShortVectorHarshCubicNormSq50 Hex.LLLBench.runFirstShortVectorHarshCubicNormSq55 Hex.LLLBench.runIsabelleHarshCubicNormSq45 Hex.LLLBench.runIsabelleHarshCubicNormSq50 Hex.LLLBench.runIsabelleHarshCubicNormSq55 --export-file reports/bench-results/hex-lll-c4d43eee-step-scaled-rows-harsh-cubic.json
```

The harness recorded `af2d0a7-dirty` because this worktree carried local
changes while measuring this patch. Export artefact:
`reports/bench-results/hex-lll-c4d43eee-step-scaled-rows-harsh-cubic.json`,
SHA-256 `55e347a67a2e16a86e522eb35a744ecafcaf0e9efe87908bc5229b0c1bacfae8`.

- `Hex.LLLBench.runFirstShortVectorHarshCubicNormSq45`: median
  `201.127 ms`, observed hash `0x6a96`, expected hash matches.
- `Hex.LLLBench.runFirstShortVectorHarshCubicNormSq50`: median
  `366.172 ms`, observed hash `0x72c6`, expected hash matches.
- `Hex.LLLBench.runFirstShortVectorHarshCubicNormSq55`: median
  `664.246 ms`, observed hash `0x7776`, expected hash matches.
- `Hex.LLLBench.runIsabelleHarshCubicNormSq45`: median `170.060 ms`,
  observed hash `0x6a96`, expected hash matches.
- `Hex.LLLBench.runIsabelleHarshCubicNormSq50`: median `285.118 ms`,
  observed hash `0x72c6`, expected hash matches.
- `Hex.LLLBench.runIsabelleHarshCubicNormSq55`: median `419.417 ms`,
  observed hash `0x7776`, expected hash matches.

The current fixed comparator registrations use the post-HO-18 densified
headline ladders:

- `random-bounded`: `n = 30, 45, 60, 75, 90, 120, 150, 180`.
- `harsh-cubic`: `n = 15, 20, 25, 30, 35, 40, 45, 50, 55, 60, 65`.
- `bz-recombination`: one tiny fixed row, retained only as contextual
  comparator evidence because process overhead dominates this family.

The committed densified Lean/Isabelle comparator sweep below covers the full
`random-bounded` and `harsh-cubic` ladders. Both native comparator
largest-rung verdicts are now met.

Informational `fpLLL via fpylll` random-bounded ladder run at worktree
commit `594364a5d86cc9daaf26c53a8b6a137998b38a6e` on `carica`
(Apple M2 Ultra, macOS), command:

```sh
PATH="$PWD/.venv-oracles/bin:$PATH" lake exe hexlll_bench run \
  Hex.LLLBench.runFpylllFirstShortVectorRandomBounded30Checksum \
  Hex.LLLBench.runFpylllFirstShortVectorRandomBounded45Checksum \
  Hex.LLLBench.runFpylllFirstShortVectorRandomBounded60Checksum \
  Hex.LLLBench.runFpylllFirstShortVectorRandomBounded75Checksum \
  Hex.LLLBench.runFpylllFirstShortVectorRandomBounded90Checksum \
  Hex.LLLBench.runFpylllFirstShortVectorRandomBounded120Checksum \
  Hex.LLLBench.runFpylllFirstShortVectorRandomBounded150Checksum \
  Hex.LLLBench.runFpylllFirstShortVectorRandomBounded180Checksum \
  --export-file reports/bench-results/hex-lll-fpylll-0c2d9a9e2d0a.json
```

The run used `fpylll 0.6.4`, `python-flint 0.8.0`, and deterministic benchmark
inputs from `HexLLL/Bench.lean`; no random seeds are involved. The harness
recorded `594364a-dirty` because this worktree carried the benchmark
registration/report edits plus a pre-existing local `.claude/CLAUDE.md`
modification outside this evidence package. Export artefact:
`reports/bench-results/hex-lll-fpylll-0c2d9a9e2d0a.json`, SHA-256
`21fcd94e1dbf8e745ace1f14fbc31cb93be139c2c4119350f51e8ace332affd3`.

- `Hex.LLLBench.runFpylllFirstShortVectorRandomBounded30Checksum`: median
  `1.837 ms`, min `1.803 ms`, max `1.888 ms`, observed checksum `0x4`.
- `Hex.LLLBench.runFpylllFirstShortVectorRandomBounded45Checksum`: median
  `4.784 ms`, min `4.611 ms`, max `4.869 ms`, observed checksum `0x4`.
- `Hex.LLLBench.runFpylllFirstShortVectorRandomBounded60Checksum`: median
  `9.756 ms`, min `9.586 ms`, max `10.359 ms`, observed checksum `0x4`.
- `Hex.LLLBench.runFpylllFirstShortVectorRandomBounded75Checksum`: median
  `19.446 ms`, min `19.324 ms`, max `19.942 ms`, observed checksum `0x4`.
- `Hex.LLLBench.runFpylllFirstShortVectorRandomBounded90Checksum`: median
  `32.003 ms`, min `31.852 ms`, max `32.490 ms`, observed checksum `0x4`.
- `Hex.LLLBench.runFpylllFirstShortVectorRandomBounded120Checksum`: median
  `76.952 ms`, min `75.794 ms`, max `79.394 ms`, observed checksum `0x4`.
- `Hex.LLLBench.runFpylllFirstShortVectorRandomBounded150Checksum`: median
  `153.998 ms`, min `152.679 ms`, max `157.519 ms`, observed checksum `0x4`.
- `Hex.LLLBench.runFpylllFirstShortVectorRandomBounded180Checksum`: median
  `271.702 ms`, min `269.054 ms`, max `1.008 s`, observed checksum `0x4`.

All eight fixed fpLLL random-bounded registrations had repeat-stable
checksums; the `n = 30` registration also matched its configured expected
checksum.

## Comparator Ratios

The current implemented gating comparator is `verified Isabelle LLL (AFP LLL_Basis_Reduction; Haskell extraction from Zenodo 2636367)`, declared in `SPEC/Libraries/hex-lll.md`. The persistent-subprocess harness for it was wired in HO-16 (#3676); the matching fpylll persistent driver was wired in HO-17 (#4186). The densified `random-bounded` and `harsh-cubic` ladders are the post-HO-18 fixed-benchmark schedules — `random-bounded` `n ∈ {30, 45, 60, 75, 90, 120, 150, 180}`, `harsh-cubic` `n ∈ {15, 20, 25, 30, 35, 40, 45, 50, 55}` — per the post-#3657 §"Headline reports" densification rule.

The certified external-dispatch SPEC also declares the gating comparator
`verified Isabelle certified-LLL (JAR 2020 §7; svp_certified from the Zenodo 2636367 LLL_Basis_Reduction extraction, same archive as the native comparator)`.
The Hex certified path is now registered as fixed process-call targets:
`runCertifiedFirstShortVectorRandomBounded{30,45,60,75,90,120,150,180}Checksum`
and
`runCertifiedFirstShortVectorHarshCubic{15,20,25,30,35,40,45,50,55,60,65}Checksum`.
Each target sends a `CERT\t` request to the persistent fpylll driver, receives a
flat `(B', U, V)` payload, and runs `LLLProvider.certifyFlat`, so the measured
path is fpLLL candidate production plus the Lean checker. Paired
`runCertifiedChecker*` targets cache the same candidate and re-run only
`certCheck` after warmup, giving the checker's share of certified-path cost.

Random-bounded certified ladder export:
`reports/bench-results/hex-lll-certified-c3d2fecb.json`,
SHA-256 `c4439a4e06c1f61ee76717ebcc8f170cb643ea095d6765230b84a55204c44e29`.
The harsh-cubic certified ladder runs two rungs further (to `n = 65`) and is
measured in its own carica sweep:
`reports/bench-results/hex-lll-certified-harsh-extended-1e6679ff.json`,
SHA-256 `ccaec1be0a5209f63387a8b2af0f093274f06d6518323f631093ad82288ee6cb`;
its `15..55` result hashes match the c3d2fecb export exactly.
Both runs used `HEX_FPLLL_FFI_LIB="$(scripts/oracle/setup_fplll_ffi.sh)"` so
the certified-path cost is fpLLL candidate production through `fplll-ffi`
plus Lean's checker. All certified-path and checker-only rows had
repeat-stable hashes. Candidate rejection rate was `0 %` across both runs
(`0 / 34` random-bounded+harsh-cubic-to-55, `0 / 22` harsh-cubic `15..65`):
every full certified target and every checker-only cached payload accepted.

Lean-certified-vs-Lean-native random-bounded ratios:

| `n` | Lean native median | Lean certified median | certified/native | checker share |
|---:|---:|---:|---:|---:|
| 30 | 15.14 ms | 4.23 ms | 0.2794 | 64.4 % |
| 45 | 55.53 ms | 14.11 ms | 0.2541 | 60.5 % |
| 60 | 142.01 ms | 32.66 ms | 0.2300 | 63.1 % |
| 75 | 296.58 ms | 65.59 ms | 0.2212 | 60.3 % |
| 90 | 495.68 ms | 112.71 ms | 0.2274 | 61.3 % |
| 120 | 1.39 s | 274.10 ms | 0.1972 | 63.0 % |
| 150 | 2.65 s | 565.88 ms | 0.2135 | 63.5 % |
| 180 | 4.76 s | 954.40 ms | 0.2005 | 64.4 % |

Random-bounded trend: Lean certified sits at about `0.20..0.28×` Lean
native. The checker is the dominant certified-path component, accounting for
`60..64 %` of the measured full path. The input-size predictor routes the
random-bounded checker rungs `n ≤ 120` to the exact integer checker
(the operand bit growth on this family stays below the 128-bit interval
working precision); rungs `n ≥ 150` dispatch to the fixed-precision
enclosure pass, which is where the small absolute speedup at the top of
the ladder comes from.

Lean-certified-vs-Lean-native harsh-cubic ratios:

| `n` | Lean native median | Lean certified median | certified/native | checker share |
|---:|---:|---:|---:|---:|
| 15 | 515 µs | 832 µs | 1.6148 | 89.1 % |
| 20 | 1.67 ms | 2.29 ms | 1.3698 | 92.0 % |
| 25 | 4.15 ms | 5.19 ms | 1.2517 | 99.0 % |
| 30 | 9.53 ms | 8.14 ms | 0.8538 | 85.5 % |
| 35 | 19.65 ms | 11.13 ms | 0.5666 | 89.0 % |
| 40 | 39.44 ms | 14.77 ms | 0.3745 | 91.2 % |
| 45 | 75.83 ms | 19.95 ms | 0.2631 | 95.0 % |
| 50 | 135.80 ms | 27.55 ms | 0.2029 | 87.4 % |
| 55 | 234.28 ms | 35.53 ms | 0.1516 | 88.1 % |
| 60 | 381.56 ms | 45.38 ms | 0.1189 | 91.2 % |
| 65 | 621.32 ms | 56.10 ms | 0.0903 | 98.1 % |

Harsh-cubic trend: Lean certified crosses below Lean native at `n = 30` and
drops to **`0.090×` Lean native at `n = 65`** — an 11.1× speedup over the
native body (`0.15×`, 6.6× at `n = 55`; the certified curve is still widening
its lead at the top of the ladder). Checker-only cost accounts for the large
majority of the full certified path (`≈85..99 %`); the candidate-production
remainder is small on this family, and its measured share is within run noise
at the small rungs where it is sub-millisecond.
The dispatched checker routes harsh-cubic above `n ≈ 25` to the
fixed-precision enclosure pass (which costs `O(n³)` on fixed-width
mantissas, independent of the `~2^(3.3n)` Gram-determinant bit growth
on this family); at `n ∈ {15, 20, 25}` the predictor still picks the exact
`d`/`ν` checker, where the small absolute cost difference is the
checker-share figure. The harsh-cubic entries are `2^(3.3n)` wide, so the
same-lattice clause runs the packed product-equality certificate on wide
entries, where the packed dot products cost the same bit operations as a
materialized comparison.

The external `verified Isabelle certified-LLL` executable is now wired from the
same Zenodo 2636367 archive as the native comparator:
`scripts/oracle/setup_lll_isabelle.sh certified` builds
`experiments/svp_certified`, and `HexLLL/Bench.lean` exposes persistent
`runIsabelleCertified*NormSq` fixed targets for the random-bounded and
harsh-cubic ladders.

The random-bounded certified-vs-Isabelle-certified ladder, and the
harsh-cubic ladder through `n = 55`, were measured in one run on
`carica` (Apple M2 Ultra, macOS) at commit `c3d2fecb`, with both engines
hosted in the same process schedule so those gating ratios share a host and
candidate set. The harsh-cubic Hex-certified column above `n = 55` (and, for
the consolidated `15..65` curve plotted in the figure, the whole harsh-cubic
Hex-certified series) comes from the later same-host dedicated sweep
`hex-lll-certified-harsh-extended-1e6679ff.json`, whose `15..55` result
hashes match this run exactly; the harsh-cubic Isabelle-certified column is
this run, which already ran to `n = 65`:

```sh
HEX_LLL_ISABELLE_CERTIFIED_SVP="$(scripts/oracle/setup_lll_isabelle.sh certified)" \
HEX_FPLLL_FFI_LIB="$(scripts/oracle/setup_fplll_ffi.sh)" \
lake exe hexlll_bench run \
  Hex.LLLBench.runCertifiedFirstShortVectorRandomBounded{30,45,60,75,90,120,150,180}Checksum \
  Hex.LLLBench.runIsabelleCertifiedRandomBoundedNormSq{30,45,60,75,90,120,150,180} \
  Hex.LLLBench.runCertifiedFirstShortVectorHarshCubic{15,20,25,30,35,40,45,50,55}Checksum \
  Hex.LLLBench.runIsabelleCertifiedHarshCubicNormSq{15,20,25,30,35,40,45,50,55,60,65} \
  --export-file reports/bench-results/hex-lll-certified-carica.json
```

This export sources the random-bounded Lean-certified and both Isabelle-certified
curves on the comparator plots. The harsh-cubic Lean-certified curve instead
sources the dedicated `15..65` harsh-cubic sweep
(`hex-lll-certified-harsh-extended-1e6679ff.json`), which extends that one series
two rungs past this run; its `15..55` result hashes match this export exactly.

Certified-vs-Isabelle-certified random-bounded ratios:

| `n` | Hex certified median | Isabelle certified median | Hex/Isabelle-certified | speedup |
|---:|---:|---:|---:|---:|
| 30 | 4.23 ms | 31.54 ms | 0.134 | 7.46× |
| 45 | 14.11 ms | 57.66 ms | 0.245 | 4.09× |
| 60 | 32.66 ms | 105.86 ms | 0.309 | 3.24× |
| 75 | 65.59 ms | 187.17 ms | 0.350 | 2.85× |
| 90 | 112.71 ms | 307.73 ms | 0.366 | 2.73× |
| 120 | 274.10 ms | 697.89 ms | 0.393 | 2.55× |
| 150 | 565.88 ms | 1.34 s | 0.424 | 2.36× |
| 180 | 954.40 ms | 2.36 s | 0.404 | 2.48× |

Certified-vs-Isabelle-certified harsh-cubic ratios:

| `n` | Hex certified median | Isabelle certified median | Hex/Isabelle-certified | speedup |
|---:|---:|---:|---:|---:|
| 15 | 832 µs | 20.15 ms | 0.041 | 24.23× |
| 20 | 2.29 ms | 24.03 ms | 0.095 | 10.51× |
| 25 | 5.19 ms | 28.01 ms | 0.185 | 5.39× |
| 30 | 8.14 ms | 38.24 ms | 0.213 | 4.70× |
| 35 | 11.13 ms | 56.29 ms | 0.198 | 5.06× |
| 40 | 14.77 ms | 90.02 ms | 0.164 | 6.10× |
| 45 | 19.95 ms | 149.14 ms | 0.134 | 7.48× |
| 50 | 27.55 ms | 243.26 ms | 0.113 | 8.83× |
| 55 | 35.53 ms | 398.40 ms | 0.089 | 11.21× |
| 60 | 45.38 ms | 628.55 ms | 0.072 | 13.85× |
| 65 | 56.10 ms | 1.01 s | 0.055 | 18.08× |

The Hex-certified column is the harsh-cubic `15..65` sweep
(`hex-lll-certified-harsh-extended-1e6679ff.json`); the Isabelle-certified
column is the carica export, which already ran to `n = 65`. Both certified
ladders now share the full rung schedule.

Gating verdict: **met at every shared rung.** Hex's certified path is faster
than Isabelle's certified path across both families — by `2.36..7.46×` on
random-bounded and `4.70..24.23×` on harsh-cubic, the harsh-cubic margin
widest and still growing at the top rung (`18.08×` at `n = 65`). On
random-bounded the margin is widest at small `n` (where Isabelle's per-request
`fplll` subprocess fork dominates), narrows through the middle of the ladder,
then plateaus at `~2.4×` on the top rungs. On harsh-cubic the margin widens
above `n = 35` because the Hex enclosure checker scales `~n^2.8` while
Isabelle's exact checker rides the `~n^4.6` slope of its exact integer
Gram-Schmidt.

Architectural asymmetries for this ratio:

- Hex's certified path calls `fplll-ffi` in process and then runs the Lean
  integer certificate checker.
- Isabelle's certified path shells out to the `fplll` binary per request, even
  though the surrounding Haskell driver is persistent.
- Hex checks reducedness with `lllReducedInt`; Isabelle confirms reducedness by
  re-running the verified LLL reducer inside `test_certified`.

The random-bounded plot shows six labelled series across the full committed
ladder: Lean native, Lean steered, Isabelle native, Lean certified, Isabelle
certified (adjusted), and fpLLL via fplll-ffi. **Lean native** is the exact
`d`/`ν` reducer (`lllNative`); **Lean steered** is the default native path, the
approximation-steered reducer that drives exact integer row operations from an
untrusted floating-point Gram–Schmidt and certifies its own output at
`(δ, 11/20)`. The steered curve sits below exact native across the whole ladder
(2.5× faster at `n = 180`) and above the certified path, which only checks an
fpLLL candidate rather than reducing the basis itself. A single `n ≥ 30`
dispatch routes every rung from `n = 30` up to the steered path, so the steered
curve is smooth to the bottom rung (`n = 30` at 4.4 ms, where the exact reducer
would cost ~14 ms); below that floor the exact reducer runs directly. The fpLLL series is the
in-process `fplll-ffi` shim called at the dispatch's requested reduction
parameters with transform production — the exact reducer call the production
dispatch makes.

![Random-bounded comparator runtime plot](figures/hex-lll-comparator-random-bounded.svg)

The plotted Isabelle-certified curve is adjusted down by its **measured**
per-request `svp_certified` floor — the fixed fork + startup cost of one
request, which Hex's in-process `fplll-ffi` path avoids. The floor is the
committed `runIsabelleCertifiedProcessFloorNormSq` benchmark (a trivial 2×2
request, so its median is the floor with negligible `n`-dependent work),
measured in the **same run** as the harsh-cubic ladder (~19.9 ms on `carica`)
so it is a true lower bound under every rung and every point survives the
subtraction — including harsh-cubic `n = 15`, whose certified work is only
~2.4 ms above the floor. The plot reads that measured value rather than a
hardcoded constant; the ratio tables above and the scaling fits keep the raw
medians.

The harsh-cubic plot shows the same six series, and this is the family where the
steered curve matters most. The exact `d`/`ν` reducers ride the `~n^5.6` slope
of their Θ(n⁴)-bit Gram-determinant state, while **Lean steered leaves that
complexity class** (`p ≈ 2.73`, 6.0× ahead of exact native at `n = 55`) and
lands within `~1.1×` of the Lean-certified curve. Both certified curves and the
steered curve carry the crossover story on this family, so all are plotted —
the earlier figure omitted the certified curves on harsh-cubic; they are now
shown alongside the steered native path they are closest to. The Lean-certified
curve now runs the full `15..65` schedule (from
`hex-lll-certified-harsh-extended-1e6679ff.json`), matching the native and
Isabelle-certified curves rung for rung; it widens its lead over exact native
across the new top rungs (`0.090×` at `n = 65`).

![Harsh-cubic comparator runtime plot](figures/hex-lll-comparator-harsh-cubic.svg)

Here too the Isabelle-certified curve is adjusted down by its measured
per-request `svp_certified` floor (the committed
`runIsabelleCertifiedProcessFloorNormSq` benchmark, ~19.9 ms; see
[§Per-call comparator overhead](#per-call-comparator-overhead)); as on the
random-bounded figure, the ratio tables and scaling fits keep the raw
medians.

For the asymptotic scaling of these curves — fitted exponents and constant
factors per method, with reproduction steps — see
[hex-lll-scaling.md](hex-lll-scaling.md). In brief: on random-bounded the
exact-native, steered, certified, and fpLLL methods are all near-`n³` and differ
by constant factors (Lean steered 2.5× faster than exact native, Lean certified
faster still); on harsh-cubic the exact native reducers (`~n^5.6`) fan out from
the steered default (`~n^2.73`), the certified path (`~n^2.79`), and fpLLL
(`~n^2.8` for the in-process shim at the production-requested parameters) —
the steered reducer is the one that moved the native curve out of the
`~n^5.6` class.

### Per-call comparator overhead

Both gating and informational comparators are wired through the persistent-subprocess protocol described at the top of `HexLLL/Bench.lean`. The per-call protocol overhead, measured on the audit host, is:

- `Isabelle` (gating): **~9 µs** per steady-state request after the one-time GHC startup.
- `Isabelle certified-LLL`: **~19.9 ms** per trivial end-to-end request through
  persistent `svp_certified`; this includes the per-request `fplll` subprocess
  and certificate/reducedness checks. This is now a committed, registered
  measurement — `runIsabelleCertifiedProcessFloorNormSq` (a trivial 2×2
  request), taken in the same run as the harsh-cubic Isabelle-certified ladder
  — so the comparator plot subtracts a reproducible floor that is a true lower
  bound under every rung, rather than a hardcoded constant; the earlier
  audit-host figure was ~18.8 ms.
- `fpLLL via fpylll` (informational): **~34 µs** per steady-state request after the one-time CPython + `import fpylll` startup.

Both figures are below the 5 % overhead-to-measured-time floor that
`SPEC/benchmarking.md` requires for honest ratios on the regenerated fixed
comparator rungs. The process-call registrations set `minTotalSeconds := 1.0`,
so each fixed child runs enough inner iterations to amortize its one-time
GHC / CPython startup before reporting `total_nanos / inner_repeats`.

### Densified Lean + Isabelle sweep

Combined Lean + Isabelle sweep at commit `6fcd1185cee03cec228194857b3bab0816060158` on `carica` (Apple M2 Ultra, macOS), recorded from `2026-06-01T12:15:13Z` through `2026-06-01T12:51:25Z`. The harness recorded `6fcd118-dirty` because this worktree carried a pre-existing local `.claude/CLAUDE.md` modification outside this evidence package.

Sweep command:

```sh
lake exe hexlll_bench run \
  Hex.LLLBench.runFirstShortVectorRandomBoundedNormSq30 \
  Hex.LLLBench.runIsabelleRandomBoundedNormSq30 \
  Hex.LLLBench.runFirstShortVectorRandomBoundedNormSq45 \
  Hex.LLLBench.runIsabelleRandomBoundedNormSq45 \
  Hex.LLLBench.runFirstShortVectorRandomBoundedNormSq60 \
  Hex.LLLBench.runIsabelleRandomBoundedNormSq60 \
  Hex.LLLBench.runFirstShortVectorRandomBoundedNormSq75 \
  Hex.LLLBench.runIsabelleRandomBoundedNormSq75 \
  Hex.LLLBench.runFirstShortVectorRandomBoundedNormSq90 \
  Hex.LLLBench.runIsabelleRandomBoundedNormSq90 \
  Hex.LLLBench.runFirstShortVectorRandomBoundedNormSq120 \
  Hex.LLLBench.runIsabelleRandomBoundedNormSq120 \
  Hex.LLLBench.runFirstShortVectorRandomBoundedNormSq150 \
  Hex.LLLBench.runIsabelleRandomBoundedNormSq150 \
  Hex.LLLBench.runFirstShortVectorRandomBoundedNormSq180 \
  Hex.LLLBench.runIsabelleRandomBoundedNormSq180 \
  Hex.LLLBench.runFirstShortVectorHarshCubicNormSq15 \
  Hex.LLLBench.runIsabelleHarshCubicNormSq15 \
  Hex.LLLBench.runFirstShortVectorHarshCubicNormSq20 \
  Hex.LLLBench.runIsabelleHarshCubicNormSq20 \
  Hex.LLLBench.runFirstShortVectorHarshCubicNormSq25 \
  Hex.LLLBench.runIsabelleHarshCubicNormSq25 \
  Hex.LLLBench.runFirstShortVectorHarshCubicNormSq30 \
  Hex.LLLBench.runIsabelleHarshCubicNormSq30 \
  Hex.LLLBench.runFirstShortVectorHarshCubicNormSq35 \
  Hex.LLLBench.runIsabelleHarshCubicNormSq35 \
  Hex.LLLBench.runFirstShortVectorHarshCubicNormSq40 \
  Hex.LLLBench.runIsabelleHarshCubicNormSq40 \
  Hex.LLLBench.runFirstShortVectorHarshCubicNormSq45 \
  Hex.LLLBench.runIsabelleHarshCubicNormSq45 \
  Hex.LLLBench.runFirstShortVectorHarshCubicNormSq50 \
  Hex.LLLBench.runIsabelleHarshCubicNormSq50 \
  Hex.LLLBench.runFirstShortVectorHarshCubicNormSq55 \
  Hex.LLLBench.runIsabelleHarshCubicNormSq55 \
  Hex.LLLBench.runFirstShortVectorBZRecombinationNormSq \
  Hex.LLLBench.runIsabelleBZRecombinationNormSq \
  --export-file reports/bench-results/hex-lll-densified-6fcd1185cee0.json
```

Export artefact: `reports/bench-results/hex-lll-densified-6fcd1185cee0.json`, SHA-256 `8917e96a952d7d2e40bdcea21d5399808dcd32fcec37114a06dd884e292effd9`.

Comparator source: `scripts/oracle/setup_lll_isabelle.sh` downloads and verifies Zenodo record `2636367`, archive SHA-256 `5c975aeb2033540b8f9a05d2ffac87dca0f258e887a5807edefbe60178a547e0`, then runs `svp_verified`.

### random-bounded ladder

All three medians come from
`reports/bench-results/hex-lll-random-bounded-schur.json`, a single
Lean+Isabelle+fpylll sweep on `carica` (Apple M2 Ultra, macOS) with
`warmupFirstIter := true`, all four post-#6330 perf fixes in
(#6338, #6339, #6348, #6350), and the per-row Schur scaled-coefficient
kernel.

| `n` | Lean median | Isabelle median | fpylll median | Lean/Isabelle | speedup vs Isabelle | status |
|---:|---:|---:|---:|---:|---:|:---|
| 30 | 15.14 ms | 16.81 ms | 1.84 ms | 0.9007 | Lean 1.11× faster | eligible |
| 45 | 55.53 ms | 64.85 ms | 4.83 ms | 0.8563 | Lean 1.17× faster | eligible |
| 60 | 142.01 ms | 176.93 ms | 9.64 ms | 0.8026 | Lean 1.25× faster | eligible |
| 75 | 296.58 ms | 383.34 ms | 19.41 ms | 0.7737 | Lean 1.29× faster | eligible |
| 90 | 495.68 ms | 691.52 ms | 31.62 ms | 0.7168 | Lean 1.40× faster | eligible |
| 120 | 1.39 s | 1.93 s | 76.61 ms | 0.7213 | Lean 1.39× faster | eligible |
| 150 | 2.65 s | 3.98 s | 151.93 ms | 0.6639 | Lean 1.51× faster | eligible |
| 180 | 4.76 s | 7.55 s | 268.23 ms | 0.6304 | Lean 1.59× faster | eligible |

**Trend.** Across the eligible range `n = 30..180`, the Lean/Isabelle ratio moves from `0.9007` to `0.6304`: Lean's lead grows with `n`.

**Gating-goal verdict (largest eligible rung `n = 180`).** Lean `4.76 s` vs Isabelle `7.55 s`; ratio `0.6304` (Lean 1.59× faster). Gating-goal verdict: **met**.

### harsh-cubic ladder

Lean and Isabelle medians come from
`reports/bench-results/hex-lll-harsh-cubic-extended-schur-lean-isabelle.json`,
a single sweep on `carica` (Apple M2 Ultra, macOS) with
`warmupFirstIter := true`, all four post-#6330 perf fixes in
(#6338, #6339, #6348, #6350), and the per-row Schur scaled-coefficient
kernel. The fpylll comparator medians in the consolidated
`reports/bench-results/hex-lll-harsh-cubic-extended-schur.json` are the
unchanged fpylll series from the post-perf export.

| `n` | Lean median | Isabelle median | fpylll median | Lean/Isabelle | speedup vs Isabelle | status |
|---:|---:|---:|---:|---:|---:|:---|
| 15 | 515 µs | 763 µs | 429 µs | 0.6743 | Lean 1.48× faster | eligible |
| 20 | 1.67 ms | 2.17 ms | 829 µs | 0.7693 | Lean 1.30× faster | eligible |
| 25 | 4.15 ms | 5.23 ms | 1.33 ms | 0.7931 | Lean 1.26× faster | eligible |
| 30 | 9.53 ms | 12.40 ms | 1.99 ms | 0.7689 | Lean 1.30× faster | eligible |
| 35 | 19.65 ms | 27.17 ms | 2.60 ms | 0.7230 | Lean 1.38× faster | eligible |
| 40 | 39.44 ms | 56.52 ms | 3.59 ms | 0.6978 | Lean 1.43× faster | eligible |
| 45 | 75.83 ms | 109.94 ms | 4.71 ms | 0.6897 | Lean 1.45× faster | eligible |
| 50 | 135.80 ms | 199.09 ms | 5.75 ms | 0.6821 | Lean 1.47× faster | eligible |
| 55 | 234.28 ms | 356.01 ms | 7.36 ms | 0.6581 | Lean 1.52× faster | eligible |
| 60 | 381.56 ms | 597.68 ms | 9.21 ms | 0.6384 | Lean 1.57× faster | eligible |
| 65 | 621.32 ms | 950.08 ms | 10.78 ms | 0.6540 | Lean 1.53× faster | eligible |

**Trend.** Across the eligible range `n = 15..65`, the Lean/Isabelle ratio stays below `1.0` and moves from `0.6743` to `0.6540`; Lean is faster than Isabelle on every harsh-cubic rung.

**Gating-goal verdict (largest eligible rung `n = 65`).** Lean `621.32 ms` vs Isabelle `950.08 ms`; ratio `0.6540` (Lean 1.53× faster). Gating-goal verdict: **met**.

The four post-#6330 perf fixes (`swapStep` #6338, `stepScaledRows`
#6339, `exactDiv` #6348, `setEntry` #6350) closed most of the
previously-reported gap, and the Schur recurrence closes the remaining
structural gap: the Lean/Isabelle ratio at `n = 65` moved from `1.90×`
(post-warmupFirstIter, pre-perf-fix) to `1.14×` after the four point
fixes, and now to `0.6540`.

### bz-recombination (context only)

- Lean `runFirstShortVectorBZRecombinationNormSq` median: `3.438 us`; Isabelle `runIsabelleBZRecombinationNormSq` median: `57.702 ms`; raw ratio `5.96e-05`; adjusted ratio `5.96e-05` (Lean 16781.08× faster).

Per the HO-18 issue body, the BZ family is reported for context only: its tiny matrix means per-call wall time on either side is dominated by process and input-marshalling overhead in the Isabelle executable, so the gating-goal verdict relies on `random-bounded` and `harsh-cubic`, not on this rung.

### fpLLL via fplll-ffi (informational)

`SPEC/Libraries/hex-lll.md` classifies the fpLLL comparator as informational
and renames it to `fpLLL via fplll-ffi`: the SPEC now requires fpLLL to be
measured through the in-process `fplll-ffi` FFI shim into `libfplll` (the
same reducer the certified external-dispatch path resolves at runtime), not
through a Python `fpylll` subprocess whose interpreter and IPC overhead the
runtime path never pays. The data in this section was collected before that
rename, via the legacy `fpylll` persistent-subprocess wiring (`Hex.LLLBench.runFpylll*`
targets); it is retained as transitional context and will be replaced by an
`fplll-ffi` sweep when the shim is wired into `hexlll_bench`.

The most recent informational fpLLL sweep is from worktree commit
`594364a5d86cc9daaf26c53a8b6a137998b38a6e` on `carica` (Apple M2 Ultra,
macOS), command:

```sh
PATH="$PWD/.venv-oracles/bin:$PATH" lake exe hexlll_bench run \
  Hex.LLLBench.runFpylllFirstShortVectorRandomBounded30Checksum \
  Hex.LLLBench.runFpylllFirstShortVectorRandomBounded45Checksum \
  Hex.LLLBench.runFpylllFirstShortVectorRandomBounded60Checksum \
  Hex.LLLBench.runFpylllFirstShortVectorRandomBounded75Checksum \
  Hex.LLLBench.runFpylllFirstShortVectorRandomBounded90Checksum \
  Hex.LLLBench.runFpylllFirstShortVectorRandomBounded120Checksum \
  Hex.LLLBench.runFpylllFirstShortVectorRandomBounded150Checksum \
  Hex.LLLBench.runFpylllFirstShortVectorRandomBounded180Checksum \
  --export-file reports/bench-results/hex-lll-fpylll-0c2d9a9e2d0a.json
```

Export artefact: `reports/bench-results/hex-lll-fpylll-0c2d9a9e2d0a.json`,
SHA-256 `21fcd94e1dbf8e745ace1f14fbc31cb93be139c2c4119350f51e8ace332affd3`.

- `random-bounded` `n = 30`: Lean median `18.403 ms`, fpLLL median `1.837 ms`, fpLLL relative median `0.100×` (raw); adjusted for ~34 µs protocol overhead, `0.098×`.
- `random-bounded` `n = 45`: Lean median `69.406 ms`, fpLLL median `4.784 ms`, fpLLL relative median `0.069×` (raw); adjusted `0.068×`.
- `random-bounded` `n = 60`: Lean median `179.295 ms`, fpLLL median `9.756 ms`, fpLLL relative median `0.054×` (raw); adjusted `0.054×`.
- `random-bounded` `n = 75`: Lean median `371.360 ms`, fpLLL median `19.446 ms`, fpLLL relative median `0.052×` (raw); adjusted `0.052×`.
- `random-bounded` `n = 90`: Lean median `650.187 ms`, fpLLL median `32.003 ms`, fpLLL relative median `0.049×` (raw); adjusted `0.049×`.
- `random-bounded` `n = 120`: Lean median `1.839 s`, fpLLL median `76.952 ms`, fpLLL relative median `0.042×` (raw); adjusted `0.042×`.
- `random-bounded` `n = 150`: Lean median `3.778 s`, fpLLL median `153.998 ms`, fpLLL relative median `0.041×` (raw); adjusted `0.041×`.
- `random-bounded` `n = 180`: Lean median `6.939 s`, fpLLL median `271.702 ms`, fpLLL relative median `0.039×` (raw); adjusted `0.039×`.

Harsh-cubic fpLLL sweep at worktree commit
`594364a5d86cc9daaf26c53a8b6a137998b38a6e` on `carica`
(Apple M2 Ultra, macOS), command:

```sh
PATH="$PWD/.venv-oracles/bin:$PATH" lake exe hexlll_bench run \
  Hex.LLLBench.runFpylllFirstShortVectorHarshCubic15Checksum \
  Hex.LLLBench.runFpylllFirstShortVectorHarshCubic20Checksum \
  Hex.LLLBench.runFpylllFirstShortVectorHarshCubic25Checksum \
  Hex.LLLBench.runFpylllFirstShortVectorHarshCubic30Checksum \
  Hex.LLLBench.runFpylllFirstShortVectorHarshCubic35Checksum \
  Hex.LLLBench.runFpylllFirstShortVectorHarshCubic40Checksum \
  Hex.LLLBench.runFpylllFirstShortVectorHarshCubic45Checksum \
  Hex.LLLBench.runFpylllFirstShortVectorHarshCubic50Checksum \
  Hex.LLLBench.runFpylllFirstShortVectorHarshCubic55Checksum \
  --export-file reports/bench-results/hex-lll-fpylll-harsh-cubic-4a69408a680d.json
```

The harness recorded `594364a-dirty` because this worktree carried the
benchmark registration/report edits plus a pre-existing local `.claude/CLAUDE.md`
modification outside this evidence package. Export artefact:
`reports/bench-results/hex-lll-fpylll-harsh-cubic-4a69408a680d.json`,
SHA-256 `572afe6866d80e4fd0f54519c3fbdf5bd6946cddcb919d8591e6642a1154aa0f`.

- `harsh-cubic` `n = 15`: Lean median `898.791 us`, fpLLL median `423.473 us`, fpLLL relative median `0.471×` (raw); adjusted `0.433×`.
- `harsh-cubic` `n = 20`: Lean median `3.191 ms`, fpLLL median `823.053 us`, fpLLL relative median `0.258×` (raw); adjusted `0.247×`.
- `harsh-cubic` `n = 25`: Lean median `8.331 ms`, fpLLL median `1.291 ms`, fpLLL relative median `0.155×` (raw); adjusted `0.151×`.
- `harsh-cubic` `n = 30`: Lean median `22.022 ms`, fpLLL median `1.961 ms`, fpLLL relative median `0.089×` (raw); adjusted `0.087×`.
- `harsh-cubic` `n = 35`: Lean median `49.134 ms`, fpLLL median `2.598 ms`, fpLLL relative median `0.053×` (raw); adjusted `0.052×`.
- `harsh-cubic` `n = 40`: Lean median `105.251 ms`, fpLLL median `3.530 ms`, fpLLL relative median `0.034×` (raw); adjusted `0.033×`.
- `harsh-cubic` `n = 45`: Lean median `202.061 ms`, fpLLL median `4.678 ms`, fpLLL relative median `0.023×` (raw); adjusted `0.023×`.
- `harsh-cubic` `n = 50`: Lean median `377.282 ms`, fpLLL median `5.913 ms`, fpLLL relative median `0.016×` (raw); adjusted `0.016×`.
- `harsh-cubic` `n = 55`: Lean median `640.050 ms`, fpLLL median `7.356 ms`, fpLLL relative median `0.011×` (raw); adjusted `0.011×`.

The regenerated fpLLL fixed-mode targets amortize CPython + `import fpylll`
startup inside each measured child. Across both `random-bounded` and
`harsh-cubic`, fpLLL is faster than Lean at every reported rung. Because
fpylll is informational, these trends remain context rather than a gating
performance signal for HexLLL.

## Profile

Profiles were captured with `samply record --save-only
--unstable-presymbolicate` through the `lean-bench profile` child path at the
same commit on `carica` (Apple M2 Ultra, macOS 14.6.1), sampling at samply's
default 1 kHz rate. Raw Firefox Profiler JSON and symbol sidecars are
developer-local under `/tmp/hex-profiles/` and are not committed.

### `bz-recombination`

Command:

```sh
lake exe hexlll_bench profile Hex.LLLBench.runOfBasisBzRecombinationChecksum --param 72 --profiler "samply record --save-only --unstable-presymbolicate --output /tmp/hex-profiles/hex-lll-bz-ofbasis-e211854d1435.json.gz" --target-inner-nanos 800000000
```

Representative case: rectangular BZ-style `LLLState.ofBasis`, `n = 72`, no
random seed, profile row hash `0xffbe453d356900c9`. Leaf samples in the worker
thread were approximately own compiled Hex/Lean code 56.1%, GMP arithmetic
12.4%, allocation/free 40.2%, and Lean runtime/dispatch 6.8%; categories
overlap because the executable image contains both Hex code and linked GMP.
The inclusive Hex ranking was led by `Hex.LLLBench.runOfBasisChecksum`,
`Hex.GramSchmidt.Int.data`, and its `scaledCoeffRows` loop. The audit finding
that `LLLState.ofBasis` used to run redundant Bareiss-style passes was tracked
by #2689; this snapshot is after #2689 and the inclusive path now reaches the
shared `GramSchmidt.Int.data` package once.

### `random-bounded`

Command:

```sh
lake exe hexlll_bench profile Hex.LLLBench.runFirstShortVectorRandomBoundedChecksum --param 120 --profiler "samply record --save-only --unstable-presymbolicate --output /tmp/hex-profiles/hex-lll-random-bounded-fsv-e211854d1435.json.gz" --target-inner-nanos 800000000
```

Representative case: random-bounded square basis, `n = 120`, seed `8`, profile
row hash `0x8582591a300e012b`. Leaf samples were approximately fixture/own
compiled code 43.4% in `lcgStep`/`lcgIterate`, GMP arithmetic 15.7%,
allocation/free 17.8%, and Lean runtime/refcount 1.4%. Inclusive Hex cost was
led by `Hex.lll.firstShortVector`, `Hex.LLLBench.runFirstShortVectorChecksum`,
and `Hex.GramSchmidt.Int.data`. The prominent LCG fixture-generation cost is
part of this public-entry snapshot; the repaired scientific registration now
declares the committed near-orthogonal fixture path rather than a worst-case
swap-count model.

### `harsh-cubic`

Command:

```sh
lake exe hexlll_bench profile Hex.LLLBench.runFirstShortVectorHarshCubicChecksum --param 45 --profiler "samply record --save-only --unstable-presymbolicate --output /tmp/hex-profiles/hex-lll-harsh-cubic-fsv-e211854d1435.json.gz" --target-inner-nanos 800000000
```

Representative case: harsh-cubic square basis, `n = 45`, no random seed,
profile row hash `0xdf1a1e91dca9fe8e`. Leaf samples were dominated by GMP
big-integer arithmetic, approximately 71.8% across `__gmpn_addmul_1`,
`__gmpn_submul_1`, division, copy, and multiplication helpers. Allocation/free
was about 5.0%; the remaining samples were own compiled Hex/Lean code and
runtime dispatch. Inclusive Hex cost was led by `Hex.lll.firstShortVector`,
`Hex.LLLBench.runFirstShortVectorChecksum`, and
`Hex.GramSchmidt.Int.data`/`scaledCoeffRows`. This matches the family purpose:
entry bit-length grows with `n`, so the dominant constant lands in exact
integer arithmetic.

## Concerns

- **The verified Isabelle certified-LLL series has only one committed point
  per family.** This is sufficient for the five-way plot legend and the
  bottom/shared-rung smoke verdict above, but it does not yet provide a
  full-ladder certified-vs-certified trend. The native `verified Isabelle LLL`
  gate is closed on both headline families: random-bounded `n = 180` is Lean
  `4.76 s` vs Isabelle `7.55 s`, ratio `0.6304`, and harsh-cubic `n = 65` is
  Lean `621.32 ms` vs Isabelle `950.08 ms`, ratio `0.6540`.
