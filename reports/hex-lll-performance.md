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

At current `main` commit `1c4a58fd4051872be9dc4f1cd676573d62583852`,
the smoke verifier succeeds for all 52 registered HexLLL benchmarks,
including the densified Isabelle ladder added after the scientific run below.

The latest committed scientific artifact after the densified-ladder work is
`reports/bench-results/hex-lll-e211854d1435.json`, SHA-256
`2b12e967b4cfa017681558ea15928e7bbd14c2ec552888f17648ae8911ac83cd`,
recorded at commit `e211854d1435fbd3db4739cd6dec5be66da2f857`. It keeps five
parametric registrations below the Phase 4 exit bar:

- `Hex.LLLBench.runSizeReduceChecksum`: `inconclusive`, verdict rows
  `n = 80, 96, 128, 144`, final row `422.723 us`.
- `Hex.LLLBench.runGramSchmidtCoeffChecksum`: `inconclusive`.
- `Hex.LLLBench.runFirstShortVectorHarshCubicChecksum`: `inconclusive`,
  verdict rows `n = 15, 30, 45`, final row `177.755 ms`.
- `Hex.LLLBench.runOfBasisHarshCubicChecksum`: `inconclusive`, verdict row
  `n = 18`, `3.965 ms`.
- `Hex.LLLBench.runFirstShortVectorRandomBoundedChecksum`: `inconclusive`,
  verdict rows `n = 30, 60, 120, 240`, final row `6.028 s`.

Because `PLAN/Phase4.md` treats an inconclusive scientific verdict as a
Phase 4 blocker, this report does not promote `HexLLL.done_through`.

The current fixed comparator registrations use the post-HO-18 densified
headline ladders:

- `random-bounded`: `n = 30, 45, 60, 75, 90, 120, 150, 180`.
- `harsh-cubic`: `n = 15, 20, 25, 30, 35, 40, 45, 50, 55`.
- `bz-recombination`: one tiny fixed row, retained only as contextual
  comparator evidence because process overhead dominates this family.

No committed artifact currently contains the full densified Lean/Isabelle
comparator sweep for those ladders. Until that artifact exists, the largest
eligible-rung gating verdict required by HO-18 cannot be recomputed from this
report, and `HexLLL.done_through` remains at `3`.

Informational `fpLLL via fpylll` comparator run at commit
`ed9da7537e96cee75f395e46962d41775f615a53` on `carica` (Apple M2 Ultra,
macOS), command:

```sh
PATH="$PWD/.venv-oracles/bin:$PATH" lake exe hexlll_bench run \
  Hex.LLLBench.runFpylllFirstShortVectorBZRecombinationChecksum \
  Hex.LLLBench.runFpylllFirstShortVectorRandomBounded30Checksum \
  Hex.LLLBench.runFpylllFirstShortVectorHarshCubic15Checksum \
  --export-file reports/bench-results/hex-lll-fpylll-ed9da7537e96.json
```

The run used `fpylll 0.6.4`, `python-flint 0.8.0`, and deterministic benchmark
inputs from `HexLLL/Bench.lean`; no random seeds are involved. The harness
recorded `ed9da75-dirty` because this worktree carried a pre-existing local
`.claude/CLAUDE.md` modification outside this evidence package. Export
artefact: `reports/bench-results/hex-lll-fpylll-ed9da7537e96.json`, SHA-256
`9a2d74112dd5581db820854019a4ff9941dfd7b806678b4aae310cadf3e666e9`.

- `Hex.LLLBench.runFpylllFirstShortVectorBZRecombinationChecksum`: median
  `84.919 ms`, min `84.325 ms`, max `94.951 ms`, observed hash
  `0x3c0064007a0036`.
- `Hex.LLLBench.runFpylllFirstShortVectorRandomBounded30Checksum`: median
  `85.203 ms`, min `84.539 ms`, max `98.094 ms`, observed hash
  `0xf977db3a0120001a`.
- `Hex.LLLBench.runFpylllFirstShortVectorHarshCubic15Checksum`: median
  `85.075 ms`, min `83.981 ms`, max `94.704 ms`, observed hash
  `0x949fde47fa1fffb4`.

All three fixed fpLLL registrations matched their expected hashes.

## Comparator Ratios

The `verified Isabelle LLL (AFP LLL_Basis_Reduction; Haskell extraction from Zenodo 2636367)`
comparator was measured at the bottom shared rung for each
`phase4.input_families` entry, command:

```sh
lake exe hexlll_bench run Hex.LLLBench.runIsabelleBZRecombinationNormSq Hex.LLLBench.runIsabelleRandomBoundedNormSq30 Hex.LLLBench.runIsabelleHarshCubicNormSq15 --export-file reports/bench-results/hex-lll-isabelle-bottom-e211854d1435.json
```

Comparator source: `scripts/oracle/setup_lll_isabelle.sh` downloads and
verifies Zenodo record `2636367`, archive SHA-256
`5c975aeb2033540b8f9a05d2ffac87dca0f258e887a5807edefbe60178a547e0`, then
runs `svp_verified`. Export artefact:
`reports/bench-results/hex-lll-isabelle-bottom-e211854d1435.json`.

- `bz-recombination`: Lean `runFirstShortVectorBZRecombinationNormSq` median
  `5.625 us`; Isabelle `runIsabelleBZRecombinationNormSq` median
  `55.206 ms`; raw Lean/Isabelle ratio `0.000102` (`9814.4x` faster).
- `random-bounded`, bottom rung `n = 30`, seed `8`: Lean
  `runFirstShortVectorRandomBoundedNormSq30` median `5.462 ms`; Isabelle
  `runIsabelleRandomBoundedNormSq30` median `50.289 ms`; raw Lean/Isabelle
  ratio `0.108612` (`9.21x` faster).
- `harsh-cubic`, bottom rung `n = 15`: Lean
  `runFirstShortVectorHarshCubicNormSq15` median `1.232 ms`; Isabelle
  `runIsabelleHarshCubicNormSq15` median `49.995 ms`; raw Lean/Isabelle
  ratio `0.024642` (`40.58x` faster).

The persistent Isabelle protocol overhead measured in `HexLLL/Bench.lean` is
approximately `9 us` per steady-state request after the one-time GHC startup.
Subtracting that protocol overhead from the Isabelle medians gives adjusted
Lean/Isabelle ratios `0.000102` (`9812.8x` faster), `0.108631`
(`9.21x` faster), and `0.024646` (`40.57x` faster), respectively.

The gating goal is met in this snapshot: Lean is faster than the verified
Isabelle extraction on all three shared bottom-rung inputs. The BZ ratio is
dominated by the fixed process and input overhead in the Isabelle executable,
but even the larger random-bounded case leaves a comfortable margin.

`SPEC/Libraries/hex-lll.md` classifies the fpLLL comparator as informational.
The ratios below are fixed bottom-rung comparisons of Lean's first-short-vector
checksum target against the process-call fpLLL target, with Lean as the
baseline:

```sh
PATH="$PWD/.venv-oracles/bin:$PATH" lake exe hexlll_bench compare \
  Hex.LLLBench.runFirstShortVectorBZRecombinationChecksum \
  Hex.LLLBench.runFpylllFirstShortVectorBZRecombinationChecksum

PATH="$PWD/.venv-oracles/bin:$PATH" lake exe hexlll_bench compare \
  Hex.LLLBench.runFirstShortVectorRandomBounded30Checksum \
  Hex.LLLBench.runFpylllFirstShortVectorRandomBounded30Checksum

PATH="$PWD/.venv-oracles/bin:$PATH" lake exe hexlll_bench compare \
  Hex.LLLBench.runFirstShortVectorHarshCubic15Checksum \
  Hex.LLLBench.runFpylllFirstShortVectorHarshCubic15Checksum
```

- BZ recombination: Lean median `8.833 us`, fpLLL median `83.531 ms`, fpLLL
  relative median `9456.748x`; hashes agreed.
- Random-bounded `n = 30`: Lean median `5.752 ms`, fpLLL median `86.261 ms`,
  fpLLL relative median `14.996x`; hashes agreed.
- Harsh-cubic `n = 15`: Lean median `1.247 ms`, fpLLL median `84.130 ms`,
  fpLLL relative median `67.475x`; hashes agreed.

The persistent fpylll protocol overhead measured in `HexLLL/Bench.lean` is
approximately `34 us` per steady-state request. Subtracting that protocol
overhead from the fpLLL medians gives adjusted fpLLL relative medians
`9452.9x`, `14.991x`, and `67.448x`, respectively. The fixed target still
includes one Python plus `import fpylll` startup per measured child, as
specified by the process-call comparator registration. These figures are
therefore useful as traceable external-comparator checks for the headline
report, but they are not a gating performance signal for HexLLL.

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

- [#4334](https://github.com/kim-em/hex/issues/4334): the latest committed
  HexLLL scientific artifact records inconclusive verdicts for five
  parametric registrations. `HexLLL.done_through` remains `3` until this is
  resolved and the Concerns section can be emptied.
