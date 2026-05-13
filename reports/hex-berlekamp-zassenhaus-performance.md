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
- `Hex.BerlekampZassenhausBench.runFastPathPrecisionLocalChecksum`:
  `bzPrecisionLocalComplexity param = n^9 + n^7 * log2(height + 2)^2 + r * n^2 * log2(k + 1)`
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

Retuned non-profile run at commit `cab8cfc-dirty` on `carica`
(Apple M2 Ultra, macOS 14.6.1), command:

```sh
lake exe hexbz_bench run \
    Hex.BerlekampZassenhausBench.runFactorChecksum \
    Hex.BerlekampZassenhausBench.runFactorFastChecksum \
    Hex.BerlekampZassenhausBench.runFactorSlowDegreeHeightChecksum \
    --export-file reports/bench-results/hex-berlekamp-zassenhaus-issue3513.json
```

Export artefact:
`reports/bench-results/hex-berlekamp-zassenhaus-issue3513.json`,
SHA-256
`d9d8b79e70f6e8d4455c57b011f756e9bf271a580f76e697d4550433c240ec2f`.
The harness recorded `cab8cfc-dirty` because the run was taken from the
working tree containing this schedule/report update plus the pre-existing
pod-managed `.claude/CLAUDE.md` modification.

- `runFactorChecksum`: inconclusive (`cMin=3.155`, `cMax=542.102`,
  parameters `2..5`, final hash `0x2a6bd8144b402a41`). All four
  rows were verdict-eligible and no committed schedule row hit the
  per-call cap.
- `runFactorFastChecksum`: inconclusive (`cMin=3.269`,
  `cMax=546.583`, parameters `2..5`, final hash
  `0x9b47b80e99720e2a`). All four rows were verdict-eligible and no
  committed schedule row hit the per-call cap.
- `runFactorSlowDegreeHeightChecksum`: inconclusive (`cMin=0.816`,
  `cMax=89465.950`, encoded parameters `1002`, `2002`, and `3008`,
  final hash `0xe5ac34affd40d076`). The diagnostic now uses the
  completing degree/height subset instead of including the previous
  cap-hitting `4008` row.

Precision-local targeted run at commit `454066c-dirty` on `carica`
(Apple M2 Ultra, macOS 15.6), command:

```sh
lake exe hexbz_bench run \
    Hex.BerlekampZassenhausBench.runFastPathPrecisionLocalChecksum \
    --export-file reports/bench-results/hex-berlekamp-zassenhaus-issue3527-precision-local.json
```

Export artefact:
`reports/bench-results/hex-berlekamp-zassenhaus-issue3527-precision-local.json`,
SHA-256
`78ae610334570a5f178e3f95b6c4138670c72a4287ace61581ce65a549b4d8ba`.
The harness recorded `454066c-dirty` because this worktree carries the
pre-existing pod-managed `.claude/CLAUDE.md` modification outside this
report package.

- `runFastPathPrecisionLocalChecksum`: inconclusive (`cMin=0.028`,
  `cMax=71.644`, encoded parameters `2002004002`, `2002016002`,
  `4004016004`, `4016064004`, `6016064006`, and `8032128008`,
  final hash `0x21b9063dace28489`). All six rows completed and were
  verdict-eligible; the run is evidence for the fast-path
  precision/local-factor setup surface but not a Phase 4 completion
  verdict.

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

Profile coverage per
[SPEC/profiling.md §Coverage requirement](../SPEC/profiling.md) records
one representative case per `phase4.input_families` entry in
`libraries.yml: HexBerlekampZassenhaus`. The profiles below were
recorded with `samply record --save-only --unstable-presymbolicate
--include-args=6 --rate 1000` on `carica` (Apple M2 Ultra, macOS
14.6.1) sampling at 1 kHz, against the `_child` mode of `hexbz_bench`.
Attribution uses the `.syms.json` sidecar that samply emits alongside
the Firefox Profiler JSON, because the JSON itself keeps address
strings rather than demangled names. Raw `*.json{,.syms.json}`
artefacts are developer-local under `/tmp/hex-profiles/` and are not
committed.

The four new family entries below (public-factor-combinator,
cld-fast-path, exhaustive-slow-backstop, ho2-adversarial-recombination)
categorise leaf samples by symbol prefix at the worker-thread scope:
samples include `_child` process startup and Lean module initialisation
because samply records the whole child lifetime. The earlier
`degree-height-matrix` entry below uses a tighter categorisation
scoped to allocator and GMP leaves; the two are not directly comparable
on category percentages, but both satisfy the SPEC's
case-per-family shape-coverage requirement.

### Profile coverage table

| Family | Bench target | Parameter | Commit | Worker weight | Dominant inclusive Hex.* |
|---|---|---|---|---|---|
| public-factor-combinator | `runFactorChecksum` | `n=5` | `db43025` | 641 | `Hex.DensePoly.divMod`, `xgcd`, `mul` (≥91%) |
| cld-fast-path | `runFactorFastChecksum` | `n=5` | `db43025` | 674 | `Hex.Matrix.rref` (28.5%), `Hex.DensePoly.mul` (20.5%) |
| exhaustive-slow-backstop | `runFactorSlowChecksum` | `n=4` | `db43025` | 1231 | `Hex.DensePoly.mul`, `derivative`, `scale`, `coeff` (≥97%) |
| degree-height-matrix | `runFactorDegreeHeightChecksum` | `param=6032` | `06d996d` | 679 | `Hex.factorWithBound` (91.5%), `choosePrimeData?` (86.3%) |
| ho2-adversarial-recombination | `runFactorAdvPhi15Checksum` | `n=0` | `db43025` | 760 (init-dominated) | recombination hot path covered via public-factor-combinator (see below) |

### degree-height-matrix

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

### public-factor-combinator

Representative case at the largest verdict-eligible rung from the
retuned scientific schedule (`n = 5`). Artefact:
`/tmp/hex-profiles/hex-bz-public-db43025.{json,syms.json}`.

```sh
samply record --save-only --unstable-presymbolicate --include-args=6 \
    --rate 1000 \
    -o /tmp/hex-profiles/hex-bz-public-db43025.json -- \
    .lake/build/bin/hexbz_bench _child \
        --bench Hex.BerlekampZassenhausBench.runFactorChecksum \
        --param 5 --target-nanos 1000000000
```

`inner_repeats=32`, `per_call_nanos=17,734,514.31`, result hash
`0x2a6bd8144b402a41`. Worker thread captured 594 sample rows with total
sample weight 641.

Leaf categories:

- Hex own code: `134 / 641 = 20.9%`.
- GMP big-integer arithmetic: `0 / 641 = 0.0%` (leaves landed in the
  calling Hex polynomial routine rather than the GMP primitive itself
  on this categorisation).
- Allocation / free: `0 / 641 = 0.0%`.
- Lean compiler/runtime and bench-harness init: `142 / 641 = 22.2%`.
- Other (dyld loader, kernel calls, spawned `git status` child for the
  `LeanBench.RunEnv.detectGitCommit` probe): `365 / 641 = 56.9%`.

Top inclusive Hex.* costs:

- `Hex.DensePoly.divMod`: `100.0%`.
- `Hex.DensePoly.xgcd`: `100.0%`.
- `Hex.DensePoly.mul`: `91.3%`.
- `Hex.BerlekampZassenhausBench.initFn`: `88.1%`.
- `Hex.Matrix.IsRREF.nullspace`: `16.4%`.
- `Hex.DensePoly.trimTrailingZeros`: `15.0%`.
- `Hex.ZMod64.instDiv_hexPolyFp`: `14.2%`.
- `Hex.ZPoly.reduceModPow`: `13.9%`.
- `Hex.Berlekamp.fixedSpaceKernel`: `5.9%`.

Dominant inclusive cost is the BHKS polynomial-arithmetic chain
anchored on `Hex.DensePoly.divMod`, `xgcd`, and `mul`, with
square-free decomposition (`Hex.ZPoly.reduceModPow`) and Berlekamp's
fixed-space-kernel computation contributing smaller shares. The
ranking maps the dominant cost to the registered `runFactorChecksum`
target.

### cld-fast-path

Representative case at the same `n = 5` rung but on the CLD fast path.
Artefact: `/tmp/hex-profiles/hex-bz-cld-db43025.{json,syms.json}`.

```sh
samply record --save-only --unstable-presymbolicate --include-args=6 \
    --rate 1000 \
    -o /tmp/hex-profiles/hex-bz-cld-db43025.json -- \
    .lake/build/bin/hexbz_bench _child \
        --bench Hex.BerlekampZassenhausBench.runFactorFastChecksum \
        --param 5 --target-nanos 1000000000
```

`inner_repeats=32`, `per_call_nanos=18,396,003.91`, result hash
`0xd60670ab7167da77`. Worker thread captured 615 sample rows with total
sample weight 674.

Leaf categories:

- Hex own code: `84 / 674 = 12.5%`.
- GMP big-integer arithmetic: `0 / 674 = 0.0%`.
- Allocation / free: `4 / 674 = 0.6%`.
- Lean compiler/runtime and bench-harness init: `184 / 674 = 27.3%`.
- Other (dyld loader, kernel, spawned `git status`): `402 / 674 = 59.6%`.

Top inclusive Hex.* costs:

- `Hex.Matrix.rref`: `28.5%`.
- `Hex.DensePoly.mul`: `20.5%`.
- `Hex.Berlekamp.berlekampFactor`: `9.6%`.
- `Hex.ZMod64.add`: `4.0%`.
- `Hex.Vector.dotProduct`: `3.0%`.
- `Hex.DensePoly.divMod`: `2.4%`.
- `Hex.ZMod64.mul`: `2.2%`.
- `Hex.FpPoly.C`: `1.8%`.

Dominant inclusive cost on the CLD fast path is Berlekamp matrix
nullspace computation (`Hex.Matrix.rref` and modular arithmetic
`Hex.ZMod64.*`), rather than the dense polynomial arithmetic seen on
the public combinator. The CLD fast path's success-case dominance over
`Hex.Matrix.rref` and `Hex.Berlekamp.berlekampFactor` is consistent
with the SPEC's "BHKS bounded-recombination route" characterisation:
the polynomial-arithmetic chain still appears (`Hex.DensePoly.mul`
20.5%) but is no longer the headline cost. The profile therefore maps
the CLD fast-path dominant cost to the registered
`runFactorFastChecksum`/`runFastPathPrecisionLocalChecksum` targets.

### exhaustive-slow-backstop

Representative case at the largest tractable rung in the slow-path
schedule (`n = 4`). Beyond `n = 4` the smoke schedule caps at
4 s per call and the slow path's exponential factor crosses the
budget. Artefact:
`/tmp/hex-profiles/hex-bz-slow-db43025.{json,syms.json}`.

```sh
samply record --save-only --unstable-presymbolicate --include-args=6 \
    --rate 1000 \
    -o /tmp/hex-profiles/hex-bz-slow-db43025.json -- \
    .lake/build/bin/hexbz_bench _child \
        --bench Hex.BerlekampZassenhausBench.runFactorSlowChecksum \
        --param 4 --target-nanos 1000000000
```

`inner_repeats=256`, `per_call_nanos=4,693,865.56`, result hash
`0x329c431d3ee6b4dd`. Worker thread captured 1215 sample rows with
total sample weight 1231.

Leaf categories:

- Hex own code: `87 / 1231 = 7.1%`.
- GMP big-integer arithmetic: `0 / 1231 = 0.0%`.
- Allocation / free: `18 / 1231 = 1.5%`.
- Lean compiler/runtime and bench-harness init: `384 / 1231 = 31.2%`.
- Other (dyld loader, kernel, spawned `git status`): `742 / 1231 = 60.3%`.

Top inclusive Hex.* costs:

- `Hex.DensePoly.mul`: `100.0%`.
- `Hex.DensePoly.derivative`: `100.0%`.
- `Hex.DensePoly.scale`: `97.9%`.
- `Hex.DensePoly.coeff`: `97.7%`.
- `Hex.DensePoly.trimTrailingZeros`: `77.1%`.
- `Hex.Matrix.rowScale`: `10.5%`.
- `Hex.ZPoly.primitiveSquareFreeDecomposition`: `3.1%`.
- `Hex.DensePoly.divMod`: `2.9%`.

Dominant inclusive cost on the slow exhaustive backstop is dense
polynomial multiplication and trimming (`Hex.DensePoly.mul`,
`derivative`, `scale`, `coeff`, `trimTrailingZeros`). The exponential
recombination loop's per-iteration body is short on `n = 4` so the
profile shape is dominated by the recombination workload rather than
search-tree overhead. The ranking maps the dominant cost to the
registered `runFactorSlowChecksum`/`runFactorSlowDegreeHeightChecksum`
targets.

### ho2-adversarial-recombination

The five singleton HO-2 adversarial registrations
(`runFactorAdvX4Plus1Checksum`, `runFactorAdvQuadSqrt2Sqrt3Checksum`,
`runFactorFastAdvQuadSqrt2Sqrt3Checksum`, `runFactorAdvPhi15Checksum`,
`runAdvSwinnertonDyerSD3ModularSplitChecksum`) and the two fast-path
setup variants (`runFactorFastSetupAdvX4Plus1Checksum`,
`runFactorFastSetupAdvPhi15Checksum`) are smoke-shape coverage on the
pinned `n = 0` schedule. Their per-call cost on `carica` is under
40 ns: the auto-tuner converges to inner-repeat budgets where the
recorded sample budget is dominated by `_child` process startup and
Lean module initialisation rather than the BZ recombination hot path.
A direct profile of any HO-2 target therefore does not give
"shape-coverage" of the recombination workload in the SPEC's sense.

A representative attempt was recorded for transparency. Artefact:
`/tmp/hex-profiles/hex-bz-adv-phi15-db43025.{json,syms.json}`.

```sh
samply record --save-only --unstable-presymbolicate --include-args=6 \
    --rate 1000 \
    -o /tmp/hex-profiles/hex-bz-adv-phi15-db43025.json -- \
    .lake/build/bin/hexbz_bench _child \
        --bench Hex.BerlekampZassenhausBench.runFactorAdvPhi15Checksum \
        --param 0 --target-nanos 1000000000
```

`inner_repeats=33,554,432`, `per_call_nanos=21.78`, result hash
`0xf794f386e54863f`. The worker thread captured 745 sample rows with
total sample weight 760. Leaf categorisation: 0% Hex own,
0% GMP, 0% allocator, 72.2% Lean compiler/runtime initialisation, and
27.8% dyld + spawned `git status` child — confirming that the bench
loop is too short to displace startup samples on this shape.

The BZ recombination hot path that the HO-2 family is meant to cover
is exercised by the public-factor-combinator profile above on the
deterministic split family at `n = 5`, where `Hex.DensePoly.divMod`,
`xgcd`, and `mul` dominate the inclusive ranking. The HO-2 inputs
flow through the same `factor` (and `factorFast` for the setup
variants) entry points, so the recombination-shape attribution
transfers; the HO-2 singletons remain valuable for fixed-shape input
coverage in `list`/`verify` and for the modular split fingerprint they
record on each adversarial polynomial.

## Concerns

- Phase 4 is not complete: every scientific verdict recorded in this
  report remains inconclusive, including the precision/local-factor
  setup surface added by the issue #3527 targeted run.
- The Phase 4 dependency gate is still closed:
  `python3 scripts/status.py HexBerlekampZassenhaus` reports blockers
  `HexBerlekamp.done_through >= 4` and `HexLLL.done_through >= 4`.
- The public and fast split-family schedules now expose verdict-eligible
  rows beyond the previous `n = 1..4` smoke ladder, but they still do
  not yield a consistent BHKS scaling verdict. An exploratory run with
  the same eight-second cap reached `n = 5` and hit the cap at `n = 6`,
  so larger split inputs require either algorithmic improvement or a
  dedicated longer scheduled run.
- The singleton HO-2 adversarial registrations are valuable fixed-shape
  coverage, but their `#[0]` schedules cannot produce verdict-eligible
  scaling rows. The recombination-shape attribution for the
  `ho2-adversarial-recombination` family is recorded against the
  public-factor-combinator profile per §Profile above, since the HO-2
  inputs flow through the same `factor`/`factorFast` entry points.
- The new public/slow/fast compare surface is intentionally smoke-sized;
  it does not replace a full scientific-domain LLL-assisted versus
  exhaustive recombination comparison.
- `runFactorSlowDegreeHeightChecksum` is now explicit and reproducible on
  a completing small subset; it remains diagnostic evidence only, not a
  Phase 4 completion verdict for the full slow path.
- `libraries.yml` now records `phase4.input_families` for
  `HexBerlekampZassenhaus`, but it still has no comparator metadata;
  final Phase 4 coverage should add or explicitly justify comparator
  metadata before bumping `done_through`.
- HO-3 ([#2566](https://github.com/kim-em/hex/issues/2566)) remains open
  as a complexity-evidence concern: this report now records §Profile
  coverage for every declared
  `phase4.input_families` entry per
  [SPEC/profiling.md §Coverage requirement](../SPEC/profiling.md), but
  it does not yet establish the full Phase 4 verdicts or external
  comparator required for the BZ implementation.
