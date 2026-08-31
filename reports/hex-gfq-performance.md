# HexGFq Performance Report

HexGFq's constructor and projection surfaces now follow the ordered complexity
claim policy. Five registrations use mode 1, the packed degree-one family uses
mode 2, and the packed degree-eight operation uses mode 3 after clean evidence
rules out both stronger modes. Two additional fixed registrations are only
expected-hash anchors for selected Conway moduli.

The evidence is complete, but `libraries.yml` remains at `done_through: 3`:
the Phase-4 dependency gate cannot advance HexGFq while its direct dependencies
HexConway and HexGF2 are themselves at Phase 3.

## Bench Targets

- `Hex.GfqBench.runGeneric21`: mode 1, model `n`, generic constructor and
  projection at `GFq 2 1` on deterministic binary representatives.
- `Hex.GfqBench.runPacked1`: mode 2, upper-bound model `n`, packed constructor
  and projection at `GF2q 1` on dense words of exact degree `n`.
- `Hex.GfqBench.runShared21`: mode 1, model `n`, packed and generic
  constructor/projection paths on a paired deterministic binary family.
- `Hex.GfqBench.runGeneric28`: mode 1, model `n`, generic constructor and
  projection at the deepest committed binary entry `GFq 2 8`.
- `Hex.GfqBench.runPacked8`: mode 3, fixed packed constructor and projection at
  `GF2q 8` on the canonical dense degree-63 word, with a 100 us budget.
- `Hex.GfqBench.runGeneric136`: mode 1, model `n`, explicit-entry generic
  constructor and projection at `GFq 13 6`.
- `Hex.GfqBench.runGenericC136`: mode 1, model `n`, instance-selected `GFqC`
  constructor and projection at `GFqC 13 6`.
- `Hex.GfqBench.runGenericModulusChecksum`: fixed expected-hash anchor for the
  selected generic degree-one Conway modulus; no performance claim.
- `Hex.GfqBench.runPackedModulusChecksum`: fixed expected-hash anchor for the
  selected packed degree-one Conway modulus and lower word; no performance
  claim.

For the generic targets, the fixed-modulus dense long-division loop scans the
degree downward and performs at most `n` eliminations, each over a fixed-width
modulus. Projection and checksum are bounded by the fixed field degree, giving
the independently derived model `n`. The shared target has the same dominant
generic scan. For `runPacked1`, reduction performs at most `n` single-word
leading-term eliminations, which supplies the mode-2 linear upper bound; a
matching lower bound is unavailable because cancellations may skip degrees.

## Verdicts

The clean scientific run was recorded at commit
`60beb2d32177b746bd8085ecf376a63831ab6632` on CPU 7 of `chungus2` (AMD EPYC
9455, Linux x86_64, Lean 4.34.0-rc2). Every parametric rung used three outer
trials, and the verdict used their median. Inputs are deterministic and use no
random seed.

```sh
taskset -c 7 ./.lake/build/bin/hexgfq_bench run \
  Hex.GfqBench.runGeneric21 Hex.GfqBench.runPacked1 \
  Hex.GfqBench.runShared21 Hex.GfqBench.runGeneric28 \
  Hex.GfqBench.runPacked8 Hex.GfqBench.runGeneric136 \
  Hex.GfqBench.runGenericC136 \
  Hex.GfqBench.runGenericModulusChecksum \
  Hex.GfqBench.runPackedModulusChecksum \
  --export-file reports/bench-results/hex-gfq-60beb2d-issue9814-final.json
```

The export has SHA-256
`3f83d3763bcccdbcf0e591254070173890dfd3c40264ade4c16c15e0983fd5af`.

| registration | mode | model / budget | scientific result | top-rung median | top hash |
|---|---:|---:|---|---:|---:|
| `runGeneric21` | 1 | `n`, `64..4096` | consistent, `beta=-0.056` | `131.672 us` | `0x0` |
| `runPacked1` | 2 | `n`, `1..63` | within upper bound (observed faster), harness `beta=-0.182` | `7.955 us` | `0x0` |
| `runShared21` | 1 | `n`, `512..32768` | consistent, `beta=-0.029` | `2.212 ms` | `0xbf58476d1ce4e5b9` |
| `runGeneric28` | 1 | `n`, `16..512` | consistent, `beta=+0.066` | `78.357 us` | `0xbf58476d1ce4e5ba` |
| `runPacked8` | 3 | `100 us` | hash match, within budget | `11.267 us` | `0xc1` |
| `runGeneric136` | 1 | `n`, `12..384` | consistent, `beta=+0.053` | `76.847 us` | `0xc248316c3dea496b` |
| `runGenericC136` | 1 | `n`, `12..384` | consistent, `beta=+0.062` | `74.920 us` | `0xc248316c3dea496b` |

The harness renders `runPacked1` as inconclusive because its negative residual
slope is too large for a two-sided mode-1 verdict. That direction is exactly
the distinct mode-2 pass: observed growth is faster than the source-derived
linear upper bound, not slower. The shared top hashes for the explicit and
instance-selected odd-prime spellings also agree; their similar timings are
consistent with instance selection adding no runtime work.

### Packed degree-eight mode audit

Mode 1 was attempted on the complete useful single-word ladder
`1, 2, 4, 8, 16, 32, 63`. Each dense input has exact polynomial degree `n`,
and the independently derived attempted model was `n`. A clean, CPU-pinned,
three-trial run at commit `92abb5d4c` was inconclusive with `beta=+0.245`,
meaning observed growth was slower than the linear declaration. The same
positive direction fails the mode-2 linear upper-bound test, so neither
stronger mode is available. The audit artifact is
`reports/bench-results/hex-gfq-packed8-parametric-audit-92abb5d-issue9814.json`
(SHA-256
`b4dce4778c0945c1d576fa35f3fc9cff75a2d7d1add912041634d7f75494bf5c`).

Mode 3 therefore uses the canonical maximal-degree dense word
`0xffffffffffffffff`. Its five clean measurements were `11.106..11.477 us`
with median `11.267 us`, all hashes agreed with expected hash `0xc1`. No
comparator or external requirement supplies a ceiling, so the absolute
`100 us` gate is the measured clean baseline rounded up with an 8.8x margin
for host variation. This target deliberately gives up asymptotic regression
detection for the bounded single-word operation.

The two limited fixed anchors also match their expected hashes:

| fixed hash anchor | median | range | observed / expected hash |
|---|---:|---:|---:|
| `runGenericModulusChecksum` | `85 ns` | `84..86 ns` | `0x3403d2eb08b5d5fc` |
| `runPackedModulusChecksum` | `47 ns` | `46..48 ns` | `0x1ce80893b914478a` |

Their tiny bodies read runtime `IO.Ref`s and intentionally anchor only modulus
projection and checksumming; they are not performance evidence.

Smoke wiring is checked separately with:

```sh
lake exe hexgfq_bench list
lake exe hexgfq_bench verify
```

All nine retained registrations pass `verify`.

## Comparator Ratios

`HexGFq/SPEC/hex-gfq.md` classifies this as a structural convenience layer and
requires no external Phase-4 comparator. HexGFqField owns comparison of the
underlying generic quotient-field arithmetic with FLINT, and HexGF2 owns the
packed arithmetic comparison with NTL. The internal common-domain path is
covered by `runShared21`; there are no external HexGFq ratios to record.

## Profile

Fresh profiles were recorded from clean commit
`2b6da015378654cbbabe9639df752e3eec042b61` on `chungus2` (AMD EPYC 9455,
Linux x86_64), Lean `leanprover/lean4:4.34.0-rc2`, lean-bench
`fa30c2763cf523f3ac8e46dc3a1dad0845a40098`, lean-bench-samply
`9356baa2f5757ee40320a897bd284914d5bb9f5e`, and samply `0.13.1`. The wrapper
used `--rate 999 --unstable-presymbolicate`, retained only the benchmark
thread's timed regions, and passed calibration, confidence, and +/-5 ms
sensitivity checks in every run. Inputs are deterministic and use no seed.
Raw filtered artifacts are developer-local under `/tmp`.

### `generic-constructor-projection`

```sh
scripts/profile/run_profile.sh ./.lake/build/bin/hexgfq_bench \
  Hex.GfqBench.runGeneric21 256 5000000000
```

Leaf cost was Lean runtime 35.34%, Hex Lean code 36.04%, allocation 22.90%,
and other 5.71%. Inclusive Hex cost was led by `runGeneric21` 99.24%,
`GFqRing.reduceMod` 99.05%, `DensePoly.divModArray` 93.48%,
`DensePoly.trimTrailingZerosGo` 41.21%, and
`DensePoly.subtractScaledShiftStep` 20.21%. This directly attributes the
generic constructor family to fixed-modulus dense reduction.

```text
bench thread:       name='hexgfq_bench' tid=274575
calibration:        absolute-monotonic-ms, residual 1.228 ms (limit 5 ms)
regions:            13, total timed = 4783.8 ms
expected samples:   ~4779 on bench thread
retained samples:   4725 on bench thread (9 rejected outside windows)
other-thread noise: 0 samples within timed windows
sensitivity +/-5 ms: passed
confidence:         passed
filtered profile:   /tmp/hex-profile-runGeneric21-256.json.gz
```

### `packed-constructor-projection`

```sh
scripts/profile/run_profile.sh ./.lake/build/bin/hexgfq_bench \
  Hex.GfqBench.runPacked1 63 5000000000
```

Leaf cost was allocation 34.69%, Hex Lean code 33.19%, Lean runtime 31.95%,
and GMP 0.17%. Inclusive Hex cost was led by `GF2n.reduce` 99.32%,
`GF2Poly.packedReduceWord` 99.05%, `GF2Poly.mod` 97.55%,
`GF2Poly.divModAux` 97.41%, `GF2Poly.add` 26.33%, and `GF2Poly.degree?`
25.38%. This identifies the packed reduction loop measured by the mode-2
family and the mode-3 degree-eight target.

```text
bench thread:       name='hexgfq_bench' tid=305970
calibration:        absolute-monotonic-ms, residual 2.699 ms (limit 5 ms)
regions:            11, total timed = 4132.2 ms
expected samples:   ~4128 on bench thread
retained samples:   4125 on bench thread (392 rejected outside windows)
other-thread noise: 0 samples within timed windows
sensitivity +/-5 ms: passed
confidence:         passed
filtered profile:   /tmp/hex-profile-runPacked1-63.json.gz
```

### `packed-generic-shared-bridge`

```sh
scripts/profile/run_profile.sh ./.lake/build/bin/hexgfq_bench \
  Hex.GfqBench.runShared21 512 5000000000
```

Leaf cost was Lean runtime 34.54%, Hex Lean code 33.36%, allocation 25.28%,
other 6.76%, and GMP 0.06%. Inclusive Hex cost was led by `runShared21`
99.86%, generic `GFqRing.reduceMod` 80.66% / `DensePoly.divModArray` 78.49%,
and packed `GF2n.reduce` 18.79% / `GF2Poly.packedReduceWord` 18.73%. Both
public paths execute, with the generic scan dominant as declared.

```text
bench thread:       name='hexgfq_bench' tid=314111
calibration:        absolute-monotonic-ms, residual 1.243 ms (limit 5 ms)
regions:            9, total timed = 5121.2 ms
expected samples:   ~5116 on bench thread
retained samples:   5072 on bench thread (132 rejected outside windows)
other-thread noise: 0 samples within timed windows
sensitivity +/-5 ms: passed
confidence:         passed
filtered profile:   /tmp/hex-profile-runShared21-512.json.gz
```

### `deep-binary-constructor-projection`

```sh
scripts/profile/run_profile.sh ./.lake/build/bin/hexgfq_bench \
  Hex.GfqBench.runGeneric28 512 5000000000
```

Leaf cost was Lean runtime 34.90%, Hex Lean code 32.13%, allocation 26.15%,
and other 6.82%. Inclusive Hex cost was led by `runGeneric28` 99.90%,
`GFqRing.reduceMod` 99.78%, `DensePoly.divModArray` 98.82%, and
`DensePoly.subtractScaledShiftStep` 66.32%. Together with the packed profile
above, this attributes both representations at the deepest binary entry.

```text
bench thread:       name='hexgfq_bench' tid=324503
calibration:        absolute-monotonic-ms, residual 1.520 ms (limit 5 ms)
regions:            8, total timed = 4968.3 ms
expected samples:   ~4963 on bench thread
retained samples:   4911 on bench thread (19 rejected outside windows)
other-thread noise: 0 samples within timed windows
sensitivity +/-5 ms: passed
confidence:         passed
filtered profile:   /tmp/hex-profile-runGeneric28-512.json.gz
```

### `odd-prime-constructor-projection`

```sh
scripts/profile/run_profile.sh ./.lake/build/bin/hexgfq_bench \
  Hex.GfqBench.runGeneric136 384 5000000000
```

Leaf cost was Lean runtime 35.68%, Hex Lean code 31.29%, allocation 24.61%,
and other 8.43%. Inclusive Hex cost was led by `runGeneric136` 99.96%,
`GFqRing.reduceMod` 99.10%, `DensePoly.divModArray` 97.67%, and
`DensePoly.subtractScaledShiftStep` 65.44%. `runGenericC136` has the same
compiled constructor/projection path and matching output hash.

```text
bench thread:       name='hexgfq_bench' tid=331614
calibration:        absolute-monotonic-ms, residual 0.898 ms (limit 5 ms)
regions:            9, total timed = 2272.9 ms
expected samples:   ~2271 on bench thread
retained samples:   2231 on bench thread (234 rejected outside windows)
other-thread noise: 0 samples within timed windows
sensitivity +/-5 ms: passed
confidence:         passed
filtered profile:   /tmp/hex-profile-runGeneric136-384.json.gz
```

## Concerns

No HexGFq performance-evidence concern remains. Promotion is intentionally
withheld solely by the dependency-coupled Phase-4 gate: HexConway and HexGF2
remain at Phase 3.
