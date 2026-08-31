# HexGFq Performance Report

HexGFq passes Phase 4. All seven constructor/projection registrations use the
strongest applicable mode, mode 1 (two-sided parametric), and pass at their
scientific settings. The only retained fixed registrations are expected-hash
anchors for the selected generic and packed Conway moduli; they are not
performance evidence.

## Bench Targets

- `Hex.GfqBench.runGeneric21`: `n`, generic constructor/projection at
  `GFq 2 1` on deterministic binary representatives of length `n`.
- `Hex.GfqBench.runPacked1`: `1`, packed constructor/projection at `GF2q 1`
  on independently generated fixed-width words.
- `Hex.GfqBench.runShared21`: `n`, packed and generic constructor/projection
  on a shared binary representative family at degree one.
- `Hex.GfqBench.runGeneric28`: `n`, generic constructor/projection at
  `GFq 2 8` on deterministic binary representatives of length `n`.
- `Hex.GfqBench.runPacked8`: `1`, packed constructor/projection at `GF2q 8`
  on independently generated fixed-width words.
- `Hex.GfqBench.runGeneric136`: `n`, explicit-entry generic
  constructor/projection at `GFq 13 6` on deterministic representatives of
  length `n`.
- `Hex.GfqBench.runGenericC136`: `n`, instance-selected `GFqC 13 6`
  constructor/projection on the same representative family.
- `Hex.GfqBench.runGenericModulusChecksum`: fixed expected-hash anchor for the
  selected generic degree-one Conway modulus; no performance claim.
- `Hex.GfqBench.runPackedModulusChecksum`: fixed expected-hash anchor for the
  selected packed degree-one Conway modulus and lower word; no performance
  claim.

The generic models follow from the compiled dense long-division kernel. With
the modulus degree and base prime fixed, its degree scan moves only downward,
for `O(n)` total scanning, and it performs at most `n` eliminations, each over
the fixed modulus width. Projection and checksum are bounded by the fixed field
degree. The packed models are constant because the input, modulus, reduction,
and projection all occupy one machine word; their parameter changes only the
independently generated word value while `prepPacked` holds the high bit at 63.
The shared model is linear because its generic scan dominates the constant
packed route. These models were derived from the kernels before measurement.

## Verdicts

Scientific evidence was recorded from clean commit
`3166b7e7428f7055d4f613f8514e0879e68f6e6d` on `chungus2` (AMD EPYC 9455,
Linux x86_64, Lean 4.34.0-rc2) with deterministic inputs and no random seed:

```sh
lake exe hexgfq_bench run \
  Hex.GfqBench.runGeneric21 Hex.GfqBench.runPacked1 \
  Hex.GfqBench.runShared21 Hex.GfqBench.runGeneric28 \
  Hex.GfqBench.runPacked8 Hex.GfqBench.runGeneric136 \
  Hex.GfqBench.runGenericC136 \
  Hex.GfqBench.runGenericModulusChecksum \
  Hex.GfqBench.runPackedModulusChecksum \
  --export-file reports/bench-results/hex-gfq-3166b7e-issue9814.json
```

The export is
`reports/bench-results/hex-gfq-3166b7e-issue9814.json`. Every performance
registration selects mode 1, so there is no stronger preceding mode to rule
out. All seven two-sided verdicts are **consistent with declared complexity**:

| registration | model | scientific ladder | `β` | top-rung time | top-rung hash |
|---|---:|---:|---:|---:|---:|
| `runGeneric21` | `n` | `64..4096` | `-0.046` | `136.311 µs` | `0x0` |
| `runPacked1` | `1` | `1..63` | `+0.027` | `11.301 µs` | `0x0` |
| `runShared21` | `n` | `512..32768` | `-0.017` | `2.275 ms` | `0xbf58476d1ce4e5b9` |
| `runGeneric28` | `n` | `16..512` | `+0.045` | `82.062 µs` | `0xbf58476d1ce4e5ba` |
| `runPacked8` | `1` | `1..63` | `+0.093` | `7.294 µs` | `0x32` |
| `runGeneric136` | `n` | `12..384` | `+0.056` | `79.938 µs` | `0xc248316c3dea496b` |
| `runGenericC136` | `n` | `12..384` | `+0.044` | `78.163 µs` | `0xc248316c3dea496b` |

The matching top-rung hashes and near-identical timings for `runGeneric136`
and `runGenericC136` confirm that instance selection adds no runtime work.

The two limited fixed anchors also pass. Their tiny bodies read runtime
`IO.Ref`s and intentionally measure only modulus projection/checksumming; the
sub-microsecond advisory therefore does not indicate missing performance
coverage:

| fixed hash anchor | median | range | observed / expected hash |
|---|---:|---:|---:|
| `runGenericModulusChecksum` | `94 ns` | `93..94 ns` | `0x3403d2eb08b5d5fc` |
| `runPackedModulusChecksum` | `50 ns` | `49..52 ns` | `0x1ce80893b914478a` |

Smoke wiring is checked separately with:

```sh
lake exe hexgfq_bench list
lake exe hexgfq_bench verify
```

All nine registrations pass `verify`.

## Comparator Ratios

`HexGFq/SPEC/hex-gfq.md` classifies this as a structural convenience layer and
requires no external Phase-4 comparator. The underlying generic quotient-field
arithmetic is compared with FLINT by HexGFqField, and the packed path is
compared with NTL by HexGF2. The internal common-domain packed/generic route is
covered by `runShared21`; there are no external HexGFq ratios to record.

## Profile

The timed-region-filtered profiles were recorded at commit
`3bc24c50fbe57487776c433106894ee544a6d656` on `carica` (Apple M2 Ultra,
arm64, Lean 4.30.0-rc2) with `scripts/profile/run_profile.sh`. The registration
renames in the current bench did not change the profiled target bodies:
`runGFqOfPolyReprChecksum` became `runGeneric21`,
`runGF2qOfWordReprProfileChecksum` became `runPacked1`, and
`runPackedGenericSharedChecksum` became `runShared21`. Raw filtered profile
files are developer-local under `/tmp`.

### `generic-constructor-projection`

```sh
scripts/profile/run_profile.sh ./.lake/build/bin/hexgfq_bench \
  Hex.GfqBench.runGFqOfPolyReprChecksum 256 5000000000
```

At `n=256`, leaf cost was Lean runtime/Std 51.0%, Hex Lean code 38.7%, other
compiler/system leaves 4.0%, allocation/free 3.6%, and GMP 2.7%. Inclusive Hex
cost was led by the target (99.9%), `GFqRing.reduceMod` (98.9%),
`DensePoly.divModArray` (86.0%), `DensePoly.divModArrayAux` (39.3%), and
`DensePoly.arrayDegreeAux` (27.2%). The dominant generic reduction is directly
attributable to `runGeneric21` and the other generic registrations use the same
fixed-modulus reduction kernel.

### `packed-constructor-projection`

```sh
scripts/profile/run_profile.sh ./.lake/build/bin/hexgfq_bench \
  Hex.GfqBench.runGF2qOfWordReprProfileChecksum 63 5000000000
```

At the representative single-word input, leaf cost was Lean runtime/Std 39.5%,
Hex Lean code 34.7%, allocation/free 15.0%, other compiler/system leaves 10.8%,
and GMP 0.1%. Inclusive Hex cost was led by `GF2n.reduce` (98.9%),
`GF2Poly.packedReduceWord` (97.8%), `GF2Poly.mod` (97.6%),
`GF2Poly.add` (27.6%), and `GF2Poly.degree?` (22.1%). The packed reduction is
directly attributable to `runPacked1`; `runPacked8` uses the same single-word
kernel with a different committed modulus.

### `packed-generic-shared-bridge`

```sh
scripts/profile/run_profile.sh ./.lake/build/bin/hexgfq_bench \
  Hex.GfqBench.runPackedGenericSharedChecksum 256 5000000000
```

At `n=256`, leaf cost was Lean runtime/Std 46.7%, Hex Lean code 40.4%, GMP
5.8%, allocation/free 3.6%, and other compiler/system leaves 3.6%. Inclusive
Hex cost was led by the target (92.6%), `GFqRing.reduceMod` (92.2%),
`DensePoly.divModArray` (87.9%), and the packed route through `GF2n.reduce` /
`GF2Poly.packedReduceWord` at 6.8% / 6.7%. This directly confirms the shared
family's declared attribution: the generic linear scan dominates the fixed
packed projection.

## Concerns

None.
