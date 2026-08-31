# HexGFq Performance Report

HexGFq's constructor and projection surfaces follow the ordered complexity
claim policy. All seven operation registrations use mode 1. Two additional
fixed registrations are expected-hash anchors for the selected Conway moduli,
not performance claims.

The evidence is complete, but `libraries.yml` remains at `done_through: 3`:
the Phase-4 dependency gate cannot advance HexGFq while its direct dependencies
HexConway and HexGF2 are themselves at Phase 3.

## Bench Targets

- `Hex.GfqBench.runGeneric21`: model `n`, generic constructor and projection at
  `GFq 2 1` on deterministic prefix-nested binary representatives.
- `Hex.GfqBench.runPacked1`: model `2 + (min n 63 + 1) / 2`, packed constructor
  and projection at `GF2q 1` on `1 + x + ... + x^n`.
- `Hex.GfqBench.runShared21`: model `n`, packed and generic constructor and
  projection on a paired deterministic binary family.
- `Hex.GfqBench.runGeneric28`: model `n`, generic constructor and projection at
  the deepest committed binary entry, `GFq 2 8`.
- `Hex.GfqBench.runPacked8`: model
  `2 + (max 8 (min n 63) + 1 - 8)`, packed constructor and projection at
  `GF2q 8` on a prepared modulus multiple with a dense quotient.
- `Hex.GfqBench.runGeneric136`: model `n`, explicit-entry generic constructor
  and projection at `GFq 13 6`.
- `Hex.GfqBench.runGenericC136`: model `n`, instance-selected `GFqC`
  constructor and projection at `GFqC 13 6`.
- `Hex.GfqBench.runGenericModulusChecksum` and
  `Hex.GfqBench.runPackedModulusChecksum`: fixed expected-hash anchors for the
  selected degree-one moduli; neither makes a performance claim.

For the generic targets, the fixed-modulus dense long-division loop scans the
degree downward and performs at most `n` eliminations, each over a fixed-width
modulus. Projection and checksum are bounded by the fixed field degree. The
shared target has the same dominant generic scan.

The packed models count their operations more precisely. Dividing
`1 + x + ... + x^n` by `x + 1` gives an alternating quotient with exactly
`(n + 1) / 2` nonzero terms, hence that many single-word leading-term
eliminations. The degree-eight preparation constructs the fixed modulus times
`1 + x + ... + x^(n-8)`. Its remainder is zero, and uniqueness of division
makes all `n - 7` quotient terms leading-term eliminations. Both models add two
fixed stages for field packaging and representative projection. Preparation is
outside the timed region.

## Verdicts

The clean scientific run was recorded at commit
`ace3da4ca2e54049505ba13db6c0cc8a0adf0837` on CPU 30 of `chungus2` (AMD EPYC
9455, Linux x86_64, Lean 4.34.0-rc2). Every parametric rung used three outer
trials, and the verdict used their median. Inputs are deterministic and use no
random seed.

```sh
taskset -c 30 ./.lake/build/bin/hexgfq_bench run \
  Hex.GfqBench.runGenericC136 Hex.GfqBench.runGeneric21 \
  Hex.GfqBench.runGeneric136 Hex.GfqBench.runShared21 \
  Hex.GfqBench.runPacked8 Hex.GfqBench.runGeneric28 \
  Hex.GfqBench.runPacked1 \
  Hex.GfqBench.runGenericModulusChecksum \
  Hex.GfqBench.runPackedModulusChecksum \
  --export-file reports/bench-results/hex-gfq-ace3da4-issue9814-final.json
```

The export has SHA-256
`1c61dab3e8f9a4b738831a34cf0e78dbe5880eeeb01d3438c53d03d79d22d60a`.

| registration | mode | model / range | scientific result | top-rung median | top hash |
|---|---:|---|---|---:|---:|
| `runGeneric21` | 1 | `n`, `64..4096` | consistent, `beta=-0.021` | `196.456 us` | `0xbf58476d1ce4e5ba` |
| `runPacked1` | 1 | `2 + (n+1)/2`, `1..63` | consistent, `beta=+0.034` | `7.792 us` | `0x0` |
| `runShared21` | 1 | `n`, `512..32768` | consistent, `beta=-0.034` | `1.840 ms` | `0xbf58476d1ce4e5b9` |
| `runGeneric28` | 1 | `n`, `16..512` | consistent, `beta=+0.019` | `68.582 us` | `0x95cc5931896b59e7` |
| `runPacked8` | 1 | `2 + (n-7)`, `8..63` | consistent, `beta=+0.034` | `13.140 us` | `0x0` |
| `runGeneric136` | 1 | `n`, `12..384` | consistent, `beta=+0.064` | `75.117 us` | `0xc248316c3dea496b` |
| `runGenericC136` | 1 | `n`, `12..384` | consistent, `beta=+0.047` | `72.339 us` | `0xc248316c3dea496b` |

A positive residual slope means observed time grows faster than the declared
model; a negative slope means it grows more slowly. Every slope above remains
inside the harness's two-sided mode-1 acceptance band. The explicit and
instance-selected odd-prime spellings have matching top hashes, consistent
with instance selection adding no runtime work.

The two fixed anchors also match their expected hashes:

| fixed hash anchor | median | range | observed / expected hash |
|---|---:|---:|---:|
| `runGenericModulusChecksum` | `86 ns` | `85..88 ns` | `0x3403d2eb08b5d5fc` |
| `runPackedModulusChecksum` | `46 ns` | `46..46 ns` | `0x1ce80893b914478a` |

Their tiny bodies read runtime `IO.Ref`s and intentionally anchor only modulus
projection and checksumming. Smoke wiring is checked separately with:

```sh
lake exe hexgfq_bench list
lake exe hexgfq_bench verify
```

All nine registrations pass `verify`.

## Comparator Ratios

`HexGFq/SPEC/hex-gfq.md` classifies this as a structural convenience layer and
requires no external Phase-4 comparator. HexGFqField owns comparison of the
underlying generic quotient-field arithmetic with FLINT, and HexGF2 owns the
packed arithmetic comparison with NTL. The internal common-domain path is
covered by `runShared21`; there are no external HexGFq ratios to record.

## Profile

Fresh profiles were recorded from clean commit
`ace3da4ca2e54049505ba13db6c0cc8a0adf0837` on `chungus2` (AMD EPYC 9455,
Linux x86_64), Lean `leanprover/lean4:4.34.0-rc2`, lean-bench
`fa30c2763cf523f3ac8e46dc3a1dad0845a40098`, lean-bench-samply
`9356baa2f5757ee40320a897bd284914d5bb9f5e`, and samply `0.13.1`. The wrapper
used `--rate 999 --unstable-presymbolicate`, retained only the benchmark
thread's timed regions, and passed calibration, confidence, and +/-5 ms
sensitivity checks in every run. Raw filtered artifacts are developer-local
under `/tmp`.

### `generic-constructor-projection`

```sh
scripts/profile/run_profile.sh ./.lake/build/bin/hexgfq_bench \
  Hex.GfqBench.runGeneric21 256 5000000000
```

Leaf cost was Hex Lean code 37.75%, Lean runtime 32.13%, allocation 22.58%,
and other 7.54%. Inclusive Hex cost was led by `runGeneric21` 99.56%,
`GFqRing.reduceMod` 98.98%, `DensePoly.divModArray` 95.55%, and
`DensePoly.subtractScaledShiftStep` 29.22%.

```text
bench thread: tid=977612; regions=12; total timed=3451.7 ms
calibration: absolute-monotonic-ms, residual 0.660 ms (limit 5 ms)
expected/retained samples: 3448/3436; rejected=55; other-thread noise=0
sensitivity +/-5 ms: passed; confidence: passed
```

### `packed-constructor-projection`

```sh
scripts/profile/run_profile.sh ./.lake/build/bin/hexgfq_bench \
  Hex.GfqBench.runPacked1 63 5000000000
```

Leaf cost was Lean runtime 37.42%, Hex Lean code 35.09%, allocation 27.44%,
and GMP 0.05%. Inclusive Hex cost was led by `GF2n.reduce` 99.12%,
`GF2Poly.packedReduceWord` 99.07%, `GF2Poly.mod` 98.17%, and
`GF2Poly.divModAux` 98.00%.

```text
bench thread: tid=978334; regions=13; total timed=4044.0 ms
calibration: absolute-monotonic-ms, residual 1.090 ms (limit 5 ms)
expected/retained samples: 4040/3998; rejected=8; other-thread noise=0
sensitivity +/-5 ms: passed; confidence: passed
```

### `packed-generic-shared-bridge`

```sh
scripts/profile/run_profile.sh ./.lake/build/bin/hexgfq_bench \
  Hex.GfqBench.runShared21 512 5000000000
```

Leaf cost was Hex Lean code 35.17%, Lean runtime 34.98%, allocation 22.70%,
other 7.11%, and GMP 0.04%. Inclusive cost included generic
`GFqRing.reduceMod` 77.83% / `DensePoly.divModArray` 74.93% and packed
`GF2n.reduce` 21.72% / `GF2Poly.packedReduceWord` 21.70%. Both public paths
execute, with the generic scan dominant as declared.

```text
bench thread: tid=978779; regions=11; total timed=4710.5 ms
calibration: absolute-monotonic-ms, residual 1.831 ms (limit 5 ms)
expected/retained samples: 4706/4683; rejected=8; other-thread noise=0
sensitivity +/-5 ms: passed; confidence: passed
```

### `deep-binary-constructor-projection`

The generic and packed degree-eight registrations were both measured directly:

```sh
scripts/profile/run_profile.sh ./.lake/build/bin/hexgfq_bench \
  Hex.GfqBench.runGeneric28 512 5000000000
scripts/profile/run_profile.sh ./.lake/build/bin/hexgfq_bench \
  Hex.GfqBench.runPacked8 63 5000000000
```

For `runGeneric28`, leaf cost was Hex Lean code 37.32%, Lean runtime 29.94%,
allocation 24.23%, and other 8.51%. Inclusive cost was led by
`runGeneric28` 99.91%, `GFqRing.reduceMod` 99.78%, and
`DensePoly.divModArray` 98.40%. For `runPacked8`, leaf cost was Lean runtime
36.86%, Hex Lean code 32.93%, allocation 29.74%, GMP 0.38%, and other 0.09%.
Inclusive cost was led by `GF2n.reduce` 98.89%,
`GF2Poly.packedReduceWord` 98.77%, `GF2Poly.mod` 98.16%, and
`GF2Poly.divModAux` 97.98%.

```text
runGeneric28: tid=980419; regions=10; total timed=4629.7 ms
  calibration residual=1.153 ms; expected/retained=4625/4619; rejected=8
runPacked8: tid=981210; regions=12; total timed=3435.4 ms
  calibration residual=0.804 ms; expected/retained=3432/3416; rejected=37
both: other-thread noise=0; sensitivity +/-5 ms passed; confidence passed
```

### `odd-prime-constructor-projection`

```sh
scripts/profile/run_profile.sh ./.lake/build/bin/hexgfq_bench \
  Hex.GfqBench.runGeneric136 384 5000000000
```

Leaf cost was Hex Lean code 33.41%, Lean runtime 31.16%, allocation 24.64%,
and other 10.80%. Inclusive Hex cost was led by `runGeneric136` 99.92%,
`GFqRing.reduceMod` 99.55%, `DensePoly.divModArray` 98.30%, and
`DensePoly.subtractScaledShiftStep` 63.25%. `runGenericC136` uses the same
compiled constructor/projection path and has the same output hash.

```text
bench thread: tid=981601; regions=10; total timed=4960.2 ms
calibration: absolute-monotonic-ms, residual 1.007 ms (limit 5 ms)
expected/retained samples: 4955/4936; rejected=8; other-thread noise=0
sensitivity +/-5 ms: passed; confidence: passed
```

## Concerns

No HexGFq performance-evidence concern remains. Promotion is intentionally
withheld solely by the dependency-coupled Phase-4 gate: HexConway and HexGF2
remain at Phase 3.
