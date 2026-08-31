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
  `GF2q 8` on a prepared modulus multiple with a dense quotient and a varying
  low-degree remainder.
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
`1 + x + ... + x^(n-8)`, plus a varying polynomial of degree less than eight.
Uniqueness of division makes all `n - 7` quotient terms leading-term
eliminations; the low remainder does not change the quotient. Both models count
field packaging and representative projection as two fixed abstract
elimination units. Preparation is outside the timed region.

## Verdicts

The clean scientific run was recorded at commit
`cf52eeccc67bdd1759ff6a28d11589f37180d3bf` on CPU 2 of `chungus2` (AMD EPYC
9455, Linux x86_64, Lean 4.34.0-rc2). Every parametric rung used three outer
trials, and the verdict used their median. Inputs are deterministic and use no
random seed.

```sh
taskset -c 2 ./.lake/build/bin/hexgfq_bench run \
  Hex.GfqBench.runGenericC136 Hex.GfqBench.runGeneric21 \
  Hex.GfqBench.runGeneric136 Hex.GfqBench.runShared21 \
  Hex.GfqBench.runPacked8 Hex.GfqBench.runGeneric28 \
  Hex.GfqBench.runPacked1 \
  Hex.GfqBench.runGenericModulusChecksum \
  Hex.GfqBench.runPackedModulusChecksum \
  --export-file reports/bench-results/hex-gfq-cf52eec-issue9814-final.json
```

The export has SHA-256
`8683a0dc636ae8da3db7220e3406a9936c9abb30f98bf52fbb88a5bb5894c69a`.

| registration | mode | model | ladder / fitted range | scientific result | top median | top hash |
|---|---:|---|---|---|---:|---:|
| `runGeneric21` | 1 | `n` | `64..4096` / `128..4096` | consistent, `beta=-0.030` | `194.075 us` | `0xbf58476d1ce4e5ba` |
| `runPacked1` | 1 | `2 + (n+1)/2` | `2..63` / `4..63` | consistent, `beta=+0.028` | `7.799 us` | `0x0` |
| `runShared21` | 1 | `n` | `512..32768` / `1024..32768` | consistent, `beta=-0.142` | `1.824 ms` | `0xbf58476d1ce4e5b9` |
| `runGeneric28` | 1 | `n` | `32..512` / `64..512` | consistent, `beta=+0.011` | `67.036 us` | `0x95cc5931896b59e7` |
| `runPacked8` | 1 | `2 + (n-7)` | `8..63` / `12..63` | consistent, `beta=+0.023` | `13.358 us` | `0xff` |
| `runGeneric136` | 1 | `n` | `24..384` / `48..384` | consistent, `beta=+0.042` | `73.445 us` | `0xc248316c3dea496b` |
| `runGenericC136` | 1 | `n` | `24..384` / `48..384` | consistent, `beta=+0.051` | `73.166 us` | `0xc248316c3dea496b` |

A positive residual slope means observed time grows faster than the declared
model; a negative slope means it grows more slowly. Every slope above remains
inside the harness's two-sided mode-1 acceptance band. The explicit and
instance-selected odd-prime spellings have matching top hashes, consistent
with instance selection adding no runtime work. The harness reserves the first
rung of each ladder for calibration and excludes it from the regression; both
the registered ladder and fitted range are shown above. `runPacked8` produces
`0x1`, `0x1f`, and `0xff` across its ladder, so its result hash is an
informative conformance signal rather than a constant zero.

The two fixed anchors also match their expected hashes:

| fixed hash anchor | median | range | observed / expected hash |
|---|---:|---:|---:|
| `runGenericModulusChecksum` | `87 ns` | `85..88 ns` | `0x3403d2eb08b5d5fc` |
| `runPackedModulusChecksum` | `47 ns` | `46..47 ns` | `0x1ce80893b914478a` |

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
`cf52eeccc67bdd1759ff6a28d11589f37180d3bf` on `chungus2` (AMD EPYC 9455,
Linux 6.12.100 x86_64, NixOS 26.11), Lean `leanprover/lean4:4.34.0-rc2`, lean-bench
`fa30c2763cf523f3ac8e46dc3a1dad0845a40098`, lean-bench-samply
`9356baa2f5757ee40320a897bd284914d5bb9f5e`, and samply `0.13.1`. The wrapper
used `--rate 999 --unstable-presymbolicate`, retained only the benchmark
thread's timed regions, and passed calibration, confidence, and +/-5 ms
sensitivity checks in every run. The raw filtered artifacts are
`/tmp/hex-profile-runGeneric21-256.json.gz`,
`/tmp/hex-profile-runPacked1-63.json.gz`,
`/tmp/hex-profile-runShared21-512.json.gz`,
`/tmp/hex-profile-runGeneric28-512.json.gz`,
`/tmp/hex-profile-runPacked8-63.json.gz`, and
`/tmp/hex-profile-runGeneric136-384.json.gz`.

### `generic-constructor-projection`

```sh
scripts/profile/run_profile.sh ./.lake/build/bin/hexgfq_bench \
  Hex.GfqBench.runGeneric21 256 5000000000
```

Leaf cost was Hex Lean code 40.02%, Lean runtime 31.76%, allocation 22.31%,
and other 5.91%. Inclusive Hex cost was led by `runGeneric21` 99.25%,
`GFqRing.reduceMod` 98.68%, `DensePoly.divModArray` 94.39%, and
`DensePoly.subtractScaledShiftStep` 30.32%.

```text
bench thread: tid=1209132; regions=12; total timed=3353.3 ms
calibration: absolute-monotonic-ms, residual 2.478 ms (limit 5 ms)
expected/retained samples: 3350/3331; rejected=8; other-thread noise=0
sensitivity +/-5 ms: passed; confidence: passed
```

### `packed-constructor-projection`

```sh
scripts/profile/run_profile.sh ./.lake/build/bin/hexgfq_bench \
  Hex.GfqBench.runPacked1 63 5000000000
```

Leaf cost was Lean runtime 37.90%, Hex Lean code 36.16%, allocation 25.50%,
GMP 0.37%, and other 0.07%. Inclusive Hex cost was led by `GF2n.reduce` 98.90%,
`GF2Poly.packedReduceWord` 98.80%, `GF2Poly.mod` 97.60%, and
`GF2Poly.divModAux` 97.36%.

```text
bench thread: tid=1210907; regions=13; total timed=4115.7 ms
calibration: absolute-monotonic-ms, residual 1.068 ms (limit 5 ms)
expected/retained samples: 4112/4087; rejected=7; other-thread noise=0
sensitivity +/-5 ms: passed; confidence: passed
```

### `packed-generic-shared-bridge`

```sh
scripts/profile/run_profile.sh ./.lake/build/bin/hexgfq_bench \
  Hex.GfqBench.runShared21 512 5000000000
```

Leaf cost was Lean runtime 35.54%, Hex Lean code 33.07%, allocation 24.13%,
other 7.16%, and GMP 0.10%. Inclusive cost included generic
`GFqRing.reduceMod` 76.53% / `DensePoly.divModArray` 74.42% and packed
`GF2n.reduce` 22.94% / `GF2Poly.packedReduceWord` 22.90%. Both public paths
execute, with the generic scan dominant as declared.

```text
bench thread: tid=1211800; regions=11; total timed=4892.2 ms
calibration: absolute-monotonic-ms, residual 1.261 ms (limit 5 ms)
expected/retained samples: 4887/4874; rejected=14; other-thread noise=0
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

For `runGeneric28`, leaf cost was Hex Lean code 34.66%, Lean runtime 30.01%,
allocation 27.51%, and other 7.82%. Inclusive cost was led by
`runGeneric28` 99.84%, `GFqRing.reduceMod` 99.71%, and
`DensePoly.divModArray` 98.07%. For `runPacked8`, leaf cost was Lean runtime
35.60%, Hex Lean code 33.68%, allocation 30.54%, and GMP 0.17%. Inclusive cost
was led by `GF2n.reduce` 99.16%, `GF2Poly.packedReduceWord` 99.04%,
`GF2Poly.mod` 98.57%, and `GF2Poly.divModAux` 98.40%.

```text
runGeneric28: tid=1213096; regions=10; total timed=4428.4 ms
  calibration residual=1.980 ms; expected/retained=4424/4409; rejected=7
runPacked8: tid=1214202; regions=12; total timed=3447.3 ms
  calibration residual=1.211 ms; expected/retained=3444/3435; rejected=8
both: other-thread noise=0; sensitivity +/-5 ms passed; confidence passed
```

### `odd-prime-constructor-projection`

```sh
scripts/profile/run_profile.sh ./.lake/build/bin/hexgfq_bench \
  Hex.GfqBench.runGeneric136 384 5000000000
```

Leaf cost was Hex Lean code 33.11%, Lean runtime 32.86%, allocation 24.18%,
and other 9.86%. Inclusive Hex cost was led by `runGeneric136` 99.90%,
`GFqRing.reduceMod` 99.63%, `DensePoly.divModArray` 98.24%, and
`DensePoly.subtractScaledShiftStep` 66.42%. `runGenericC136` uses the same
compiled constructor/projection path and has the same output hash.

```text
bench thread: tid=1215596; regions=10; total timed=4839.9 ms
calibration: absolute-monotonic-ms, residual 0.876 ms (limit 5 ms)
expected/retained samples: 4835/4827; rejected=7; other-thread noise=0
sensitivity +/-5 ms: passed; confidence: passed
```

## Concerns

No HexGFq performance-evidence concern remains. Promotion is intentionally
withheld solely by the dependency-coupled Phase-4 gate: HexConway and HexGF2
remain at Phase 3.
