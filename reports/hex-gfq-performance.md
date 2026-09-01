# HexGFq Performance Report

HexGFq's constructor and projection surfaces follow the ordered complexity
claim policy. All seven operation registrations use mode 1. Two additional
fixed registrations are expected-hash anchors for the selected Conway moduli,
not performance claims.

The requested constructor/projection evidence is complete, but `libraries.yml`
remains at `done_through: 3`: the Phase-4 dependency gate cannot advance HexGFq
while its direct dependency HexGF2 remains at Phase 3.

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
`2ac0ce87fbfe842fc76f98d2fd0426a199dcd778` on CPU 5 of `chungus2` (AMD EPYC
9455, Linux x86_64, Lean 4.34.0-rc2). Every parametric rung used three outer
trials, and the verdict used their median. Inputs are deterministic and use no
random seed.

```sh
taskset -c 5 ./.lake/build/bin/hexgfq_bench run \
  Hex.GfqBench.runGenericC136 Hex.GfqBench.runGeneric21 \
  Hex.GfqBench.runGeneric136 Hex.GfqBench.runShared21 \
  Hex.GfqBench.runPacked8 Hex.GfqBench.runGeneric28 \
  Hex.GfqBench.runPacked1 \
  Hex.GfqBench.runGenericModulusChecksum \
  Hex.GfqBench.runPackedModulusChecksum \
  --export-file reports/bench-results/hex-gfq-2ac0ce8-issue9814-final.json
```

The export has SHA-256
`fa2fae1d7483f6b18db56d970d91a4e1c18caff5bdc6140da0d2afdee4c648c6`.

| registration | mode | model | ladder / fitted range | scientific result | top median | top hash |
|---|---:|---|---|---|---:|---:|
| `runGeneric21` | 1 | `n` | `64..4096` / `128..4096` | consistent, `beta=-0.026` | `195.718 us` | `0xbf58476d1ce4e5ba` |
| `runPacked1` | 1 | `2 + (n+1)/2` | `2..63` / `4..63` | consistent, `beta=+0.026` | `7.826 us` | `0x0` |
| `runShared21` | 1 | `n` | `2048..32768` / `4096..32768` | consistent, `beta=-0.006` | `1.824 ms` | `0xbf58476d1ce4e5b9` |
| `runGeneric28` | 1 | `n` | `32..512` / `64..512` | consistent, `beta=+0.006` | `67.778 us` | `0x95cc5931896b59e7` |
| `runPacked8` | 1 | `2 + (n-7)` | `8..63` / `13..63` | consistent, `beta=+0.011` | `13.213 us` | `0xff` |
| `runGeneric136` | 1 | `n` | `24..384` / `48..384` | consistent, `beta=+0.038` | `72.680 us` | `0xc248316c3dea496b` |
| `runGenericC136` | 1 | `n` | `24..384` / `48..384` | consistent, `beta=+0.037` | `73.506 us` | `0xc248316c3dea496b` |

A positive residual slope means observed time grows faster than the declared
model; a negative slope means it grows more slowly. Every slope above remains
inside the harness's two-sided mode-1 acceptance band. The explicit and
instance-selected odd-prime spellings have matching top hashes, consistent
with instance selection adding no runtime work. The configured 20% warmup
fraction excludes one leading rung from each six- or seven-rung regression;
both the registered ladder and fitted range are shown above. `runPacked8`
produces six distinct hashes across seven rungs, so its result hash is an
informative conformance signal rather than a constant zero. Every target uses
`signalFloorMultiplier := 1.0`; the artifact records per-target spawn floors of
24.7 to 88.4 ms, and the harness flags no rung as below its signal floor.

The two fixed anchors also match their expected hashes:

| fixed hash anchor | median | range | observed / expected hash |
|---|---:|---:|---:|
| `runGenericModulusChecksum` | `86 ns` | `86..87 ns` | `0x3403d2eb08b5d5fc` |
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
packed arithmetic comparison with NTL. `runShared21` jointly exercises the
packed and generic constructor/projection surfaces under one size parameter;
it is not an equivalence comparator and does not exercise `GF2q.toGFq`, which
is outside issue #9814's constructor/projection scope. There are no external
HexGFq ratios to record.

## Profile

Fresh profiles were recorded from clean commit
`2ac0ce87fbfe842fc76f98d2fd0426a199dcd778` on `chungus2` (AMD EPYC 9455,
Linux 6.12.100 x86_64, NixOS 26.11), Lean `leanprover/lean4:4.34.0-rc2`, lean-bench
`fa30c2763cf523f3ac8e46dc3a1dad0845a40098`, lean-bench-samply
`9356baa2f5757ee40320a897bd284914d5bb9f5e`, and samply `0.13.1`. The wrapper
used `--rate 999 --unstable-presymbolicate`, retained only the benchmark
thread's timed regions, and passed calibration, confidence, and +/-5 ms
sensitivity checks in every run. The raw filtered artifacts are
`/tmp/hex-profile-runGeneric21-256.json.gz`,
`/tmp/hex-profile-runPacked1-63.json.gz`,
`/tmp/hex-profile-runShared21-2048.json.gz`,
`/tmp/hex-profile-runGeneric28-512.json.gz`,
`/tmp/hex-profile-runPacked8-63.json.gz`, and
`/tmp/hex-profile-runGeneric136-384.json.gz`.

### `generic-constructor-projection`

```sh
scripts/profile/run_profile.sh ./.lake/build/bin/hexgfq_bench \
  Hex.GfqBench.runGeneric21 256 5000000000
```

Leaf cost was Hex Lean code 35.94%, Lean runtime 33.74%, allocation 22.21%,
and other 8.11%. Inclusive Hex cost was led by `runGeneric21` 99.70%,
`GFqRing.reduceMod` 99.01%, `DensePoly.divModArray` 95.07%, and
`DensePoly.subtractScaledShiftStep` 26.56%.

```text
bench thread: tid=1441020; regions=12; total timed=3368.1 ms
calibration: absolute-monotonic-ms, residual 1.651 ms (limit 5 ms)
expected/retained samples: 3365/3328; rejected=8; other-thread noise=0
sensitivity +/-5 ms: passed; confidence: passed
```

### `packed-constructor-projection`

```sh
scripts/profile/run_profile.sh ./.lake/build/bin/hexgfq_bench \
  Hex.GfqBench.runPacked1 63 5000000000
```

Leaf cost was Lean runtime 36.73%, Hex Lean code 35.07%, allocation 27.97%,
and GMP 0.22%. Inclusive Hex cost was led by `GF2n.reduce` 98.94%,
`GF2Poly.packedReduceWord` 98.79%, `GF2Poly.mod` 97.57%, and
`GF2Poly.divModAux` 97.20%.

```text
bench thread: tid=1441402; regions=13; total timed=4081.9 ms
calibration: absolute-monotonic-ms, residual 1.033 ms (limit 5 ms)
expected/retained samples: 4078/4040; rejected=8; other-thread noise=0
sensitivity +/-5 ms: passed; confidence: passed
```

### `packed-generic-shared-bridge`

```sh
scripts/profile/run_profile.sh ./.lake/build/bin/hexgfq_bench \
  Hex.GfqBench.runShared21 2048 5000000000
```

Leaf cost was Hex Lean code 38.91%, Lean runtime 32.03%, allocation 21.08%,
and other 7.98%. Inclusive cost included generic `GFqRing.reduceMod` 92.84% /
`DensePoly.divModArray` 89.82% and packed `GF2n.reduce` 7.03% /
`GF2Poly.packedReduceWord` 7.03%. Both public paths execute, with the generic
scan dominant as declared.

```text
bench thread: tid=1442105; regions=9; total timed=4017.1 ms
calibration: absolute-monotonic-ms, residual 0.975 ms (limit 5 ms)
expected/retained samples: 4013/4009; rejected=12; other-thread noise=0
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

For `runGeneric28`, leaf cost was Hex Lean code 37.34%, Lean runtime 30.42%,
allocation 24.20%, and other 8.04%. Inclusive cost was led by
`runGeneric28` 99.93%, `GFqRing.reduceMod` 99.89%, and
`DensePoly.divModArray` 98.34%. For `runPacked8`, leaf cost was Lean runtime
39.44%, Hex Lean code 34.88%, allocation 25.62%, and GMP 0.06%. Inclusive cost
was led by `GF2n.reduce` 99.07%, `GF2Poly.packedReduceWord` 99.04%,
`GF2Poly.mod` 98.29%, and `GF2Poly.divModAux` 98.20%.

```text
runGeneric28: tid=1445482; regions=10; total timed=4423.8 ms
  calibration residual=0.909 ms; expected/retained=4419/4392; rejected=8
runPacked8: tid=1446718; regions=12; total timed=3456.3 ms
  calibration residual=1.634 ms; expected/retained=3453/3443; rejected=7
both: other-thread noise=0; sensitivity +/-5 ms passed; confidence passed
```

### `odd-prime-constructor-projection`

```sh
scripts/profile/run_profile.sh ./.lake/build/bin/hexgfq_bench \
  Hex.GfqBench.runGeneric136 384 5000000000
```

Leaf cost was Hex Lean code 33.19%, Lean runtime 31.41%, allocation 26.71%,
and other 8.69%. Inclusive Hex cost was led by `runGeneric136` 99.96%,
`GFqRing.reduceMod` 99.62%, `DensePoly.divModArray` 98.13%, and
`DensePoly.subtractScaledShiftStep` 65.27%. `runGenericC136` uses the same
compiled constructor/projection path and has the same output hash.

```text
bench thread: tid=1447557; regions=10; total timed=4793.7 ms
calibration: absolute-monotonic-ms, residual 2.200 ms (limit 5 ms)
expected/retained samples: 4789/4766; rejected=7; other-thread noise=0
sensitivity +/-5 ms: passed; confidence: passed
```

## Concerns

No HexGFq performance-evidence concern remains. Promotion is intentionally
withheld solely by the dependency-coupled Phase-4 gate: HexGF2 remains at
Phase 3.
