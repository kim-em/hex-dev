# HexPoly Performance Report

## Bench Targets

- `Hex.PolyBench.runAddChecksum`: `n`
- `Hex.PolyBench.runSubChecksum`: `n`
- `Hex.PolyBench.runMulChecksum`: `n * n`
- `Hex.PolyBench.runEval`: `n`
- `Hex.PolyBench.runComposeChecksum`: `n * n * n * n`
- `Hex.PolyBench.runDerivativeChecksum`: `n`
- `Hex.PolyBench.runDivModChecksum`: `n * n`
- `Hex.PolyBench.runDivChecksum`: `n * n`
- `Hex.PolyBench.runModChecksum`: `n * n`
- `Hex.PolyBench.runModByMonicChecksum`: `n * n`
- `Hex.PolyBench.runGcdChecksum`: `n * n`
- `Hex.PolyBench.runXGcdChecksum`: `n * n`
- `Hex.PolyBench.runContent`: `n`
- `Hex.PolyBench.runPrimitivePartChecksum`: `n`
- `Hex.PolyBench.runPolyCRTChecksum`: `n * n`

## Verdicts

Scientific run at commit `f5bfa6409349b42d02ece03f5cb5193c89118bb4` on
`carica` (Apple M2 Ultra, macOS 14.6.1), command:

```sh
lake exe hexpoly_bench run Hex.PolyBench.runEval Hex.PolyBench.runDivChecksum Hex.PolyBench.runContent Hex.PolyBench.runAddChecksum Hex.PolyBench.runPolyCRTChecksum Hex.PolyBench.runPrimitivePartChecksum Hex.PolyBench.runGcdChecksum Hex.PolyBench.runXGcdChecksum Hex.PolyBench.runDerivativeChecksum Hex.PolyBench.runSubChecksum Hex.PolyBench.runComposeChecksum Hex.PolyBench.runModByMonicChecksum Hex.PolyBench.runModChecksum Hex.PolyBench.runMulChecksum Hex.PolyBench.runDivModChecksum --export-file reports/bench-results/hex-poly-f5bfa6409349.json
```

The run used deterministic benchmark inputs from `HexPoly/Bench.lean`; random
seeds are not involved. The harness recorded `f5bfa64-dirty` because this
worktree had an unrelated pre-existing `.claude/CLAUDE.md` modification.
Export artefact: `reports/bench-results/hex-poly-f5bfa6409349.json`.

- `Hex.PolyBench.runEval`: consistent with declared complexity (`β=-0.005`,
  parameters `8192..131072`, final hash `0x41cb15d2703fbc8c`).
- `Hex.PolyBench.runDivChecksum`: consistent with declared complexity
  (`β=-0.052`, parameters `64..512`, final hash `0xc61628eb23727403`).
- `Hex.PolyBench.runContent`: consistent with declared complexity
  (`β=+0.002`, parameters `8192..131072`, final hash `0xc`).
- `Hex.PolyBench.runAddChecksum`: consistent with declared complexity
  (`β=+0.000`, parameters `8192..131072`, final hash
  `0xd5b9f2ba6ec00df3`).
- `Hex.PolyBench.runPolyCRTChecksum`: consistent with declared complexity
  (parameters `128..512`, final hash `0x6b2ee9ab30297af7`).
- `Hex.PolyBench.runPrimitivePartChecksum`: consistent with declared
  complexity (`β=+0.001`, parameters `8192..131072`, final hash
  `0x6723bfbfb8236996`).
- `Hex.PolyBench.runGcdChecksum`: consistent with declared complexity
  (`β=-0.101`, parameters `16..96`, final hash `0x1b1bcaf06d8ce2c1`).
- `Hex.PolyBench.runXGcdChecksum`: consistent with declared complexity
  (`β=-0.078`, parameters `16..96`, final hash `0xd7c3a48ff94871b3`).
- `Hex.PolyBench.runDerivativeChecksum`: consistent with declared complexity
  (`β=-0.016`, parameters `8192..131072`, final hash
  `0x136784a3e32917c5`).
- `Hex.PolyBench.runSubChecksum`: consistent with declared complexity
  (`β=-0.001`, parameters `8192..131072`, final hash
  `0xb661ce41e16ecdac`).
- `Hex.PolyBench.runComposeChecksum`: consistent with declared complexity
  (parameters `16..64`, final hash `0x22d4cff389f27388`).
- `Hex.PolyBench.runModByMonicChecksum`: consistent with declared complexity
  (`β=-0.048`, parameters `64..512`, final hash `0xe292fd87a14a5ba4`).
- `Hex.PolyBench.runModChecksum`: consistent with declared complexity
  (`β=-0.057`, parameters `64..512`, final hash `0x9829367400164008`).
- `Hex.PolyBench.runMulChecksum`: consistent with declared complexity
  (parameters `128..512`, final hash `0xd634bb91fcd2a52d`).
- `Hex.PolyBench.runDivModChecksum`: consistent with declared complexity
  (`β=-0.057`, parameters `64..512`, final hash `0x9afda056859428e`).

Smoke wiring was also checked with:

```sh
lake exe hexpoly_bench list
lake exe hexpoly_bench verify
```

`verify` passed all 15 registered benchmarks at the same commit.

## Comparator Ratios

`SPEC/Libraries/hex-poly.md` names FLINT `fmpz_poly` via `python-flint` as an
`informational` comparator for integer-polynomial inputs. The comparator is
wired through the shared persistent-subprocess driver
`scripts/oracle/flint_bench_driver.py` and registered as fixed representative
pairs for each integer-input HexPoly target. Pairwise hashes agree for every
row below.

The comparator process-call overhead is about `56-65 ms` per fixed call on this
host. That dominates the small linear rows and is shown directly in the raw
medians; because this comparator is informational, no gating-goal verdict is
computed. The full parametric Hex ladders for integer targets were densified in
`HexPoly/Bench.lean` to `8192,12288,16384,24576,32768,49152,65536,98304,131072`
for linear targets, `128,160,192,224,256,320,384,448,512` for multiplication,
and `16,20,24,28,32,40,48,56,64` for composition. A larger fixed comparator
matrix was not kept because this version of the bench registry overflows while
listing/verifying that many fixed IO registrations; the committed fixed surface
therefore records one representative case per integer-input target.

Command:

```sh
lake exe hexpoly_bench compare \
    Hex.PolyBench.runFixedAddChecksum8192 \
    Hex.PolyBench.runFixedFlintAddChecksum8192 \
    Hex.PolyBench.runFixedSubChecksum8192 \
    Hex.PolyBench.runFixedFlintSubChecksum8192 \
    Hex.PolyBench.runFixedMulChecksum512 \
    Hex.PolyBench.runFixedFlintMulChecksum512 \
    Hex.PolyBench.runFixedComposeChecksum64 \
    Hex.PolyBench.runFixedFlintComposeChecksum64 \
    Hex.PolyBench.runFixedDerivativeChecksum8192 \
    Hex.PolyBench.runFixedFlintDerivativeChecksum8192 \
    Hex.PolyBench.runFixedContent8192 \
    Hex.PolyBench.runFixedFlintContent8192 \
    Hex.PolyBench.runFixedPrimitivePartChecksum8192 \
    Hex.PolyBench.runFixedFlintPrimitivePartChecksum8192 \
    --export-file reports/bench-results/hex-poly-flint-fixed-7771fa9c.json
```

Export artefact:
`reports/bench-results/hex-poly-flint-fixed-7771fa9c.json`.

| Pair | n | Hex median | FLINT median | raw ratio |
|---|---:|---:|---:|---:|
| addition | 8192 | 1.004 ms | 64.549 ms | 64.3x |
| subtraction | 8192 | 1.042 ms | 62.958 ms | 60.4x |
| multiplication | 512 | 3.740 ms | 56.519 ms | 15.1x |
| composition | 64 | 1.692 s | 411.914 ms | 0.243x |
| derivative | 8192 | 651.583 us | 61.885 ms | 95.0x |
| content | 8192 | 1.518 ms | 59.488 ms | 39.2x |
| primitive part | 8192 | 1.850 ms | 63.974 ms | 34.6x |

Trend: the small linear fixed rows mostly measure the persistent subprocess and
JSON boundary, so FLINT appears slower despite matching results. The
multiplication row is still process-overhead dominated but narrows the gap. The
composition row is large enough for algorithmic work to dominate and FLINT is
about `4.1x` faster (`0.243x` FLINT/Hex), matching the expected structural
advantage of FLINT's tuned integer-polynomial kernels. These rows are
orientation data only, not a Phase-4 gate.

## Profile

Profiles were recorded with `samply record --save-only` at the same commit on
`carica` (Apple M2 Ultra, macOS 14.6.1), at the default 1 kHz sampling rate.
The raw Firefox Profiler JSON artefacts are developer-local and are not
committed.

### `dense-int-arithmetic`

Command:

```sh
samply record --save-only -o reports/bench-results/profiles/hex-poly-dense-int-arithmetic-f5bfa6409349.json -- lake exe hexpoly_bench run Hex.PolyBench.runComposeChecksum
```

Representative case: deterministic same-size dense integer composition,
parameters `16..64`, no seed. Leaf cost was allocation/free 55.0%, other
system 20.4%, GMP 15.5%, Lean runtime/harness 6.5%, own HexPoly code 2.7%.
Inclusive HexPoly cost was led by
`Hex.PolyBench.runComposeChecksum` (86.1%), `DensePoly.compose`'s fold
(84.3%), `DensePoly.mul` (83.9%), and the nested multiplication fold (79.4%).
The dominant allocation and GMP leaves occur under the registered dense
composition/multiplication target.

### `field-euclidean`

Command:

```sh
samply record --save-only -o reports/bench-results/profiles/hex-poly-field-euclidean-f5bfa6409349.json -- lake exe hexpoly_bench run Hex.PolyBench.runDivModChecksum
```

Representative case: deterministic fixed-size `F7` division inputs,
parameters `64..512`, no seed. Leaf cost was own HexPoly code 27.9%, Lean
runtime/harness 23.6%, allocation/free 13.4%, and other system 35.1%.
Inclusive HexPoly cost was led by `DensePoly.divMod` and
`Hex.PolyBench.runDivModChecksum` (both 71.5%), followed by
`DensePoly.divModArray` (69.7%) and `DensePoly.divModArrayAux` entries
(27.6%, 22.3%, 14.2%). The dominant work maps to the registered division and
remainder targets.

### `integer-content`

Command:

```sh
samply record --save-only -o reports/bench-results/profiles/hex-poly-integer-content-f5bfa6409349.json -- lake exe hexpoly_bench run Hex.PolyBench.runPrimitivePartChecksum
```

Representative case: deterministic dense integer polynomials with nontrivial
content, parameters `8192..131072`, no seed. Leaf cost was allocation/free
44.8%, other system 23.2%, GMP 13.1%, Lean runtime/harness 12.8%, and own
HexPoly code 6.0%. Inclusive HexPoly cost was led by
`DensePoly.primitivePart` (54.7%) and the `contentNat` fold (52.6%). The GMP
and allocation leaves are expected for integer gcd/content normalization and
are attributable to the registered content and primitive-part targets.

### `polynomial-crt`

Command:

```sh
samply record --save-only -o reports/bench-results/profiles/hex-poly-polynomial-crt-f5bfa6409349.json -- lake exe hexpoly_bench run Hex.PolyBench.runPolyCRTChecksum
```

Representative case: deterministic coprime monic rational-polynomial moduli,
parameters `128..512`, no seed. Leaf cost was allocation/free 51.3%, other
system 22.8%, GMP 17.1%, Lean runtime/harness 7.4%, and own HexPoly code
1.4%. Inclusive HexPoly cost was led by `Hex.PolyBench.runPolyCRTChecksum`
(75.3%), `DensePoly.mul` under `DensePoly.polyCRT` (75.2%), the nested
multiplication fold (72.9%), and `DensePoly.polyCRT` (37.4%). The dominant
allocation and GMP leaves are attributable to the registered CRT witness
construction target.

## Concerns
