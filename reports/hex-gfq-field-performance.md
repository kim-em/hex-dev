# HexGFqField Performance Report

## Bench Targets

- `Hex.GFqFieldBench.runOfPolyReprChecksum`: `n * n`
- `Hex.GFqFieldBench.runAddChecksum`: `n`
- `Hex.GFqFieldBench.runMulChecksum`: `n * n`
- `Hex.GFqFieldBench.runNegSubChecksum`: `n`
- `Hex.GFqFieldBench.runPowChecksum`: `n * n * Nat.log2 (n + 1)`
- `Hex.GFqFieldBench.runInvDivChecksum`: `n * n`
- `Hex.GFqFieldBench.runZPowChecksum`: `n * n * Nat.log2 (n + 1)`
- `Hex.GFqFieldBench.runFrobChecksum`: `n * n * Nat.log2 7`

## Verdicts

All eight parametric performance registrations use **mode 1, two-sided
parametric**. Their adjacent derivations determine the expected family scaling
before measurement:
coefficientwise addition is linear, dense multiplication/reduction and
extended gcd are quadratic, and exponentiation repeats quadratic
multiplication logarithmically. The scientific schedule is
`#[2, 432, 600, 768, 936, 1216]`: degree 2 retains a smoke point, while the
five-point verdict tail spans more than a factor of `e`. Every tail degree is
`40 mod 56`, so the deterministic dense operands have the same coefficient
pattern over `F_7`; only their degree changes. The sparse modulus exponents are
`(n,k) = (432,54), (600,75), (768,96), (936,324), (1216,144)`. The differing
middle exponent at degree 936 produces a visible but verdict-safe constant
bump (most clearly `69.209` versus `48.905..58.851` for inversion/division),
so the evidence does not claim the moduli themselves have a uniform shape.

The high-degree sparse trinomials are checked by `Berlekamp.rabinTest` during
compiled benchmark preparation, and the proven implication from that check
supplies each field's irreducibility witness. Ordinary elaboration still
contains only the static degree-2-through-8 certificates. Thus `verify`, which
uses parameters 0 and 1, does not generate or elaborate the scientific
fixtures. The scientific registrations use three outer trials, warm-cache
medians, a 120-second per-call cap, and the same schedule for all eight models.

The 96 fixed registrations are comparator endpoints and canonical
expected-hash checks. They make no complexity claim, have no mode, and do not
replace the eight performance registrations.

The declared input families are `dense-canonical-reduction`,
`field-arithmetic`, `field-exponentiation`, and `field-inversion-division`.

The clean scientific run at commit
`97ff768e53567c607c2afb8942295314c35ed3b9` on `chungus2` (AMD EPYC 9455,
Linux x86-64, Lean 4.34.0-rc2) used two direct harness invocations:

```sh
lake exe hexgfqfield_bench run \
  Hex.GFqFieldBench.runOfPolyReprChecksum \
  Hex.GFqFieldBench.runNegSubChecksum \
  Hex.GFqFieldBench.runPowChecksum \
  Hex.GFqFieldBench.runInvDivChecksum \
  Hex.GFqFieldBench.runFrobChecksum \
  --export-file reports/bench-results/hex-gfq-field-scientific-core-9740.json

lake exe hexgfqfield_bench run \
  Hex.GFqFieldBench.runAddChecksum \
  Hex.GFqFieldBench.runMulChecksum \
  Hex.GFqFieldBench.runZPowChecksum \
  --export-file reports/bench-results/hex-gfq-field-scientific-holdouts-9740.json
```

The artefacts are unmodified exports from those commands. Their SHA-256 sums
are respectively
`2335f01b8c0d3b77adf858ce42eb836d56df2a1764ec75caef649bd93d34807f`
and
`9d047aa1c878e44e117a8a325fe945378545a8201d164423f165ed8db11f62bb`.
Both top-level and per-result environments record the full commit above and
`git_dirty=false`. Splitting the registrations limits sustained host drift;
each verdict is produced directly by the harness, with no row combination or
post-processing. The commands took approximately 15 and 9 minutes respectively;
runtime Rabin checking is preparation cost and is excluded from timed rows.

| Registration | Model | `cMin` | `cMax` | slope | degree-1216 hash |
|---|---:|---:|---:|---:|---:|
| `runOfPolyReprChecksum` | `n * n` | 14.969 | 17.601 | +0.117 | `0x7d4ede102dccc098` |
| `runAddChecksum` | `n` | 15.201 | 16.378 | +0.053 | `0x7104d75758a05e8b` |
| `runMulChecksum` | `n * n` | 18.534 | 20.124 | +0.015 | `0xce29294f4da9426b` |
| `runNegSubChecksum` | `n` | 65.493 | 69.065 | +0.047 | `0xe4ecaaefaae0627e` |
| `runPowChecksum` | `n * n * Nat.log2 (n + 1)` | 40.441 | 41.488 | -0.026 | `0x330820cab12539dd` |
| `runInvDivChecksum` | `n * n` | 48.905 | 69.209 | -0.037 | `0x7845bac0524b037c` |
| `runZPowChecksum` | `n * n * Nat.log2 (n + 1)` | 49.974 | 52.785 | -0.054 | `0x4619a8eb8cf05b54` |
| `runFrobChecksum` | `n * n * Nat.log2 7` | 46.266 | 47.960 | -0.003 | `0x736ff013e830511` |

Every registration is **consistent with declared complexity** under the
mode-1 two-sided rule, so the Phase-4 gate passes. The informational FLINT
comparator remains declared in `libraries.yml`, wired in
`HexGFqField/Bench.lean`, and covered by this report's comparator section.

Smoke wiring was checked with:

```sh
lake exe hexgfqfield_bench verify
```

All 104 registrations passed at commit
`fb1e5bed38960fd1ce941a2d94986439c7d61705` on `chungus2`, using
python-flint 0.9.0 for the external fixed targets.

## Comparator Ratios

`FLINT fq_default via python-flint` is wired as an `informational`
comparator through the shared python-flint persistent-subprocess driver
`scripts/oracle/flint_bench_driver.py`. The clean 96-registration export at
commit `d75e69edf2a67d31d9503c1a66ce611d17d4a767` is
`reports/bench-results/hex-gfq-field-comparators-9740.json` (SHA-256
`66128f94c50662c7c9ff11a83c8dd33fd0852e8e56ae0cd33f1bfa017412e419`).
It records five warm-cache repeats for every Lean/FLINT endpoint, 480
successful samples, agreeing hashes, and `git_dirty=false`. Mutable runtime
anchors keep the Lean fixed inputs from being folded during compilation;
FLINT's warmup starts the persistent driver before measurement, and each
measured inner-repeat batch reuses it.

A fresh probe on the same host and python-flint 0.9.0 environment sent 20
warmup and 200 measured trivial `fq_default.reduce` requests through one
persistent driver. It measured 12.689 us median JSON request/reply overhead
(12.068 us minimum, 18.938 us maximum). The adjusted ratio below subtracts
that median once from the FLINT time. Since framing is roughly half of many
degree-8 FLINT medians, both raw and adjusted values are reported and neither
is used as a gate.

| Target (`n = 8`) | Hex median | FLINT median | Raw FLINT/Hex | Adjusted FLINT/Hex |
| --- | ---: | ---: | ---: | ---: |
| dense canonical reduction | 2.698 us | 23.005 us | 8.53x | 3.82x |
| addition | 0.301 us | 23.442 us | 77.88x | 35.72x |
| multiplication | 3.570 us | 25.421 us | 7.12x | 3.57x |
| negation/subtraction | 0.678 us | 46.655 us | 68.81x | 50.10x |
| natural exponentiation | 27.840 us | 22.925 us | 0.82x | 0.37x |
| inversion/division | 23.080 us | 47.442 us | 2.06x | 1.51x |
| signed exponentiation | 37.927 us | 23.293 us | 0.61x | 0.28x |
| Frobenius | 19.982 us | 23.305 us | 1.17x | 0.53x |

The full degree-2, 3, 4, 5, 6, and 8 ladder is retained in the export. FLINT's
finite-field context changes representation across these small moduli, so the
ratios are not monotone and this report does not infer a scaling trend from
them. Ratios below one mean Hex took longer. The comparator remains
informational and has no gating-goal verdict.

## Profile

Profiles were recorded with `scripts/profile/run_profile.sh` at clean commit
`2d95961b79bad5e6cec0509a5d61fae673f4e763` on `chungus2` (AMD EPYC
9455, Linux x86-64) with `samply 0.13.1` at 999 Hz and
`lean-bench-samply` commit `9356baa2f5757ee40320a897bd284914d5bb9f5e`.
The binary reported LeanBench 0.1.0 and Lean 4.34.0-rc2. Each command used
parameter 1216, the scientific tail rather than the old certificate-limited
degree-8 regime:

```sh
for target in runOfPolyReprChecksum runMulChecksum runZPowChecksum \
    runInvDivChecksum; do
  scripts/profile/run_profile.sh ./.lake/build/bin/hexgfqfield_bench \
    "Hex.GFqFieldBench.${target}" 1216 1000000000
done
```

The raw filtered Firefox Profiler JSON artefacts remain developer-local under
`/tmp/hex-profile-*-1216.json.gz`. The postprocessor retained only bench-thread
samples inside LeanBench timed regions, excluding fixture preparation,
autotuner gaps, hashing, and process exit. All four profiles had zero
other-thread samples in their timed windows and passed calibration,
minimum-sample, and ±5 ms sensitivity checks.

| Target | Samples | Timed | Calibration residual | Hex code | Lean runtime | Allocation | Other |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| dense canonical reduction | 848 | 848.6 ms | 0.459 ms | 42.0% | 38.6% | 12.6% | 6.8% |
| multiplication | 987 | 988.3 ms | 0.726 ms | 30.0% | 33.0% | 32.2% | 4.8% |
| signed exponentiation | 756 | 757.7 ms | 0.577 ms | 30.0% | 30.2% | 34.1% | 5.7% |
| inversion/division | 680 | 680.6 ms | 0.652 ms | 31.6% | 36.8% | 28.5% | 3.1% |

For dense canonical reduction, `GFqRing.reduceMod`, `DensePoly.divMod`, and
`DensePoly.divModArray` were inclusive in 100% of samples, with
`DensePoly.subtractScaledShiftStep` at 93.2%. Multiplication spent 89.5% of
samples in quotient reduction after `GFqRing.mul`; the packed polynomial
multiplication path appeared at 9.0%. These profiles support the quadratic
dense multiplication/reduction model at the actual scientific scale.

Signed exponentiation spent 81.4% inclusively in `GFqField.zpow` and
`GFqRing.pow.go`, 73.5% in quotient reduction, and 18.3% in the
negative-exponent inversion path. Inversion/division spent 61.6% in
`GFqField.inv`, `GFqField.invPoly`, and `DensePoly.xgcd`, while
`GFqField.div` accounted for 31.2%. The observed call paths are the operations
named by the `n² · log n` and `n²` registrations; the profiles are
corroborating attribution evidence, not a second scaling verdict.

## Concerns

None. All eight mode-1 registrations pass on the clean scientific schedule,
and the runtime checks make rejected high-degree modulus fixtures visible.
