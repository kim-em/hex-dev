# HexPolyFp Performance Report

This report records partial HexPolyFp Phase-4 evidence from clean source
revision `9aee6e90e1ea76432e24562c9f0de3502b25eda7`, measured on 2026-08-31 on
`chungus2` (AMD EPYC 9455, Linux x86-64) with Lean 4.34.0-rc2 and lean-bench
0.1.0. The repaired Frobenius and GCD ladders pass, but the library remains at
Phase 3 because the concerns at the end of this report still block Phase 4.

The scientific artifact is
[`hex-poly-fp-9aee6e9-scientific.json`](bench-results/hex-poly-fp-9aee6e9-scientific.json)
(SHA-256 `8d5835bdab5063b84c78b6ff9c9cef81cb715b700507d9b02335f1df0792ae9e`).
It was produced with the committed scientific settings:

```sh
.lake/build/bin/hexpolyfp_bench run \
  Hex.FpPolyBench.runFrobeniusXModChecksum \
  Hex.FpPolyBench.runGcdChecksum \
  Hex.FpPolyBench.runWeightedProductChecksum \
  Hex.FpPolyBench.runSquareFreeDecompositionSummary \
  Hex.FpPolyBench.runFrobeniusXPowModChecksum \
  Hex.FpPolyBench.runPowModMonicChecksum \
  Hex.FpPolyBench.runDivModChecksum \
  Hex.FpPolyBench.runComposeModMonicChecksum \
  --export-file reports/bench-results/hex-poly-fp-9aee6e9-scientific.json
```

`lake exe hexpolyfp_bench verify` passed all 27 registrations.

Three fresh within-Lean crossover comparisons were run at clean source
revision `b439978767e42783c500e464ec38ed17b497ac8c` with three outer trials per
rung. Their machine-readable records are:

- [`hex-poly-fp-b439978-pow-compare.json`](bench-results/hex-poly-fp-b439978-pow-compare.json),
  SHA-256 `9e76761ca2e839d3c064603c15b7e10176e5c72ef9e34fc668a12843d48983b6`;
- [`hex-poly-fp-b439978-frobenius-compare.json`](bench-results/hex-poly-fp-b439978-frobenius-compare.json),
  SHA-256 `d5bb0b21664d84745f22f017ba87aad9b2618bccda9bf0641623a5c0c272a9b1`;
- [`hex-poly-fp-b439978-compose-compare.json`](bench-results/hex-poly-fp-b439978-compose-compare.json),
  SHA-256 `0ea5156135080fc09a3a2db98b3e98c92181b5e3422bee5aef2457d0a1a3096b`.

They were produced by pairing
`runPowModMonicChecksum`/`runFastPowChecksum`,
`runFrobeniusXModChecksum`/`runFastFrobeniusChecksum`, and
`runComposeModMonicChecksum`/`runFastComposeChecksum` with
`compare --outer-trials 3 --signal-floor-multiplier 1 --export-file FILE`.
Each record has `git_dirty: false`, names the full source revision, and reports
agreement on every common parameter.

## Bench Targets

These formulas are copied from the adjacent `setup_benchmark` registrations
in `bench/HexPolyFp/Bench.lean`.

| Target | Declared complexity |
|---|---|
| `runMulSchoolbook257Checksum` | `(n * n)` |
| `runMulPacked257Checksum` | `(n * n)` |
| `runMulKaratsuba257Checksum` | `(n * Nat.sqrt n)` |
| `runMulDirectNtt257Checksum` | `(n * Nat.log2 (n + 1))` |
| `runMulCrtNtt257Checksum` | `(n * Nat.log2 (n + 1))` |
| `runMulFast257Checksum` | `(n * n)` |
| `runMulSchoolbookChecksum` | `(n * n)` |
| `runMulPackedChecksum` | `(n * n)` |
| `runMulKaratsubaChecksum` | `(n * Nat.sqrt n)` |
| `runMulDirectNttChecksum` | `(n * Nat.log2 (n + 1))` |
| `runMulDirectNttColdChecksum` | `(n * Nat.log2 (n + 1))` |
| `runMulCrtNttChecksum` | `(n * Nat.log2 (n + 1))` |
| `runMulFastChecksum` | `(n * n)` |
| `runPowModMonicChecksum` | `n * n * Nat.log2 (n + 1)` |
| `runFastPowChecksum` | `(n * n * Nat.log2 (n + 1))` |
| `runFrobeniusXModChecksum` | `frobeniusWork n` |
| `runFastFrobeniusChecksum` | `frobeniusWork n` |
| `runFrobeniusXPowModChecksum` | `n * n * n` |
| `runFastFrobeniusPowChecksum` | `(n * n * n)` |
| `runComposeModMonicChecksum` | `n * n * n` |
| `runFastComposeChecksum` | `(n * n * n)` |
| `runWeightedProductChecksum` | `n * n` |
| `runSquareFreeDecompositionSummary` | `n * n` |
| `runDivModChecksum` | `n * n` |
| `runDivModFastChecksum` | `(n * n)` |
| `runGcdChecksum` | `n * n` |
| `runGcdFastChecksum` | `(n * n)` |

The table contains 27 parametric registrations. The eight registrations in
the verdict table below have current scientific mode-1 results. The other 19
are forced-kernel, dispatcher, or fast-candidate crossover registrations, but
their control role does not exempt parametric registrations from the Phase-4
ordered-mode and scientific-verdict requirements. They remain open work.

For the fixed-prime Frobenius family, the independently derived model is

`frobeniusWork n = n * sum_{k=0}^{16} min(n, 2^k)^2`.

The exponent `65537 = 2^16 + 1` fixes the 17 squaring stages. Before reduction
saturates, the active degree doubles; afterward it remains at the modulus
degree. Schoolbook multiplication and monic reduction are quadratic in that
active degree, and the target performs `n` calls.

For GCD, the prepared pair consists of consecutive polynomial Fibonacci
values defined by `F₀ = 0`, `F₁ = 1`, and `Fₖ₊₂ = X Fₖ₊₁ + Fₖ`. The Euclidean
chain has exactly `n` degree-one quotient steps. Each remainder-only division
scans a polynomial of the current degree, so the decreasing-degree costs sum
to `Theta(n^2)`. Neither model was inferred from the measured wall times.

The earlier committed
[`hex-poly-fp-f1ab9696-gcd-hensel-chungus2.json`](bench-results/hex-poly-fp-f1ab9696-gcd-hensel-chungus2.json)
(SHA-256 `fcb72f342a3edb09cce09214101182765b9037e4ba12f46ea14e32360e8265c3`)
recorded the then-current GCD fixture growing nearly linearly from 2.937 µs at
`n = 16` to 43.570 µs at `n = 256`, so that family did not force the declared
quadratic chain. It predates the subsequently introduced dense hash-mixed
fixture, for which no scientific export was committed. The replacement is
therefore justified by the exact polynomial-Fibonacci remainder recurrence,
not by fitting either prior timing series. For fixed-prime Frobenius, the old
`n^3` proxy incorrectly treated the number of reduction-saturated squaring
stages as constant; the exact 17-stage active-degree sum corrects that
structural mismatch.

## Verdicts

The eight operation-level registrations measured below pass **mode 1,
two-sided parametric**, the first and strongest applicable mode. Their
expected scaling is derived from the registered family before measurement, so
neither mode 2 nor mode 3 is needed for these eight. This table is not a
verdict for the other 19 parametric registrations and does not assert Phase-4
completion.

`C` is per-call time divided by the declared model over the verdict window.
The final column is the observed hash at the largest rung.

| Target | Harness verdict | C min | C max | beta | Largest rung | Median | Hash |
|---|---|---:|---:|---:|---:|---:|---|
| `runFrobeniusXModChecksum` | consistent with declared complexity | 51.554 | 59.158 | -0.105 | 80 | 286.481 ms | `0xac1417f1a37c7f40` |
| `runGcdChecksum` | consistent with declared complexity | 5.647 | 10.561 | -0.102 | 2048 | 24.282 ms | `0xfcd34e69b617ac7d` |
| `runWeightedProductChecksum` | consistent with declared complexity | 38.007 | 39.487 | -0.003 | 4096 | 662.479 ms | `0x972bd3a6f2b6d429` |
| `runSquareFreeDecompositionSummary` | consistent with declared complexity | 8.774 | 26.295 | -0.227 | 768 | 6.304 ms | `0x66ff822aca96ce87` |
| `runFrobeniusXPowModChecksum` | consistent with declared complexity | 1244.558 | 1657.772 | narrow-window | 64 | 326.254 ms | `0x6b9763a45f6b5d11` |
| `runPowModMonicChecksum` | consistent with declared complexity | 60.101 | 77.450 | -0.115 | 512 | 141.796 ms | `0x3f65c86be5e72dd5` |
| `runDivModChecksum` | consistent with declared complexity | 14.323 | 22.769 | -0.070 | 2048 | 63.261 ms | `0x5e661a9702ea0fc1` |
| `runComposeModMonicChecksum` | consistent with declared complexity | 35.615 | 39.439 | -0.071 | 192 | 252.081 ms | `0xee8f3ebaae233227` |

No ladder was truncated by its wall-clock cap. The Frobenius model passes on
the committed 16-through-80 schedule; the forced Euclidean family passes on
the full 8-through-2048 schedule.

## Comparator Ratios

HexPolyFp has no per-library external-comparator declaration in its SPEC or in
`libraries.yml`, so no external ratio can yet be reported. This is a Phase-4
blocker rather than a not-applicable result: FLINT `nmod_poly` exposes direct
counterparts for multiplication, division/remainder, GCD, modular power, and
modular composition. The comparator still needs a scoped classification,
wiring, overhead treatment, and measured ratios.

The three refreshed within-Lean comparisons all reported agreement on every
common parameter. Representative largest-rung medians are:

| Pair | Parameter | Schoolbook | Fast candidate | Schoolbook / fast | Agreement |
|---|---:|---:|---:|---:|---|
| modular power | 512 | 147.724 ms | 72.513 ms | 2.037 | all agreed |
| batched Frobenius | 80 | 291.952 ms | 166.828 ms | 1.750 | all agreed |
| modular composition | 192 | 249.535 ms | 189.995 ms | 1.313 | all agreed |

The remaining within-Lean implementation pairs have source-level equality
guarantees, including `FpPoly.mulFast_eq`, `DensePoly.divModWith_eq`, and
`DensePoly.gcdWith_eq`; the fast power and Horner loops reduce pointwise to
`mulFast_eq`. These proofs establish semantic equality, but do not substitute
for the missing scientific verdicts or required `compare` runs.

## Profile

One representative case from each declared `phase4.input_families` family was
sampled from the clean source revision above. The commands used the project
wrapper with `samply 0.13.1` at 999 Hz and `lean-bench-samply` commit
`9356baa2f5757ee40320a897bd284914d5bb9f5e`:

```sh
scripts/profile/run_profile.sh .lake/build/bin/hexpolyfp_bench \
  Hex.FpPolyBench.runMulFastChecksum 16384 2000000000
scripts/profile/run_profile.sh .lake/build/bin/hexpolyfp_bench \
  Hex.FpPolyBench.runFrobeniusXModChecksum 80 5000000000
scripts/profile/run_profile.sh .lake/build/bin/hexpolyfp_bench \
  Hex.FpPolyBench.runComposeModMonicChecksum 192 2000000000
scripts/profile/run_profile.sh .lake/build/bin/hexpolyfp_bench \
  Hex.FpPolyBench.runSquareFreeDecompositionSummary 768 2000000000
scripts/profile/run_profile.sh .lake/build/bin/hexpolyfp_bench \
  Hex.FpPolyBench.runGcdChecksum 2048 5000000000
```

The deterministic fixtures use no random seed. Raw filtered Firefox Profiler
artifacts remain developer-local at `/tmp/hex-profile-<target>-<param>.json.gz`,
as required by `SPEC/profiling.md`. The postprocessor retained only bench-thread
samples inside timed regions. Every run had zero other-thread samples in its
timed windows and passed calibration, minimum-sample, and plus-or-minus 5 ms
sensitivity checks.

| Family / target | Samples | Timed | Residual | Own code | GMP | Allocation | Lean runtime | Other | Classified |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| coefficient-kernels / `runMulFastChecksum`, n=16384 | 1316 | 1326.7 ms | 0.695 ms | 22.72% | 11.55% | 30.09% | 30.02% | 5.62% | 94.38% |
| quotient-powers / `runFrobeniusXModChecksum`, n=80 | 5139 | 5165.0 ms | 0.433 ms | 35.18% | 0% | 26.60% | 35.55% | 2.67% | 97.33% |
| modular-composition / `runComposeModMonicChecksum`, n=192 | 2216 | 2254.9 ms | 0.995 ms | 34.34% | 0% | 29.20% | 32.45% | 4.02% | 95.98% |
| product-squarefree / `runSquareFreeDecompositionSummary`, n=768 | 1615 | 1627.4 ms | 0.926 ms | 35.60% | 0% | 27.00% | 30.53% | 6.87% | 93.13% |
| euclidean-division-gcd / `runGcdChecksum`, n=2048 | 3065 | 3086.4 ms | 0.736 ms | 42.25% | 0% | 28.78% | 24.67% | 4.31% | 95.69% |

The coefficient-kernel profile places 75.30% of samples inclusively in
`FpPoly.mulNttCrt?`; CRT image convolution accounts for 60.71%, and the NTT
forward path for 25.15%. These costs are covered by the forced NTT/CRT and
public-dispatch registrations.

The Frobenius profile places 99.90% in `FpPoly.powModMonicAux`, with
`DensePoly.mulImpl` at 55.71% and monic reduction/division at 44.09%/43.98%.
This is precisely the multiplication-and-reduction work represented by
`frobeniusWork` and registered by the quotient-power targets.

The composition profile places 64.08% in monic reduction and 35.65% in dense
multiplication beneath the registered Horner composition target. The
product/square-free profile places 99.32% in `squareFreeDecomposition`, 95.23%
in `yunFactorsWithLevel`, and 51.64% in `monicGcd`; its dominant GCD and exact
division phases are covered by the square-free, GCD, and division targets.

The forced-chain GCD profile places 100% in `DensePoly.gcdAuxImpl` and
99.74% in `DensePoly.modImpl`, with `subtractScaledShiftStep` inclusive in
95.07% of samples. The dominant cost is therefore the registered Euclidean
remainder chain, not fixture preparation or an unregistered phase.

## Concerns

- Nineteen parametric forced-kernel, dispatcher, and fast-candidate
  registrations still lack complete ordered-mode rationales and scientific
  verdicts. Several declarations are explicitly conservative upper bounds and
  therefore need the required mode-2 citation and dominant-phase rationale or
  a different registration mode. In the fresh comparison,
  `runFastFrobeniusChecksum` was inconclusive against `frobeniusWork`
  (`beta = -0.330`, faster than declared), even though all result hashes
  agreed.
- The HexPolyFp SPEC and `libraries.yml` still lack the required scoped FLINT
  comparator declaration, registration, and measured ratios. The existing
  python-flint conformance oracle demonstrates that comparable `nmod_poly`
  surfaces exist, so an absence declaration would not be accurate.
- The polynomial-Fibonacci GCD result is `1` at every rung, so the current
  result hash is parameter-independent. The exact fixture recurrence and
  paired equality proof protect correctness, but a future registration audit
  should mix an input checksum into both GCD targets before their compare
  evidence is considered complete.
