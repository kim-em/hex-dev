# HexIntFactor performance

## Scope and acceptance

This is the Phase-4 headline report for `HexIntFactor`. It covers all five
input families declared in `libraries.yml`: `table-and-balanced-semiprimes`,
`smooth-and-unbalanced-semiprimes`, `power-forms`,
`certificate-replay-and-order`, and `generalized-divisor-sums`.

The compiled track has 19 parametric targets and four fixed policy targets.
Nine parametric targets satisfy their tight mode-1 models; ten intentionally
use conservative mode-2 upper bounds. All fixed targets are mode 3 and have
agreeing hashes. The `HexIntFactorMathlib` audit classifies that library as a
`correspondence-only-layer`; it owns no separate computational benchmark or
comparator, and names `HexIntFactor` as its computational performance owner.

## Bench targets

| Evidence family | Targets | Track |
|---|---|---|
| `table-and-balanced-semiprimes` | `runTableBatch`, `runBalancedFactor`, `runBalancedRho` | fixed table policy; parametric factor/rho |
| `smooth-and-unbalanced-semiprimes` | `runPMinusOneWord`, `runPMinusOneNat`, `runEcmWord`, `runEcmNat`, `runEcmRhoWord`, `runEcmRhoNat` | parametric route and paired policy comparisons |
| `power-forms` | `runCyclotomic`, `runPowerGeneric`, `runPowerSplit` | parametric structural and paired policy comparison |
| `certificate-replay-and-order` | `runReplay`, `runReplayWidth`, `runOrder`, `runPrimitiveRoot`, `runDownstreamOrder`, `runDownstreamPrimitiveRoot` | parametric scan/replay plus fixed downstream operands |
| `generalized-divisor-sums` | `runSigmaExponent`, `runSigmaFactorCount`, `runSquareFactorCount`, `runTotientFactorCount` | parametric certified inputs |
| cross-family policy | `runDefaultFuelSchedule` | fixed exact public schedule |

`runReplay` grows the exponent of one certified prime power; `runReplayWidth`
grows the number of certified entries. Preparation for the divisor-function
targets constructs or selects checked data outside the timed region. The ECM
registrations are split at the `UInt64`/direct-`Nat` backend boundary. Every
registration's adjacent source comment derives its declared model.

## Verdicts

The clean scientific artifact is
`reports/bench-results/hex-int-factor-phase4-703d2f42-chungus2-cpu2.json`
(SHA-256 `2ae86f6a5c348a6605028563ff726520b7b4d530ceac44a5bb9a7b71b841a798`).
It was produced from clean commit
`703d2f4203725857d61092f5342e981a305c1267`; the benchmark executable hash is
`44c53cd33de691b82766ded78e49068b248af8f71b4120b28ff12305d38da620`.

| Target | Domain | Declared model | Mode | Result |
|---|---:|---:|---:|---|
| `runSquareFactorCount` | 32--1024 entries | `n²` | 1 | consistent, slope -0.132 |
| `runReplay` | exponent 1024--262144 | `n²` | 1 | consistent, slope -0.097 |
| `runPMinusOneWord` | 32--64 bits | `n` | 1 | consistent |
| `runBalancedFactor` | 32--80 bits | `2^(n/4)` | 2 | conservative rho upper bound |
| `runReplayWidth` | 1--10 entries | `n²` | 2 | conservative widening-product bound |
| `runPrimitiveRoot` | 257--65537 | `n` | 2 | candidate-count upper bound; observed early success |
| `runPowerSplit` | exponent 12--64 | `2^n` | 2 | input-value upper bound |
| `runCyclotomic` | exponent 4--32 | `n²` | 2 | recursive-prefix upper bound |
| `runEcmNat` | 72--80 bits | `n²` | 1 | consistent |
| `runEcmRhoWord` | 48--64 bits | `1` | 2 | fixed-factor expected-cost bound; seed-dependent spread |
| `runEcmRhoNat` | 72--80 bits | `2^(n/4)` | 2 | worst expected rho upper bound |
| `runBalancedRho` | 32--80 bits | `2^(n/4)` | 2 | worst expected rho upper bound |
| `runPMinusOneNat` | 72--80 bits | `n²` | 1 | consistent |
| `runSigmaFactorCount` | 32--512 entries | `n²` | 1 | consistent, slope -0.013 |
| `runTotientFactorCount` | 32--1024 entries | `n²` | 1 | consistent, slope 0.132 |
| `runPowerGeneric` | exponent 12--64 | `2^n` | 2 | input-value upper bound |
| `runEcmWord` | 48--64 bits | `1` | 1 | consistent |
| `runSigmaExponent` | 16384--4194304 | `n log n` | 1 | consistent, slope 0.159 |
| `runOrder` | 257--65537 | `n` | 1 | consistent, slope -0.005 |
| `runDownstreamOrder` | fixed 50/61-bit primes | fixed | 3 | 0.000021 ms median; hashes agree |
| `runDownstreamPrimitiveRoot` | fixed 50/61-bit primes | fixed | 3 | 1.476 ms median; hashes agree |
| `runTableBatch` | fixed table-range batch | fixed | 3 | 1.667 ms median; hashes agree |
| `runDefaultFuelSchedule` | fixed cross-family schedule | fixed | 3 | 599.261 ms median; hashes agree |

Mode 2 here is a positive manual upper-bound result, not a contrary verdict.
The expected route costs depend on factor shape or deliberately overapproximate
the input value; finite ladders need not make their normalized constants flat.
No target exhibited scaling worse than its declared upper bound.

The exact default-fuel record reports success on all nine cases. The largest
charged count is 34 attempts at the 80-bit balanced input with fuel 352;
the 64-bit balanced case uses 23 of 288. The table-range, smooth, ECM, and two
power-form cases likewise complete within their public default budget.

## Comparator ratios

Both external comparators are informational. PARI 2.17.3 times a calibrated
`factor` batch inside one GP process. GMP-ECM 7.0.6 accepts a calibrated batch
of inputs in one process with `B1=1000` and `sigma=7`; subtracting the median
0.217 ms/input factorization-of-15 protocol floor avoids charging process
startup to the algorithm.

| bits | Hex balanced factor | PARI `factor` | Hex / PARI |
|---:|---:|---:|---:|
| 32 | 0.127 ms | 0.003 ms | 37.07x |
| 40 | 1.430 ms | 0.006 ms | 246.69x |
| 48 | 1.700 ms | 0.062 ms | 27.63x |
| 56 | 11.106 ms | 0.135 ms | 82.41x |
| 64 | 47.116 ms | 0.121 ms | 389.09x |
| 72 | 125.513 ms | 0.184 ms | 683.64x |
| 80 | 534.988 ms | 0.422 ms | 1268.12x |

The widening ratio is consistent with PARI's SQUFOF/tuned portfolio rather
than a rho-parity claim. SQUFOF is not required for the present absolute API
contract: the 80-bit balanced case remains below one second and the public
fuel schedule completes with margin. It would be required for a future
small-constant word-semiprime parity goal.

| bits | Hex ECM | GMP-ECM raw | GMP-ECM adjusted | Hex / adjusted |
|---:|---:|---:|---:|---:|
| 48 | 0.059 ms | 0.498 ms | 0.281 ms | 0.21x |
| 56 | 0.060 ms | 0.261 ms | 0.044 ms | 1.36x |
| 64 | 0.060 ms | 0.362 ms | 0.145 ms | 0.42x |
| 72 | 4.218 ms | 0.348 ms | 0.131 ms | 32.25x |
| 76 | 4.179 ms | 0.407 ms | 0.189 ms | 22.05x |
| 80 | 4.144 ms | 0.410 ms | 0.193 ms | 21.52x |

The direct GMP comparison records the expected tuned-C constant gap above the
word boundary. The internal output-agreeing compare is the route-policy test:
Hex ECM takes 0.060--0.061 ms versus rho's 0.172--0.939 ms at 48--64 bits,
and 4.14--4.20 ms versus 59.0--743.2 ms at 72--80 bits. ECM therefore earns
its maintenance cost in both backends. All common-parameter hashes agree.

The power-form compare also has agreeing hashes at every exponent 12--64.
The split is close to the generic route at the expensive rungs and slightly
slower elsewhere; no factorization failure appears. There is consequently no
measured case for adding Aurifeuillian identities.

## Profile

Five clean, 999 Hz `samply 0.13.1` profiles cover the five declared input
families. They use benchmark commit
`406922122205bee2214d26ab4ee2a93ca6c1bd77`, lean-bench
`fa30c2763cf523f3ac8e46dc3a1dad0845a40098`, and lean-bench-samply
`9356baa2f5757ee40320a897bd284914d5bb9f5e`. Hardware was `chungus2`,
x86-64 Linux 6.12.100 on an AMD EPYC 9455. Raw filtered profiles remain under
`/tmp` and are not committed.

| Family / representative | Leaf-cost split | Inclusive Hex ranking | Diagnostics | Raw SHA-256 |
|---|---|---|---|---|
| `table-and-balanced-semiprimes`: `runBalancedFactor 80` | allocation 67.96%, GMP 25.54%, runtime 4.87%, own 0.04%, other 1.59% | `factorCounted?`, `runFactor`, `factor?` each 93.50% | 4722 samples / 4739.9 ms; residual 0.564 ms; sensitivity passed | `d121506c933dd9ff0d1e859ff0e43a73dfcee07e90cb53b7d0ebcb1b36f6d9ed` |
| `smooth-and-unbalanced-semiprimes`: `runEcmNat 80` | allocation 59.82%, GMP 32.36%, runtime 6.67%, other 1.14% | `runEcm`, `ecmStage1` each 93.81% | 4199 samples / 4238.1 ms; residual 1.500 ms; sensitivity passed | `0e524cbf0adbde2c012805f42ad6e37d662945c1b014b7de73ce021d1ada9ae5` |
| `power-forms`: `runPowerSplit 64` | allocation 23.62%, GMP 0.89%, own 20.64%, runtime 25.67%; identified `lean_nat_log2` 22.73% and upstream `HexPrimality` trial 5.22%; 1.23% other | `removePower` 29.12%, `runPowerSplit` 14.15%, `factorPower?` 13.93%, `factorCounted?` 12.85% | 3159 samples / 3262.6 ms; residual 2.150 ms; sensitivity passed | `9dd73629a5339b2fdc6d203608932c5d14ae2b51edbcf9725e0de3b9e2c8c17e` |
| `certificate-replay-and-order`: `runOrder 65537` | upstream Lean `orderOfAux` 99.70%, allocation 0.18%, GMP 0.02%, runtime 0.06%, other 0.04% | `orderOf` 99.76% | 5039 samples / 5071.9 ms; residual 1.197 ms; sensitivity passed | `36c65e325d4ee795a3dbb85e60019823b099f9cee7f9c4131654f9863f9494e3` |
| `generalized-divisor-sums`: `runSigmaExponent 4194304` | GMP 90.59% including `mpn_mul_fft_internal`, allocation/kernel memory 4.38% including `madvise`, other 5.03% | `sigma` 77.41%, `sigmaEntry` 76.57% | 4537 samples / 4717.4 ms; residual 0.793 ms; sensitivity passed | `3646f194862bdd03ed4ebcd05455e5ef2c672a17249e3b04ae765148b44a2fc4` |

The balanced and direct-`Nat` ECM profiles are dominated by allocation and GMP
division/copy work, matching their widening modular-arithmetic paths. The
power-form profile lands in small-route trial division, `removePower`, and
`Nat.log2`; every dominant phase is represented by the power registrations.
The order profile lands almost entirely in `HexPrimality.Order.orderOfAux`:
that is the upstream implementation deliberately exercised by HexIntFactor's
advertised order surface, not an unmeasured local phase. The sigma profile is
dominated by GMP multiplication, including the FFT regime expected at the
multi-million-bit rung. No profile exposes an unattributed dominant cost.

## Reproduction

Build, wiring, and full scientific collection:

```sh
lake build hexintfactor_bench
.lake/build/bin/hexintfactor_bench list
.lake/build/bin/hexintfactor_bench verify
python3 scripts/bench/intfactor_phase4.py \
  --pari /nix/store/g4sv6kfhwyh176gipz6zc1m35sd2jycf-pari-2.17.3/bin/gp \
  --ecm /nix/store/9cbg4dh5xm3ihbnm0s490vlz1kjx9936-ecm-7.0.6/bin/ecm \
  --output reports/bench-results/hex-int-factor-phase4-703d2f42-chungus2-cpu2.json \
  --cpu 2
python3 scripts/bench/intfactor_phase4.py --report \
  reports/bench-results/hex-int-factor-phase4-703d2f42-chungus2-cpu2.json
```

The collector pins itself and every child to CPU 2, records pre/post pressure,
uses seven median rounds for each external comparator, preserves the full
LeanBench exports for the ECM/rho and power compare groups, and records every
default-fuel result and attempt count.

Profiles used the following template, with the five `(TARGET, PARAM)` pairs
shown in the profile table and `LEAN_BENCH_SAMPLY_HOME` pointing at commit
`9356baa2f5757ee40320a897bd284914d5bb9f5e`:

```sh
LEAN_BENCH_SAMPLY_HOME=/tmp/lean-bench-samply-9634 \
  scripts/profile/run_profile.sh \
  .lake/build/bin/hexintfactor_bench TARGET PARAM 5000000000
python3 scripts/profile/summarize_profile.py \
  /tmp/hex-profile-SHORT-PARAM.json.gz \
  --thread hexintfactor_bench --top 15
```

## Concerns

None.
