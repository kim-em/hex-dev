# HexIntFactor performance

## Scope and acceptance

This is the Phase-4 report for `HexIntFactor`. It covers the five input
families declared in `libraries.yml`: table and balanced semiprimes, smooth and
unbalanced semiprimes, power forms, certificate replay and order, and
generalized divisor sums. The declared comparator is **PARI factor and GMP-ECM**.
It is informational because PARI uses a broader factorization
portfolio and GMP-ECM is an independently tuned C implementation.

The compiled track contains seven parametric and 31 fixed targets. Every
parametric target returned the exact harness verdict
`consistent_with_declared_complexity`. Every fixed target completed all three
repeats and returned `expected_hash_check.status = "match"`. The
`HexIntFactorMathlib` audit classifies it as a `correspondence-only-layer` and
names `HexIntFactor` as its computational performance owner.

## Bench targets

| Family | Targets | Evidence |
|---|---|---|
| table and balanced semiprimes | `runTableDispatch`, `runTableTrial`, `runBalancedFactor{32..80}`, `runBalancedForced{32..80}`, `runBalancedRho` | fixed output-agreeing policy controls plus raw-rho scaling |
| smooth and unbalanced semiprimes | `runPMinusOneBatch`, `runEcmBatch`, `runEcmRhoBatch`, `runEcm{48,56,64,72,76,80}` | fixed whole-family and per-rung route measurements |
| power forms | `runCyclotomicBatch`, `runPowerGenericBatch`, `runPowerSplitBatch` | fixed structural and generic/split measurements |
| certificate replay and order | `runReplay`, kernel `HexIntFactorKernelProbe`, `runOrder`, `runDownstreamOrder`, `runDownstreamPrimitiveRoot` | compiled scaling, kernel replay, and opaque fixed operands |
| generalized divisor sums | `runSigmaExponent`, `runSigmaFactorCount`, `runSquareFactorCount`, `runTotientFactorCount` | prepared certified inputs with explicit models |
| cross-family policy | `runDefaultFuelSchedule` | fixed exact public schedule |

The kernel replay target checks actual `checkFactorization` certificates for
one through ten entries. Its last entry is a 61-bit prime with a committed
Pocklington certificate, so the family reaches the required 64-bit operand
class rather than merely widening a table-prime list.

Fixed-target bodies enforce their absolute ceilings internally, independently
of process startup: table 10 ms; balanced normal and forced 10, 50, 100, 200,
750, 2000, and 6000 ms; p-1 100 ms; ECM batch 100 ms; ECM/rho batch 500 ms;
each per-rung ECM target 20 ms; cyclotomic 10 ms; generic and split power forms
20 ms; downstream order 10 ms; downstream primitive root 20 ms; and the
default-fuel schedule 2000 ms. Opaque `IO.Ref` inputs and no-inline wrappers
prevent closed-term lifting.

## Harness verdicts

The clean artifact is
`reports/bench-results/hex-int-factor-phase4-a30ecb84-chungus2-cpu7.json`
(SHA-256 `222d101a061a9b12d73ea29b52407a92f275588efa023584efe9e299d8201f9f`).
It records clean source commit
`a30ecb84eba72538fbe1e582563ab2ef7d0725f6`, benchmark executable SHA-256
`5336e03e7487fefe3e1f6e948f5bf1810c63750d80d107670c13175606b64b98`,
Lean 4.34.0-rc2, host `chungus2`, and affinity to CPU 7.

| Target | Domain | Declared model | Exact verdict | Slope |
|---|---:|---:|---|---:|
| `runSquareFactorCount` | 32--1024 entries | `n²` | `consistent_with_declared_complexity` | -0.142 |
| `runReplay` | exponent 1024--262144 | `n²` | `consistent_with_declared_complexity` | -0.065 |
| `runBalancedRho` | 32--80 bits | `2^(n/4)` | `consistent_with_declared_complexity` | n/a |
| `runSigmaFactorCount` | 32--1024 entries | `n²` | `consistent_with_declared_complexity` | 0.039 |
| `runTotientFactorCount` | 32--1024 entries | `n²` | `consistent_with_declared_complexity` | 0.101 |
| `runSigmaExponent` | 16384--4194304 | `n log n` | `consistent_with_declared_complexity` | 0.151 |
| `runOrder` | 257--1048589 | `n` | `consistent_with_declared_complexity` | -0.002 |

No parametric run was budget-truncated and no leading rung was dropped from a
verdict. The fixed control medians below are the headline policy evidence.

| bits | normal full pipeline | forced-rho full pipeline | normal / forced | canonical hash agrees |
|---:|---:|---:|---:|:---:|
| 32 | 0.601 ms | 0.634 ms | 0.949x | yes |
| 40 | 6.603 ms | 6.748 ms | 0.979x | yes |
| 48 | 13.735 ms | 13.507 ms | 1.017x | yes |
| 56 | 43.578 ms | 43.396 ms | 1.004x | yes |
| 64 | 192.307 ms | 190.750 ms | 1.008x | yes |
| 72 | 728.078 ms | 746.206 ms | 0.976x | yes |
| 80 | 3148.246 ms | 3106.699 ms | 1.013x | yes |

The paired arms use the same inputs, five fixed seeds, budgets, preprocessing,
recursive completion, prime-certificate construction, and checked acceptance.
All ratios satisfy the preregistered `normal / forced <= 1.25` gate. The table
control also agrees on its canonical hash: public dispatch is 0.039 ms versus
0.032 ms for direct trial division, a 1.202x ratio under its 1.25 gate.

All 47 default-fuel cases through 80 bits succeeded. The maximum charge is 34
attempts with fuel 352 on the 80-bit balanced input. The fixed default-fuel
anchor took 921.689 ms and matched its expected hash.

The generic and cyclotomic power-form batches both succeed with the same pinned
result hash. Their medians are 1.526 and 1.529 ms respectively; this aggregate
does not support adding more specialized identities or claiming a speedup.

## Comparator ratios

PARI 2.17.3 times a calibrated in-process `factor` batch. These ratios are
context, not a rho or dispatch gate; the two implementations do not expose the
same route portfolio.

| bits | Hex full factor | PARI `factor` | Hex / PARI |
|---:|---:|---:|---:|
| 32 | 0.601 ms | 0.003 ms | 175.90x |
| 40 | 6.603 ms | 0.006 ms | 1126.93x |
| 48 | 13.735 ms | 0.062 ms | 219.75x |
| 56 | 43.578 ms | 0.135 ms | 323.36x |
| 64 | 192.307 ms | 0.121 ms | 1588.08x |
| 72 | 728.078 ms | 0.184 ms | 3965.70x |
| 80 | 3148.246 ms | 0.430 ms | 7326.83x |

GMP-ECM 7.0.6 uses exactly `ecm -q -sigma 7 1000 1`: the same curve and B1 as
Hex, with B2 below B1 to disable stage 2. Every case and the input-15 overhead
control use the same persistent 256-input batch. The protocol floor is 0.217
ms/input; a row is ratio-eligible only when that floor is at most 50% of raw
time. Factor reconstruction is checked even on ineligible rows.

| bits | Hex ECM | GMP raw | adjusted | overhead | factor found | eligible | Hex / adjusted |
|---:|---:|---:|---:|---:|:---:|:---:|---:|
| 48 | 0.059 ms | 0.481 ms | 0.264 ms | 45.1% | yes | yes | 0.225x |
| 56 | 0.060 ms | 0.259 ms | 0.042 ms | 83.7% | yes | no | -- |
| 64 | 0.060 ms | 0.364 ms | 0.147 ms | 59.6% | yes | no | -- |
| 72 | 4.322 ms | 0.270 ms | 0.053 ms | 80.3% | no | no | -- |
| 76 | 4.323 ms | 0.349 ms | 0.132 ms | 62.1% | yes | no | -- |
| 80 | 4.378 ms | 0.376 ms | 0.159 ms | 57.7% | yes | no | -- |

Only the 48-bit row supports a ratio conclusion; the other five are reported
without drawing one. This is intentionally narrower than subtracting a noisy
process floor and presenting every adjusted value as comparable.

## Profile attribution

A fresh 999 Hz `samply 0.13.1` profile covers the separately registered raw-rho
80-bit rung at commit `a30ecb84eba72538fbe1e582563ab2ef7d0725f6` using
lean-bench-samply `9356baa2f5757ee40320a897bd284914d5bb9f5e`. It retained
3053 samples over 3088.0 ms, rejected eight boundary samples, observed no
off-thread noise, had 0.926 ms calibration residual, and passed the +/-5 ms
sensitivity check. The raw profile SHA-256 is
`580fca84c267736e6d9b20d7163376b72ffc2864f84b1f49db3b6e17e71e81c2`.

Leaf costs are allocation 66.89%, GMP 25.52%, Lean runtime 5.90%, and other
1.70% (98.30% classified). Inclusive samples put `rhoLeast`, `rhoTry`, and
`brentGo` on 94.20% of samples; `rhoNext` is 40.22%. The dominant self costs
are allocation/free paths, followed by GMP division and copy operations. This
confirms that raw rho's hot path is allocation-heavy and keeps that diagnosis
separate from the successful like-for-like full-pipeline control.

## Reproduction

```sh
lake build hexintfactor_bench HexIntFactorKernelProbe
.lake/build/bin/hexintfactor_bench list
.lake/build/bin/hexintfactor_bench verify
.lake/build/bin/hexintfactor_bench control-audit
.lake/build/bin/hexintfactor_bench default-fuel
nix shell nixpkgs#pari nixpkgs#ecm --command \
  python3 scripts/bench/intfactor_phase4.py \
    --cpu 7 --rounds 7 --timeout 120 \
    --output reports/bench-results/hex-int-factor-phase4-a30ecb84-chungus2-cpu7.json
nix shell nixpkgs#pari nixpkgs#ecm --command \
  python3 scripts/bench/intfactor_phase4.py --report \
    reports/bench-results/hex-int-factor-phase4-a30ecb84-chungus2-cpu7.json
LEAN_BENCH_SAMPLY_HOME=/tmp/lean-bench-samply-9634 \
  scripts/profile/run_profile.sh \
    .lake/build/bin/hexintfactor_bench \
    Hex.IntFactorBench.runBalancedRho 80 5000000000
python3 scripts/profile/summarize_profile.py \
  /tmp/hex-profile-runBalancedRho-80.json.gz \
  --thread hexintfactor_bench --top 20
```

The artifact preserves the full benchmark export, all control and fuel rows,
seven comparator rounds, the exact commands and versions, pre/post host state,
and source/executable hashes. Raw profile files remain under `/tmp` rather than
being committed.

## Concerns

None.
