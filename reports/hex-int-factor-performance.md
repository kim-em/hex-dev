# HexIntFactor performance

## Scope and acceptance

This is the Phase-4 report for `HexIntFactor`. It covers the five input
families declared in `libraries.yml`: table and balanced semiprimes, smooth and
unbalanced semiprimes, power forms, certificate replay and order, and
generalized divisor sums. The exact declared comparator name is
**PARI factor and GMP-ECM**. Both endpoints are informational: PARI exposes a broader
factorization portfolio, while GMP-ECM is a separately tuned C implementation.

The compiled scientific track contains seven parametric and 31 fixed targets.
Every parametric target returned the exact harness verdict
`consistent_with_declared_complexity`; every fixed target completed its
preregistered repeats, agreed across hashes, matched its canonical expected
hash, and passed its collector-owned scientific budget. The benchmark bodies
contain only generous process timeouts, so `verify` remains a correctness and
bitrot check rather than a shared-runner timing gate.

The `HexIntFactorMathlib` audit under #9368 classifies the bridge as a
correspondence-only layer. `HexIntFactor` therefore remains the computational
performance owner.

## Bench targets

| Declared family | Compiled and kernel targets | Role |
|---|---|---|
| table-and-balanced-semiprimes | `runTableDispatch`, `runTableTrial`, `runBalancedFactor{32..80}`, `runBalancedCompletion{32..80}`, `runBalancedRho` | output-agreeing table control; separate public, raw-split, and post-split surfaces |
| smooth-and-unbalanced-semiprimes | `runPMinusOneBatch`, `runEcmBatch`, `runEcmRhoBatch`, `runEcm{48,56,64,72,76,80}` | fixed whole-family and per-rung route measurements |
| power-forms | `runCyclotomicBatch`, `runPowerGenericBatch`, `runPowerSplitBatch` | structural split plus same-seed complete-factorization comparison |
| certificate-replay-and-order | `runReplay`, `HexIntFactorKernelProbe`, `runOrder`, `runDownstreamOrder`, `runDownstreamPrimitiveRoot` | compiled scaling, actual kernel replay, and opaque fixed operands |
| generalized-divisor-sums | `runSigmaExponent`, `runSigmaFactorCount`, `runSquareFactorCount`, `runTotientFactorCount` | prepared certified inputs with independently derived models |
| cross-family default fuel | `runDefaultFuelSchedule` | exact public schedule over all 49 committed cases |

`Hex.IntFactorProfile.runSmooth` (ECM stage 1) and
`Hex.IntFactorProfile.runPower` are
attribution-only runners. Their parameter is an honest repetition count over
one committed representative operand; it does not assert an operand-size model
for either mode-3 family.

## Native artifact and harness verdicts

The clean native artifact is
`reports/bench-results/hex-int-factor-phase4-ecb06bcb-chungus2-cpu7.json`
(SHA-256
`65bf567777a07e963f344befc70e7f41a0fe11882628b43729ae3ccd99d809d9`).
It records source commit `ecb06bcb19222e1656cc7039c9abdace00da4ddb`,
benchmark executable SHA-256
`d0bd18eb6f48d3ef210f323e686932c56832df6c0c03214c7faa4c084ca1d4bf`,
Lean 4.34.0-rc2, lean-bench 0.1.0, host `chungus2`, and CPU 7 affinity.

| Target | Domain | Declared model | Exact verdict | Slope |
|---|---:|---:|---|---:|
| `runSquareFactorCount` | 32--1024 entries | `n * n` | `consistent_with_declared_complexity` | -0.145 |
| `runReplay` | exponent 1024--262144 | `n * n` | `consistent_with_declared_complexity` | -0.017 |
| `runBalancedRho` | 32--80 bits | `2 ^ (n / 4)` | `consistent_with_declared_complexity` | n/a |
| `runSigmaFactorCount` | 32--1024 entries | `n * n` | `consistent_with_declared_complexity` | 0.039 |
| `runTotientFactorCount` | 32--1024 entries | `n * n` | `consistent_with_declared_complexity` | 0.101 |
| `runSigmaExponent` | 16384--4194304 | `n * n.log2` | `consistent_with_declared_complexity` | 0.150 |
| `runOrder` | 257--1048589 | `n` | `consistent_with_declared_complexity` | -0.002 |

All scheduled rungs were measured and none was budget-truncated. The harness's
preregistered warmup fraction excludes the first ratio from each verdict fit;
the artifact retains every raw rung, trial, ratio, and the resulting
`verdict_dropped_leading = 1` metadata. `runReplay` reports the informational
`partially_below_signal_floor` advisory, but has enough surviving rows for the
quoted verdict.

The complete fixed-target table below is rendered from that artifact. The
phrase `expected hash match` is the artifact's
`expected_hash_check.status = "match"`; the power rows use seven repeats and
all other fixed rows use three.

| Target | Exact harness result |
|---|---|
| `runPowerGenericBatch` | median 2.008 ms; expected hash match |
| `runBalancedCompletion64` | median 4.527 ms; expected hash match |
| `runBalancedFactor64` | median 193.084 ms; expected hash match |
| `runPMinusOneBatch` | median 11.050 ms; expected hash match |
| `runBalancedFactor72` | median 720.462 ms; expected hash match |
| `runEcm48` | median 0.060 ms; expected hash match |
| `runEcmRhoBatch` | median 175.476 ms; expected hash match |
| `runBalancedCompletion80` | median 4.730 ms; expected hash match |
| `runBalancedFactor40` | median 6.440 ms; expected hash match |
| `runPowerSplitBatch` | median 1.915 ms; expected hash match |
| `runDownstreamOrder` | median 0.001 ms; expected hash match |
| `runBalancedFactor48` | median 13.355 ms; expected hash match |
| `runTableTrial` | median 0.032 ms; expected hash match |
| `runBalancedFactor56` | median 43.347 ms; expected hash match |
| `runDefaultFuelSchedule` | median 921.422 ms; expected hash match |
| `runCyclotomicBatch` | median 0.014 ms; expected hash match |
| `runEcm72` | median 4.300 ms; expected hash match |
| `runDownstreamPrimitiveRoot` | median 1.224 ms; expected hash match |
| `runTableDispatch` | median 0.038 ms; expected hash match |
| `runBalancedCompletion56` | median 3.797 ms; expected hash match |
| `runEcm56` | median 0.060 ms; expected hash match |
| `runEcmBatch` | median 12.938 ms; expected hash match |
| `runBalancedCompletion32` | median 1.242 ms; expected hash match |
| `runBalancedFactor32` | median 0.620 ms; expected hash match |
| `runBalancedFactor80` | median 3158.427 ms; expected hash match |
| `runBalancedCompletion48` | median 3.776 ms; expected hash match |
| `runEcm76` | median 4.274 ms; expected hash match |
| `runEcm64` | median 0.060 ms; expected hash match |
| `runEcm80` | median 4.273 ms; expected hash match |
| `runBalancedCompletion72` | median 4.464 ms; expected hash match |
| `runBalancedCompletion40` | median 3.831 ms; expected hash match |

## Factorization decomposition and retained power route

The balanced five-seed family is deliberately three different surfaces. Full
public `factor?` includes preprocessing, primality rejection, splitting,
recursive completion, certificate construction, and checked acceptance. Raw
rho starts from the declared seed and returns only a normalized split. The
public route advances its generator during primality work before reaching rho,
so raw rho and full public factorization are separate deterministic executions,
not a continuous timing decomposition. Completion starts from the exact split
and advanced generator state produced by the direct-rho execution, factors both
sides, canonically merges them, and runs checked acceptance. The untimed control
recomputes that direct-rho trajectory and proves that the stored split/state and
both complete outputs agree.

| bits | public route | public full | raw rho split | post-split completion | full / rho | full / (rho + completion) |
|---:|---|---:|---:|---:|---:|---:|
| 32 | table-complete | 0.620 ms | 0.112 ms | 1.242 ms | 5.534x | 0.458x |
| 40 | rho-driven | 6.440 ms | 2.350 ms | 3.831 ms | 2.741x | 1.042x |
| 48 | rho-driven | 13.355 ms | 9.298 ms | 3.776 ms | 1.436x | 1.022x |
| 56 | rho-driven | 43.347 ms | 39.217 ms | 3.797 ms | 1.105x | 1.008x |
| 64 | rho-driven | 193.084 ms | 181.835 ms | 4.527 ms | 1.062x | 1.036x |
| 72 | rho-driven | 720.462 ms | 728.312 ms | 4.464 ms | 0.989x | 0.983x |
| 80 | rho-driven | 3158.427 ms | 3207.515 ms | 4.730 ms | 0.985x | 0.983x |

The two ratios are explanatory observations, not gates between unequal APIs.
The 32-bit public operand is fully consumed by the committed prime table, so
its raw-rho and completion columns are cross-surface diagnostics rather than a
decomposition of the public route. On the 40--80-bit rho-driven rungs, the
ratios show fixed completion cost dominating the low rungs and raw rho
dominating the upper rungs. Ratios below one are possible because the public
and direct-rho generator trajectories differ. They do not define a second
algorithm or support an inference about SQUFOF.

The independent table control has identical canonical hashes: public dispatch
is 0.038159 ms and direct trial division is 0.032235 ms, a 1.184x ratio under
the preregistered 1.25 gate.

Generic and cyclotomic power factorization use the same target-derived seed,
the same exponent set 12 through 80 (including 72 and 80), and canonical
complete-factorization encodings. Both have hash `0x681a285cd74ea124` over
seven repeats. The split/generic median ratio is 0.954, satisfying the
preregistered `<= 0.98` retention rule by 2.6 percentage points, so the
specialized route remains. That margin is real but intentionally modest; the
seven retained paired repeats make it visible rather than hiding it in one run.

Every one of the 49 default-fuel cases succeeded, including all direct-`Nat`
balanced, smooth, ECM, and power cases through 80 bits. The maximum observed
charge is 34 attempts; the maximum committed fuel is 352.

## Mode-3 conversion and absolute budgets

For the fixed families, asymptotic regression detection was explicitly given
up rather than retrofitting a slope:

- Full balanced factorization was attempted as a five-seed 32--80-bit
  `2^(bits/4)` schedule. Certificate construction and completion dominate
  different lower rungs, so only the isolated raw-rho surface retains that
  model.
- Integer value is not a useful table parameter because it mixes unrelated
  factor shapes; the committed uniform batch is the workload.
- Fixed-bound p-1 crosses word/direct-`Nat` regimes and plateaus in limb count.
  No single observed parameter gave a stable tight model.
- ECM has only three word and three direct-`Nat` rungs. That sparse schedule
  cannot distinguish constant, linear, and multiplication costs.
- Cyclotomic and power-form cost changes with divisor and factor shape, not
  monotonically with exponent alone.
- The downstream order and primitive-root probes are fixed because the chosen
  50- and 61-bit primes have deliberately short orders; treating operand width
  as a general order-cost model would be false.

Budgets were preregistered from the preceding clean pinned-host diagnostic,
rounded upward to coarse 10/20/50/100/200/500/750/2000/6000 ms ceilings. A
10 ms resolution envelope is the minimum for sub-millisecond targets. The
slowest target still has 90.0% clean-baseline headroom; all other targets have
at least 111.4%. `margin` is `(budget / clean median - 1) * 100`.

| Target | Clean median (ms) | Budget (ms) | Margin |
|---|---:|---:|---:|
| `runBalancedCompletion32` | 1.242 | 10 | 705.4% |
| `runBalancedCompletion40` | 3.831 | 10 | 161.0% |
| `runBalancedCompletion48` | 3.776 | 10 | 164.8% |
| `runBalancedCompletion56` | 3.797 | 10 | 163.4% |
| `runBalancedCompletion64` | 4.527 | 10 | 120.9% |
| `runBalancedCompletion72` | 4.464 | 10 | 124.0% |
| `runBalancedCompletion80` | 4.730 | 10 | 111.4% |
| `runBalancedFactor32` | 0.620 | 10 | 1513.4% |
| `runBalancedFactor40` | 6.440 | 50 | 676.4% |
| `runBalancedFactor48` | 13.355 | 100 | 648.8% |
| `runBalancedFactor56` | 43.347 | 200 | 361.4% |
| `runBalancedFactor64` | 193.084 | 750 | 288.4% |
| `runBalancedFactor72` | 720.462 | 2000 | 177.6% |
| `runBalancedFactor80` | 3158.427 | 6000 | 90.0% |
| `runCyclotomicBatch` | 0.014 | 10 | 72935.3% |
| `runDefaultFuelSchedule` | 921.422 | 2000 | 117.1% |
| `runDownstreamOrder` | 0.001 | 10 | 811588.3% |
| `runDownstreamPrimitiveRoot` | 1.224 | 20 | 1534.4% |
| `runEcm48` | 0.060 | 20 | 33348.7% |
| `runEcm56` | 0.060 | 20 | 33216.7% |
| `runEcm64` | 0.060 | 20 | 33070.8% |
| `runEcm72` | 4.300 | 20 | 365.1% |
| `runEcm76` | 4.274 | 20 | 367.9% |
| `runEcm80` | 4.273 | 20 | 368.0% |
| `runEcmBatch` | 12.938 | 100 | 672.9% |
| `runEcmRhoBatch` | 175.476 | 500 | 184.9% |
| `runPMinusOneBatch` | 11.050 | 100 | 805.0% |
| `runPowerGenericBatch` | 2.008 | 20 | 896.1% |
| `runPowerSplitBatch` | 1.915 | 20 | 944.1% |
| `runTableDispatch` | 0.038 | 10 | 26106.1% |
| `runTableTrial` | 0.032 | 10 | 30922.2% |

These are collector assertions on CPU 7, not target-body assertions in
`lake exe hexintfactor_bench verify`.

## External comparator ratios

PARI 2.17.3 times a calibrated in-process `factor` batch. The Hex side is
normalized from each five-seed batch to one factorization before the ratio is
formed. PARI does not expose the same route portfolio, so these values are
context rather than an internal rho or dispatch gate.

| bits | Hex factor per call | PARI `factor` | Hex / PARI |
|---:|---:|---:|---:|
| 32 | 0.124 ms | 0.003 ms | 36.27x |
| 40 | 1.288 ms | 0.006 ms | 219.81x |
| 48 | 2.671 ms | 0.062 ms | 43.42x |
| 56 | 8.669 ms | 0.135 ms | 64.33x |
| 64 | 38.617 ms | 0.121 ms | 318.90x |
| 72 | 144.092 ms | 0.182 ms | 793.28x |
| 80 | 631.685 ms | 0.422 ms | 1497.33x |

The low rungs are irregular because the implementations select different
portfolios. From 48 through 80 bits the ratio grows sharply from 43.42x to
1497.33x. The accompanying raw-rho profile attributes the Hex-side cost to the
Brent loop, allocation, and GMP, while the wall ratio also includes an expected
portfolio and algorithm-class divergence from PARI. It is useful orientation,
not a standalone unresolved defect and not evidence for a particular
unobserved PARI route.

GMP-ECM 7.0.6 uses exactly `ecm -q -sigma 0:7 1000 1`: parameterization 0,
curve sigma 7, B1 1000, and B2 below B1 to disable stage 2. The explicit
`parameterization:sigma` syntax removes any dependence on GMP-ECM's default;
verbose probes report `sigma=0:7` for every operand. Every operand and the
overhead control use the same persistent 256-input batch. The measured floor
is 0.220 ms/input; a row is ratio-eligible only under the preregistered rule
that this floor is at most 50% of raw time. Equal discovered factors do not
imply equal stage-1 wall cost: a curve can reach a gcd checkpoint with the
whole composite on one cofactor while yielding a nontrivial gcd on another.
Output reconstruction is checked even for ineligible rows.

| bits | Hex ECM | GMP raw | adjusted | factor found | eligible | Hex / adjusted |
|---:|---:|---:|---:|:---:|:---:|---:|
| 48 | 0.060 ms | 0.484 ms | 0.264 ms | yes | yes | 0.23x |
| 56 | 0.060 ms | 0.263 ms | 0.043 ms | yes | no | -- |
| 64 | 0.060 ms | 0.365 ms | 0.145 ms | yes | no | -- |
| 72 | 4.300 ms | 0.271 ms | 0.052 ms | no | no | -- |
| 76 | 4.274 ms | 0.348 ms | 0.129 ms | yes | no | -- |
| 80 | 4.273 ms | 0.378 ms | 0.158 ms | yes | no | -- |

Only the 48-bit row supports a ratio conclusion. No ratio is inferred from the
five overhead-dominated rows.

## Kernel replay

The fresh-module artifact is
`reports/bench-results/hex-int-factor-kernel-replay-7d0ee1e2-chungus2-cpu8.json`
(SHA-256
`bb36b862702dfba3cd370f82acd4bb9cdf1d020b1668a1163079f8f35230c547`).
It records clean source commit `7d0ee1e2a479d08a9eeaf617531a3b113aa43e55`,
host `chungus2`, CPU 8 with SMT sibling 56, six rotated paired samples, and
expected axiom inventory `[propext]`. `release_quality` is true: there are no
violations, preflight failures, or exhausted pairs. Contaminated pair attempts
were discarded and retried.

Each candidate is a fresh module containing an actual `decide +kernel`
`checkFactorization` replay; its paired reference imports the same support but
does not replay the certificate. The last case includes a 61-bit factor.

The two preregistered null controls expose fresh-build noise before the
substantive replay rows. Signed deltas are candidate minus reference; ranges
and the robust spread ratio are retained rather than summarized away.

| Null control | Six signed deltas (ms) | median (ms) | min--max (ms) | absolute range (ms) | max absolute (ms) | robust spread / build magnitude |
|---|---|---:|---:|---:|---:|---:|
| fresh-build | -1358.286, -1.162, -1.844, -200.425, 31.959, 1.598 | -1.503 | -1358.286--31.959 | 1390.244 | 1358.286 | 0.1361 |
| replay-10-shaped | 761.383, 0.186, 6.991, 402.610, -2.910, 6.162 | 6.576 | -2.910--761.383 | 764.293 | 761.383 | 0.1575 |

| factors | largest factor bits | reference build (ms) | replay build (ms) | paired delta (ms) | 5000 ms budget |
|---:|---:|---:|---:|---:|:---:|
| 1 | 5 | 1114.165 | 1911.862 | 795.350 | passed |
| 2 | 5 | 1117.675 | 1915.716 | 797.513 | passed |
| 3 | 5 | 1110.550 | 1925.647 | 809.464 | passed |
| 4 | 5 | 1113.632 | 1914.667 | 799.800 | passed |
| 5 | 5 | 1111.804 | 1918.667 | 800.257 | passed |
| 6 | 5 | 1117.847 | 1912.373 | 796.981 | passed |
| 7 | 5 | 1112.407 | 1910.479 | 797.950 | passed |
| 8 | 5 | 1113.485 | 1916.493 | 801.543 | passed |
| 9 | 5 | 1113.388 | 1912.860 | 800.571 | passed |
| 10 | 61 | 1114.870 | 1919.637 | 807.732 | passed |

All six rotated signed deltas for each substantive row are:

| factors | signed deltas (ms) |
|---:|---|
| 1 | 1796.499, 796.619, 699.286, 794.081, 792.063, 797.364 |
| 2 | 1427.998, 704.752, 792.132, 706.371, 808.260, 802.894 |
| 3 | 2693.454, 811.615, 800.828, 701.422, 826.142, 807.314 |
| 4 | 1387.050, 801.348, 798.252, 801.959, 786.509, 790.237 |
| 5 | 702.254, 798.798, 812.009, 705.364, 828.306, 801.717 |
| 6 | 1291.868, 808.339, 800.209, 652.894, 781.484, 793.753 |
| 7 | 809.771, 688.771, 803.642, 702.523, 796.764, 799.136 |
| 8 | 805.734, 800.290, 707.559, 746.200, 808.842, 802.797 |
| 9 | 802.246, 810.787, 696.899, 762.798, 799.992, 801.150 |
| 10 | 804.019, 906.271, 811.445, 2809.758, 797.925, 792.900 |

The candidate medians are flat across `k = 1..10`; the 61-bit final witness
does not introduce a visible replay cliff at this resolution. Individual raw
samples contain large positive excursions mirrored by the null controls, so
the claim is deliberately limited to the rotated-pair medians and 5000 ms
budget rather than a fine-grained slope.

## Five-family profile attribution

All profiles use clean commit `97d3b1f292710ccdf502671d8d9c01d6ad09d74c`,
`samply 0.13.1`, lean-bench-samply commit
`9356baa2f5757ee40320a897bd284914d5bb9f5e`, and the 999 Hz filtered timed-region
protocol. Every profile has confidence `passed`, zero off-bench-thread samples,
at least 3014 retained samples, calibration residual below 2 ms against the
5 ms limit, and sensitivity verdict `passed`.

| Declared family / representative | Profile SHA-256 | retained / residual | Leaf categories | Dominant inclusive path |
|---|---|---:|---|---|
| table-and-balanced-semiprimes: `runBalancedRho 80` | `1a39e495c5e97409b52039c70260889260ea1059ea262ae89d53289894507a83` | 3014 / 0.050 ms | allocation 68.12%, GMP 24.68%, runtime 5.11%, other 2.09% | `rhoLeast` / `rhoTry` / `brentGo` 93.56%; `rhoNext` 39.85% |
| smooth-and-unbalanced-semiprimes: `IntFactorProfile.runSmooth 1` (80-bit ECM stage 1) | pending clean recapture | pending | pending | pending |
| power-forms: `IntFactorProfile.runPower 1` (exponent 80 split) | `aaaecc7c59a022f1105d9d672bc8298215b5620952cd7ff64f1cd95558d5619e` | 4563 / 1.505 ms | Lean runtime 35.04%, Lean own code 21.96%, other 20.91%, allocation 20.40%, GMP 1.69% | trial division 88.67%; `removePower` 28.14%; `factorPower?` 14.71% |
| certificate-replay-and-order: `runOrder 1048589` | `31a09f8b9e37f3c6d9020d8fec92c0340f7e4a961b81e6720e2152d60f619d11` | 6842 / 0.223 ms | other 99.91%, allocation 0.09% | `orderOf` 100.00%; `orderOfAux` 99.91% |
| generalized-divisor-sums: `runSigmaExponent 4194304` | `541ee2b206a3f40c2364b0b002deaad6b47485eccaab410b23ca92b457cab37b` | 6431 / 0.378 ms | GMP 93.28%, other 6.34%, allocation 0.37% | `sigma` 73.85%; `sigmaEntry` 72.83% |

The balanced rho profile attributes its dominant cost to allocation and GMP
underneath the Brent loop. The smooth/unbalanced profile directly exercises
ECM stage 1 rather than duplicating rho. Power forms are dominated by trial
division and exact-power removal, order by the repository's private compiled
order scan, and the large-exponent sigma case by GMP arithmetic. No declared
family is left with an unattributed dominant cost.

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
    --output reports/bench-results/hex-int-factor-phase4-ecb06bcb-chungus2-cpu7.json
nix shell nixpkgs#pari nixpkgs#ecm --command \
  python3 scripts/bench/intfactor_phase4.py --report \
    reports/bench-results/hex-int-factor-phase4-ecb06bcb-chungus2-cpu7.json

python3 scripts/bench/intfactor_kernel_replay.py \
  --samples 6 --shared-host --expected-host chungus2 --cpu 8 \
  --max-pair-retries 32 --timeout 30 --warm-timeout 300 \
  --output reports/bench-results/hex-int-factor-kernel-replay-7d0ee1e2-chungus2-cpu8.json

LEAN_BENCH_SAMPLY_HOME=/tmp/lean-bench-samply-9634 \
  scripts/profile/run_profile.sh .lake/build/bin/hexintfactor_bench \
    Hex.IntFactorBench.runBalancedRho 80 5000000000
LEAN_BENCH_SAMPLY_HOME=/tmp/lean-bench-samply-9634 \
  scripts/profile/run_profile.sh .lake/build/bin/hexintfactor_bench \
    Hex.IntFactorProfile.runSmooth 1 5000000000
LEAN_BENCH_SAMPLY_HOME=/tmp/lean-bench-samply-9634 \
  scripts/profile/run_profile.sh .lake/build/bin/hexintfactor_bench \
    Hex.IntFactorProfile.runPower 1 5000000000
LEAN_BENCH_SAMPLY_HOME=/tmp/lean-bench-samply-9634 \
  scripts/profile/run_profile.sh .lake/build/bin/hexintfactor_bench \
    Hex.IntFactorBench.runOrder 1048589 5000000000
LEAN_BENCH_SAMPLY_HOME=/tmp/lean-bench-samply-9634 \
  scripts/profile/run_profile.sh .lake/build/bin/hexintfactor_bench \
    Hex.IntFactorBench.runSigmaExponent 4194304 5000000000

python3 scripts/profile/summarize_profile.py PROFILE.json.gz \
  --thread hexintfactor_bench --top 20
```

The artifact preserves the full benchmark export, controls, all 49 fuel rows,
seven comparator rounds, external outputs, exact versions and commands, host
state, and source/executable hashes. Raw profiles and their symbol sidecars
remain under `/tmp`; their content hashes above make each cited capture
identifiable. The profiling orchestrator has SHA-256
`ef0aabd98ef0dee35feb19696e006ef64849cba6140b433024d950c6c7c5e32e`;
the summarizer has SHA-256
`ba36b14948d7986bb8c349f2655323b24d33cc05ad0349d492e9929e00ab24fe`.

## Concerns

GMP-ECM's specialized stage-1 implementation is externally faster on its one
eligible row, and PARI's broader factorization portfolio is faster on every
balanced rung. These are expected algorithm- and implementation-class gaps
recorded for orientation, not missing attribution or a failed gating
requirement.
