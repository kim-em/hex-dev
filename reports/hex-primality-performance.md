# HexPrimality Performance Report

## Bench Targets

The compiled suite owns each executable surface once.  The first six rows use
the published schoolbook upper bound; the next seven use two-sided controlled
families; the last four are canonical fixed boundaries.

| target | declared complexity or fixed purpose |
|---|---|
| `Hex.PrimalityBench.runMillerRabin` | `n * n * n` |
| `Hex.PrimalityBench.runProbablePrime` | `n * n * n` |
| `Hex.PrimalityBench.runDecision` | `n * n * n` |
| `Hex.PrimalityBench.runTotalDecision` | `n * n * n` |
| `Hex.PrimalityBench.runCertSearch` | `n * n * n` |
| `Hex.PrimalityBench.runChecker` | `n * n * n` |
| `Hex.PrimalityBench.runSieve` | `n * Nat.sqrt n` |
| `Hex.PrimalityBench.runTableLookup` | `n` |
| `Hex.PrimalityBench.runOrder` | `n` |
| `Hex.PrimalityBench.runPMinusOne` | `n` |
| `Hex.PrimalityBench.runRho` | `Nat.sqrt n` |
| `Hex.PrimalityBench.runSegment` | `n * Nat.sqrt n` |
| `Hex.PrimalityBench.runNextPrime` | `n` |
| `Hex.PrimalityBench.runDecision512` | fixed 512-bit rho-backed decision boundary |
| `Hex.PrimalityBench.runCertSearch512` | fixed 512-bit rho-backed search boundary |
| `Hex.PrimalityBench.runChecker512` | fixed twin of the 512-bit kernel replay |
| `Hex.PrimalityBench.runPock3Checker` | fixed Pocklington-3 constructor anchor |

The proof track has matched fresh modules at 31, 61, 123, 256, 511, and 512
bits.  For every size it measures import baseline to input construction, input
to compiled production-search attribution, input to the exact emitted
certificate literal, literal to `prime_of_checkPrimeAt` kernel replay, and
import baseline to full Mathlib-free `primality` elaboration.  Those thirty
pairs replace generic compiled timing for input elaboration, emitted-term
construction, theorem instantiation, kernel acceptance, and the tactic surface.
The sweep also places import-baseline, 123-bit-tactic, and 512-bit-tactic null
controls before the substantive pairs in its rotated order.

This assignment is normative in
`HexPrimality/SPEC/hex-primality.md`.  The `table-smooth-certificates` family
contains committed exact production-search witnesses, while
`segment-enumeration` exercises the complete initial-segment route.

## Verdicts

The compiled scientific record is
`reports/bench-results/hex-primality-compiled-75ec0de4f-chungus2.json`
(SHA-256
`fb409f326d6f39395f0eae5a47e33d31bd0f069e535f01755268d95be06980ee`).
It was produced from pristine commit
`75ec0de4f278da97e630da5162745e7890978167` on `chungus2`, an AMD EPYC
9455 host, with Lean 4.34.0-rc2.  All rows passed their expected-result hashes.
The exact command was:

```sh
taskset -c 22 lake exe hexprimality_bench run \
  Hex.PrimalityBench.runMillerRabin \
  Hex.PrimalityBench.runProbablePrime \
  Hex.PrimalityBench.runDecision \
  Hex.PrimalityBench.runTotalDecision \
  Hex.PrimalityBench.runCertSearch \
  Hex.PrimalityBench.runChecker \
  Hex.PrimalityBench.runSieve \
  Hex.PrimalityBench.runTableLookup \
  Hex.PrimalityBench.runOrder \
  Hex.PrimalityBench.runPMinusOne \
  Hex.PrimalityBench.runRho \
  Hex.PrimalityBench.runSegment \
  Hex.PrimalityBench.runNextPrime \
  Hex.PrimalityBench.runDecision512 \
  Hex.PrimalityBench.runCertSearch512 \
  Hex.PrimalityBench.runChecker512 \
  Hex.PrimalityBench.runPock3Checker \
  --export-file reports/bench-results/hex-primality-compiled-75ec0de4f-chungus2.json
```

The bit-size rows are mode 2.  A tight family-specific model is not derivable:
GMP changes multiplication algorithms across the ladder and each certificate
has an input-dependent shrinking tree.  Binary powering uses `O(b)`
multiplications on `b`-bit operands, and schoolbook multiplication is
`O(b^2)`, giving the published conservative `O(b^3)` bound (Brent and
Zimmermann, *Modern Computer Arithmetic*, chapter 1).  The certificate-search
profile below confirms that modular powering and certificate construction
dominate the registered family.  The two-sided harness therefore says
`inconclusive` because it observes substantially faster scaling; the Phase-4
result is the distinct one-sided verdict **within declared upper bound
(observed faster)**.

| target | harness verdict | slope residual `beta` | largest-rung median |
|---|---:|---:|---:|
| `runMillerRabin` | inconclusive | -1.581 | 177.556 us |
| `runProbablePrime` | inconclusive | -1.548 | 2.355 ms |
| `runDecision` | inconclusive | -1.467 | 3.659 ms |
| `runTotalDecision` | inconclusive | -1.463 | 3.625 ms |
| `runCertSearch` | inconclusive | -1.471 | 3.629 ms |
| `runChecker` | inconclusive | -0.506 | 611.109 us |

The remaining parametric registrations use mode 1, the strongest applicable
mode, because each registration has a pre-measurement family-specific
derivation adjacent to it.  All seven are consistent with their declared
complexity:

| target | range | `beta` | largest-rung median |
|---|---:|---:|---:|
| `runSieve` | 1000--32000 | -0.415 | 2.820 ms |
| `runTableLookup` | 4096--65536 | +0.019 | 5.405 ms |
| `runOrder` | 1009--32003 | -0.003 | 135.674 us |
| `runPMinusOne` | 64--8192 | -0.116 | 297.277 us |
| `runRho` | 100003--30000001 least factor | +0.166 | 4.940 ms |
| `runSegment` | 1000--32000 | -0.169 | 24.546 ms |
| `runNextPrime` | gap 4--64 | -0.046 | 2.428 us |

The 512-bit rho-backed route and sole Pocklington-3 shape have no honest
one-parameter family, so modes 1 and 2 do not apply.  They use mode 3 absolute
budgets.  Decision, search, and replay each have a 5 s budget; Pocklington-3
has a 2 s budget.  Their medians were respectively 13.423 ms, 13.496 ms,
677.945 us, and 623 ns, with all five samples and expected hashes agreeing.

The release-quality proof record is
`reports/bench-results/hex-primality-core-proof-issue-9762-chungus2.json`
(SHA-256
`344e5acd2c6f57e4a61981bcd0b3733a3d42054584c326297c0a45ba7eb97de5`).
It uses six rotated samples per pair, alternates reference/candidate
orientation, rejects contaminated physical-core windows, records source and
olean hashes and sizes, and applies a 10 s absolute fresh-module budget.  The
pristine source was commit `995d4a9dd44e4b7f9bfe251b31fafd98e5e50d36`
with tree `d127b8e59cc07c136006924f8556ed20934a2085` on `chungus2`, Lean
4.34.0-rc2, pinned to CPU 19 with SMT sibling 67.  The driver admitted all 180
required substantive pair samples and 18 null samples, rejected 63 complete
pair attempts and 940 preflight windows, exhausted no pair, recorded no
validity exception, and classified the artifact `release_quality=true`.
Every replay and tactic sample reported exactly
`[propext, Classical.choice, Quot.sound]`; no other axiom appeared.  The
largest absolute fresh build was 4.016 s, inside the 10 s budget.

The null controls precede the substantive data.  Values below are the six raw
signed candidate-minus-reference wall-time deltas in milliseconds, followed
by their median and full range:

| null control | raw paired deltas (ms) | median (ms) | range (ms) |
|---|---|---:|---:|
| import baseline | -352.856, -114.426, 321.107, 7.334, 29.432, -227.065 | -53.546 | 673.962 |
| 123-bit tactic | -499.480, 240.988, -106.234, 301.564, -368.954, 23.610 | -41.312 | 801.044 |
| 512-bit tactic | -344.032, 83.668, 102.805, 258.963, -1002.537, -79.968 | 1.850 | 1261.500 |

Each substantive entry likewise reports all six rotated paired deltas.  The
candidate median is an absolute fresh-module time, not a null-subtracted
estimate:

| probe | raw paired deltas (ms) | median delta (ms) | candidate median (ms) |
|---|---|---:|---:|
| 31 input | -417.694, -90.517, 225.100, -101.687, -29.505, 64.060 | -60.011 | 1171.538 |
| 31 search | -0.514, 105.570, 98.666, 216.372, 150.166, -0.166 | 102.118 | 1180.340 |
| 31 literal | 112.691, 108.801, 0.935, -23.897, -29.918, 65.494 | 33.215 | 1115.495 |
| 31 replay | 1397.475, 1656.350, 2421.019, 1557.634, 1215.286, 1230.046 | 1477.555 | 2572.770 |
| 31 tactic | 1500.241, 1807.447, 1991.966, 2333.393, 971.005, 1463.998 | 1653.844 | 2692.726 |
| 61 input | 5.998, 296.871, 192.946, 279.350, 286.875, -96.344 | 236.148 | 1351.163 |
| 61 search | 104.126, 141.180, -2.555, -270.837, 7.129, 85.087 | 46.108 | 1291.129 |
| 61 literal | -7.813, 605.098, -116.845, 310.186, -139.447, -84.539 | -46.176 | 1229.560 |
| 61 replay | 1297.930, 1482.615, 1608.061, 1553.886, 1356.142, 1327.989 | 1419.379 | 2532.332 |
| 61 tactic | 1129.798, 1831.079, 2516.278, 1665.845, 1274.979, 1234.191 | 1470.412 | 2842.577 |
| 123 input | -143.033, 0.658, 71.413, 268.601, 100.294, 93.561 | 82.487 | 1237.090 |
| 123 search | -472.297, -215.287, -108.371, 103.253, 2.021, -69.666 | -89.018 | 1231.508 |
| 123 literal | -294.613, 200.399, -201.363, 65.758, 11.523, -19.027 | -3.752 | 1235.748 |
| 123 replay | 798.516, 1623.371, 708.622, 1445.643, 1410.438, 1456.260 | 1428.040 | 2741.252 |
| 123 tactic | 1266.238, 1614.070, 1820.700, 1328.388, 1630.561, 1228.711 | 1471.229 | 2605.793 |
| 256 input | 7.618, -24.178, 89.053, -55.889, -417.434, -114.252 | -40.034 | 1148.663 |
| 256 search | 130.698, 114.650, 102.843, -36.038, -10.960, 86.183 | 94.513 | 1211.398 |
| 256 literal | 5.038, 3.874, 209.489, 99.804, 102.063, 81.333 | 90.569 | 1150.507 |
| 256 replay | 1248.469, 1750.634, 1717.363, 1622.036, 1743.135, 2924.091 | 1730.249 | 2811.009 |
| 256 tactic | 1184.536, 1584.907, 1163.455, 1305.600, 2152.889, 1627.602 | 1445.254 | 2623.541 |
| 511 input | -122.963, -160.096, -1.504, 2.171, -68.585, 115.324 | -35.045 | 1210.565 |
| 511 search | 2.927, -169.444, 102.660, 467.464, -323.114, 246.625 | 52.794 | 1127.140 |
| 511 literal | -7.006, 2.539, 29.565, 160.045, 191.147, 163.646 | 94.805 | 1142.485 |
| 511 replay | 1609.773, 1817.073, 1402.790, 1655.353, 2159.674, 1733.059 | 1694.206 | 2832.064 |
| 511 tactic | 1511.188, 1510.632, 1628.599, 2584.716, 1614.802, 1412.235 | 1562.995 | 2731.243 |
| 512 input | 9.348, 0.294, 97.058, 8.384, 0.610, -8.045 | 4.497 | 1111.975 |
| 512 search | -44.578, 102.899, 210.408, -50.339, -102.643, -2.932 | -23.755 | 1154.323 |
| 512 literal | 91.730, -11.111, 80.654, 512.979, -216.719, 110.308 | 86.192 | 1158.843 |
| 512 replay | 1714.646, 1788.392, 1913.013, 2678.915, 1805.610, 1626.943 | 1797.001 | 2928.561 |
| 512 tactic | 1604.430, 1920.371, 1710.793, 1791.877, 1434.578, 1478.180 | 1657.612 | 2789.333 |

The committed record contains the corresponding raw absolute arm times,
peak RSS, precise child CPU accounting, host snapshots, preflight windows,
artifact sizes and hashes, and deterministic source hashes.  The exact command
is:

```sh
python3 scripts/bench/primality_core_proof_sweep.py --samples 6 \
  --shared-host --expected-host chungus2 --cpu 19 --timeout 30 \
  --warm-timeout 600 --max-pair-retries 32 \
  --preflight-timeout-seconds 3600 \
  --output reports/bench-results/hex-primality-core-proof-issue-9762-chungus2.json
```

The settled core policy is: generated and proved table bound `10^5`; bounded
decision dispatch through 6,000,000 before the total trial fallback;
certificate construction fuel `bitLength n + 1`; `HexArith.powModNat` as the
kernel-facing route; and Mathlib-free `primality` support through 512 bits with
a 10 s fresh-module budget.  The SPEC records the derivations, boundary cases,
and retained policy-selection evidence.

Smoke wiring is reproduced with:

```sh
lake build HexPrimality HexPrimalityKernelProbe
lake exe hexprimality_bench list
lake exe hexprimality_bench verify
```

## Comparator ratios

The declared comparator is **PrimeCert (b-mehta/PrimeCert kernel-replay primality certificates)**,
classified informational.  The driver installed
templates for the same exact six witnesses into a separate PrimeCert checkout,
then rotated tool order and baseline/replay arm order for six samples per size.
The committed raw record is
`reports/bench-results/hex-primality-primecert-ce4dbcfeb-chungus2.json`
(SHA-256
`a54e9f54a7a590bf37fbdad454832a647cd05b2b0ff9692c572984979845a9e8`).
Hex was pristine commit `ce4dbcfeb1c76f4437508db9f65acc0e061e9791`
using Lean 4.34.0-rc2; PrimeCert was pristine commit
`924f63d9500e53e2dcb0dcbd0579287a8b194395` using Lean 4.33.0.

| bits | Hex replay median | PrimeCert replay median | Hex / PrimeCert |
|---:|---:|---:|---:|
| 31 | 3.072 s | 3.023 s | 1.016 |
| 61 | 3.293 s | 3.385 s | 0.973 |
| 123 | 3.129 s | 2.811 s | 1.113 |
| 256 | 4.306 s | 4.016 s | 1.072 |
| 511 | 3.613 s | 3.599 s | 1.004 |
| 512 | 3.495 s | 3.274 s | 1.067 |

These are absolute fresh-replay ratios, not baseline-subtracted numbers: under
the shared host's high load, some baseline builds exceeded replay builds.
Load-one ranged from 12.54 to 146.50 and concurrent Lake/Lean processes from 6
to 123, all retained in the raw record.  Together with the differing
toolchains, that makes the result useful evidence of parity within 12%, but
not a release gate or a claim about incremental elaboration cost.

The exact command was:

```sh
python3 scripts/bench/primality_primecert_compare.py \
  --primecert-checkout /tmp/hex-primecert-9762 --samples 6 --cpu 3 \
  --output reports/bench-results/hex-primality-primecert-ce4dbcfeb-chungus2.json
```

## Profile

Both declared families have inclusive profiles from pristine commit
`5b86166ee`.  The filtered summaries are committed; raw profiler JSON remains
developer-local.  Calibration, minimum sample count, and the +/-5 ms
sensitivity checks all passed, with no samples on other threads inside timed
windows.

- `table-smooth-certificates`: `runCertSearch` at 511 bits retained 3,722
  samples (8 rejected) over 3,751.55 ms.  Inclusive cost was
  `primeCertCountedWith?` 84.98%, `millerRabin` 54.94%, `mrWitnessLoop`
  40.68%, `powModNatGo` 24.83%, and `checkPrime` 14.05%.  Leaf attribution was
  GMP 63.33%, allocation 26.63%, Lean runtime 7.31%, and library code 2.28%.
  Summary:
  `reports/bench-results/hex-primality-profile-cert-5b86166ee-chungus2.json`
  (SHA-256
  `8833ea39a833138b909e30448682eea029135e126a8604fc5914dac70ae413dd`).
- `segment-enumeration`: `runSegment` at 32,000 retained 3,076 samples (8
  rejected) over 3,094.64 ms.  Inclusive cost was `primesIn` 99.84% and
  `isPrimeTrialAux` 98.57%; leaf attribution was allocation 39.47%, GMP
  32.05%, library code 17.46%, and Lean runtime 10.40%.  Summary:
  `reports/bench-results/hex-primality-profile-segment-5b86166ee-chungus2.json`
  (SHA-256
  `e7dc808580ca594ce29241e0875c5ab527f2a2b9c9566c88a564c61ad8b03bad`).

The exact commands were:

```sh
LEAN_BENCH_SAMPLY_HOME=/tmp/lean-bench-samply-9762 \
  scripts/profile/run_profile.sh .lake/build/bin/hexprimality_bench \
  Hex.PrimalityBench.runCertSearch 511 5000000000
LEAN_BENCH_SAMPLY_HOME=/tmp/lean-bench-samply-9762 \
  scripts/profile/run_profile.sh .lake/build/bin/hexprimality_bench \
  Hex.PrimalityBench.runSegment 32000 5000000000
```

## Concerns

None.
