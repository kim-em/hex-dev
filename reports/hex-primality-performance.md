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
`reports/bench-results/hex-primality-compiled-f2c153ebb-chungus2.json`
(SHA-256
`b7d06514c0c3e458241467f7d3791951750140f54a44619ebb334c185f4c45ac`).
It was produced from pristine commit
`f2c153ebbdc084ff9510fe167d65d77e1afef898` on `chungus2`, an AMD EPYC
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
  --export-file reports/bench-results/hex-primality-compiled-f2c153ebb-chungus2.json
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
| `runMillerRabin` | inconclusive | -1.557 | 175.397 us |
| `runProbablePrime` | inconclusive | -1.575 | 2.255 ms |
| `runDecision` | inconclusive | -1.476 | 3.571 ms |
| `runTotalDecision` | inconclusive | -1.469 | 3.583 ms |
| `runCertSearch` | inconclusive | -1.475 | 3.596 ms |
| `runChecker` | inconclusive | -0.511 | 604.449 us |

The remaining parametric registrations use mode 1, the strongest applicable
mode, because each registration has a pre-measurement family-specific
derivation adjacent to it.  All seven are consistent with their declared
complexity:

| target | range | `beta` | largest-rung median |
|---|---:|---:|---:|
| `runSieve` | 1000--32000 | -0.423 | 2.707 ms |
| `runTableLookup` | 4096--65536 | +0.017 | 5.197 ms |
| `runOrder` | 1009--32003 | -0.003 | 135.393 us |
| `runPMinusOne` | 64--8192 | -0.116 | 298.571 us |
| `runRho` | 100003--30000001 least factor | +0.163 | 4.722 ms |
| `runSegment` | 1000--32000 | -0.165 | 24.527 ms |
| `runNextPrime` | gap 4--64 | -0.042 | 2.439 us |

The 512-bit rho-backed route and sole Pocklington-3 shape have no honest
one-parameter family, so modes 1 and 2 do not apply.  They use mode 3 absolute
budgets.  Decision, search, and replay each have a 5 s budget; Pocklington-3
has a 2 s budget.  Their medians were respectively 13.407 ms, 13.448 ms,
678.436 us, and 632 ns, with all five samples and expected hashes agreeing.

The release-quality proof record is
`reports/bench-results/hex-primality-core-proof-issue-9762-chungus2.json`
(SHA-256
`e73b2cc14e37e049f6cfeaf20d619d0858859db235f9253c457e9511c28519f1`).
It uses six rotated samples per pair, alternates reference/candidate
orientation, rejects contaminated physical-core windows, records source and
olean hashes and sizes, and applies a 10 s absolute fresh-module budget.  The
pristine source was commit `0cb80651ad3914a9a7cf3133555523dd1410ff77`
with tree `f817a4e57f52fcf30f4574acf8c8825a9d098634` on `chungus2`, Lean
4.34.0-rc2, pinned to CPU 5 with SMT sibling 53.  The driver admitted all 180
required substantive pair samples and 18 null samples, rejected 26 complete
pair attempts and 1,388 preflight windows, exhausted no pair, recorded no
validity exception, and classified the artifact `release_quality=true`.
Every replay and tactic sample reported exactly
`[propext, Classical.choice, Quot.sound]`; no other axiom appeared.  The
largest absolute fresh build was 3.608 s, inside the 10 s budget.

The null controls precede the substantive data.  Values below are the six raw
signed candidate-minus-reference wall-time deltas in milliseconds, followed
by their median and full range:

| null control | raw paired deltas (ms) | median (ms) | range (ms) |
|---|---|---:|---:|
| import baseline | 634.482, 55.907, -117.352, 92.192, -6.537, 39.805 | 47.856 | 751.834 |
| 123-bit tactic | -334.059, 126.836, 91.122, -115.071, -13.696, -37.040 | -25.368 | 460.895 |
| 512-bit tactic | -885.864, -71.978, -85.496, 109.590, -10.418, -33.780 | -52.879 | 995.454 |

Each substantive entry likewise reports all six rotated paired deltas.  The
candidate median is an absolute fresh-module time, not a null-subtracted
estimate:

| probe | raw paired deltas (ms) | median delta (ms) | candidate median (ms) |
|---|---|---:|---:|
| 31 input | 153.640, 79.050, -31.244, 129.425, -0.877, 35.602 | 57.326 | 1222.541 |
| 31 search | -9.011, -90.218, -43.019, 28.285, -13.328, -84.227 | -28.173 | 1194.973 |
| 31 literal | 34.204, 74.643, -78.791, 31.744, -37.501, -9.780 | 10.982 | 1207.556 |
| 31 replay | 1522.971, 1105.805, 1191.614, 1231.927, 1096.465, 1213.033 | 1202.324 | 2410.852 |
| 31 tactic | 1152.605, 1311.024, 1302.646, 1189.734, 1296.463, 1114.392 | 1243.098 | 2456.700 |
| 61 input | -180.111, -39.730, 10.066, 5.181, -134.858, 92.362 | -17.274 | 1188.194 |
| 61 search | -226.255, -112.006, 0.858, -116.312, -30.721, 28.473 | -71.363 | 1188.858 |
| 61 literal | -20.783, -25.293, 157.254, 5.138, 61.071, 10.310 | 7.724 | 1205.729 |
| 61 replay | 1319.003, 1131.475, 1313.541, 1185.406, 1201.902, 1128.478 | 1193.654 | 2377.075 |
| 61 tactic | 1143.874, 1213.364, 1190.274, 1223.166, 1310.722, 1110.167 | 1201.819 | 2397.718 |
| 123 input | -192.531, -55.829, -16.636, -23.400, 21.037, 34.782 | -20.018 | 1204.732 |
| 123 search | -29.624, -12.502, 55.621, 134.070, -54.646, 17.090 | 2.294 | 1257.440 |
| 123 literal | 46.637, 48.128, 17.932, -4.166, 97.057, 4.627 | 32.285 | 1226.263 |
| 123 replay | 1228.215, 1357.355, 1204.793, 1108.394, 1182.982, 1227.967 | 1216.380 | 2427.310 |
| 123 tactic | 1107.107, 1310.275, 1184.069, 1210.008, 1252.106, 1221.292 | 1215.650 | 2433.888 |
| 256 input | 135.350, 23.191, -55.779, -7.646, -25.263, 8.774 | 0.564 | 1195.301 |
| 256 search | 45.046, 53.365, -8.783, -12.178, -50.159, 178.854 | 18.132 | 1187.580 |
| 256 literal | -204.006, -1.408, -53.237, 149.655, 39.682, 29.551 | 14.071 | 1222.245 |
| 256 replay | 1360.718, 1404.854, 1337.427, 1321.112, 1326.655, 1247.635 | 1332.041 | 2536.849 |
| 256 tactic | 1402.989, 1343.759, 1361.421, 1399.966, 1279.006, 1299.033 | 1352.590 | 2560.490 |
| 511 input | 10.330, -12.284, 58.239, -28.462, -36.382, -0.378 | -6.331 | 1170.865 |
| 511 search | -115.602, -7.869, -67.012, -8.102, -54.353, 97.763 | -31.227 | 1182.732 |
| 511 literal | 106.125, -129.549, 13.946, -75.893, 126.292, 22.817 | 18.381 | 1217.613 |
| 511 replay | 1501.654, 1549.916, 1630.660, 1512.330, 1337.027, 1525.897 | 1519.113 | 2726.788 |
| 511 tactic | 1585.138, 1535.405, 1544.004, 1494.378, 1366.627, 1491.849 | 1514.892 | 2698.082 |
| 512 input | 37.442, 12.711, 16.407, 10.308, 122.516, 43.456 | 26.925 | 1194.100 |
| 512 search | 105.396, -42.550, -15.812, 107.502, -12.672, 37.840 | 12.584 | 1225.275 |
| 512 literal | -80.594, 22.416, 0.718, -10.143, 89.500, 74.200 | 11.567 | 1183.518 |
| 512 replay | 1443.276, 1430.125, 1474.771, 1564.708, 1278.215, 1508.635 | 1459.023 | 2717.991 |
| 512 tactic | 1632.469, 1526.679, 1414.426, 1500.914, 1402.275, 1517.502 | 1509.208 | 2694.096 |

The committed record contains the corresponding raw absolute arm times,
peak RSS, precise child CPU accounting, host snapshots, preflight windows,
artifact sizes and hashes, and deterministic source hashes.  The exact command
is:

```sh
python3 scripts/bench/primality_core_proof_sweep.py --samples 6 \
  --shared-host --expected-host chungus2 --cpu 5 --timeout 30 \
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

Both declared families have inclusive profiles.  Certificate search was
profiled from pristine commit `ca6f6f9ca`; segment enumeration was profiled
from pristine commit `5b86166ee`, whose segment path is unchanged.  The
filtered summaries are committed; raw profiler JSON remains developer-local.
Calibration, minimum sample count, and the +/-5 ms sensitivity checks all
passed, with no samples on other threads inside timed windows.

- `table-smooth-certificates`: `runCertSearch` at 511 bits retained 3,656
  samples (8 rejected) over 3,669.23 ms.  Inclusive cost was
  `primeCertCountedUsing?` 85.28%, `millerRabin` 53.86%, `mrWitnessLoop`
  39.91%, `powModNatGo` 25.96%, and `checkPrime` 14.91%.  Leaf attribution was
  GMP 62.69%, allocation 27.32%, Lean runtime 6.51%, and library code 2.22%.
  Summary:
  `reports/bench-results/hex-primality-profile-cert-ca6f6f9ca-chungus2.json`
  (SHA-256
  `1cdaf9ac3c358941eecd100572815cd530b85c7bef0980caa1fe72a2d70f9911`).
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
python3 scripts/profile/summarize_profile.py \
  /tmp/hex-profile-runCertSearch-511.json.gz \
  --thread hexprimality_bench \
  --output reports/bench-results/hex-primality-profile-cert-ca6f6f9ca-chungus2.json
python3 scripts/profile/summarize_profile.py \
  /tmp/hex-profile-runSegment-32000.json.gz \
  --thread hexprimality_bench \
  --output reports/bench-results/hex-primality-profile-segment-5b86166ee-chungus2.json
```

## Concerns

None.
