# Dixon solve and determinant divisor

The implementation reuses a checked modular inverse for p-adic lifting, reconstructs and reduces a common-denominator solution, and checks the integer equation. The determinant route reconstructs the cofactor after extracting the reduced denominator as a determinant divisor. The tables below measure that route against ordinary CRT, Bareiss, and FLINT, and attribute single and repeated solves.

Dimension 512: divisor 0.2877 s, Bareiss 1.278 s (4.44× speedup), FLINT 0.1442 s (2.00× divisor/FLINT). The required 4× Bareiss threshold is met. The structured crossover is dimension 192; the total `detViaDivisor` wrapper uses Bareiss below it, while these main tables force each route at every rung. A separate table measures the public wrapper.

## Protocol and inputs

- Structured determinant: the shared salt-71 tridiagonal fixture, dimensions 16, 24, 32, 48, 64, 96, 128, 192, 256, 320, 384, 512.
- Dense determinant: splitmix64 seed 10219, signed entry widths 8, 64, 1024; dimensions 32, 64, 96, 128, 192, 256.
- Unimodular determinant: dense `I + u vᵀ`, `u = 1`, alternating `v = ±2⁶⁴`, hence determinant one. This is the divisor’s worst case.
- Single solve: dense 8-bit seed 10220 matrices at the same six dimensions. Integral RHS is `A C`; rational RHS is `C`, with `C[i,j] = (i + 3j) % 17 - 8`. The inverse is prepared outside the timed `solveWith` call; decomposition has its own arm.
- Repeated solve: `r = 1, 8, n`. Reused timing includes one decomposition and `solveMatWith`; independent timing includes `r` complete `solve?` calls. Both use the rational RHS and return the same common-denominator checksum.

Closed memoised fixture values are forced by discarded warmups. Matrix construction, RHS construction, and FLINT JSON input-tree construction are outside timed calls. Determinant arms include bound computation, prime search, elimination, and reconstruction; a fallback makes the forced modular/divisor benchmark fail. Seed 10220 selects the divisor RHS. FLINT uses a persistent python-flint process; serialization, parsing, and transport remain timed. Its determinant comparator gates the public structured dispatcher at 5× on every complete eligible rung; `fmpq_mat_solve` is informational and includes its own decomposition, unlike the separate Hex lifting arm.

Each registration has five fixed repeats, a 0.2-second tuning floor, and discarded outer and inner warmups. Adjacent arms reverse order on alternate rungs. Each collector leases an automatically selected CPU and uses two Lean workers pinned there. Host activity is recorded without filtering. Immutable executable copies and source hashes identify each run; different datasets are not a controlled before/after comparison.

Medians are seconds. FLINT ratios subtract the same dataset’s empty-protocol median from the FLINT denominator. `cap` describes a killed child batch, including setup and warmup; it is not a lower bound on one timed call. Ratios require five successful repeats in both arms. These fixed comparator anchors do not attest an empirical complexity fit. The generic algorithm uses cubic modular elimination, quadratic matrix-vector work per lifting digit, and one elimination per cofactor image; zero skipping and sparse residual products benefit the structured fixture.

## hex-modular-matrix-divisor-measured

Host `chungus2`, AMD EPYC 9455 48-Core Processor, CPU 37; Lean 4.34.0, python-flint 0.9.0. Protocol median 7.367 µs.

Load before `7.41 7.47 7.38 11/5886 980885`; after `5.40 5.91 6.87 5/5885 1093549`. [Raw exports and fingerprints](data/hex-modular-matrix-divisor-measured.json).

| Family | n | bits | Divisor s | Ordinary CRT s | Bareiss s | FLINT s | Bareiss / divisor | Divisor / FLINT |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| structured | 16 | 8 | 0.006112 | — | 2.064e-05 | 5.119e-05 | 0.00× | 139.47× |
| structured | 24 | 8 | 0.006351 | — | 7.712e-05 | 0.0001084 | 0.01× | 62.89× |
| structured | 32 | 8 | 0.006567 | — | 0.0001891 | 0.0001738 | 0.03× | 39.46× |
| structured | 48 | 8 | 0.007233 | — | 0.0007176 | 0.0004148 | 0.10× | 17.75× |
| structured | 64 | 8 | 0.008098 | — | 0.001864 | 0.001019 | 0.23× | 8.01× |
| structured | 96 | 8 | 0.01096 | — | 0.006999 | 0.002442 | 0.64× | 4.50× |
| structured | 128 | 8 | 0.01867 | — | 0.01761 | 0.004806 | 0.94× | 3.89× |
| structured | 192 | 8 | 0.03157 | — | 0.06294 | 0.01227 | 1.99× | 2.58× |
| structured | 256 | 8 | 0.05645 | — | 0.1538 | 0.02528 | 2.72× | 2.23× |
| structured | 320 | 8 | 0.08675 | — | 0.3091 | 0.04249 | 3.56× | 2.04× |
| structured | 384 | 8 | 0.1385 | — | 0.5332 | 0.06775 | 3.85× | 2.04× |
| structured | 512 | 8 | 0.2877 | — | 1.278 | 0.1442 | 4.44× | 2.00× |
| dense | 32 | 8 | 0.01089 | — | 0.00181 | 0.0002809 | 0.17× | 39.81× |
| dense | 64 | 8 | 0.04907 | — | 0.01722 | 0.001461 | 0.35× | 33.76× |
| dense | 96 | 8 | 0.1571 | — | 0.06558 | 0.003882 | 0.42× | 40.55× |
| dense | 128 | 8 | 0.3877 | — | 0.1722 | 0.007571 | 0.44× | 51.26× |
| dense | 192 | 8 | 1.401 | — | 0.7347 | 0.02092 | 0.52× | 67.00× |
| dense | 256 | 8 | 3.623 | — | 2.158 | 0.04658 | 0.60× | 77.80× |
| dense | 32 | 64 | 0.02915 | — | 0.00371 | 0.001149 | 0.13× | 25.54× |
| dense | 64 | 64 | 0.1595 | — | 0.05894 | 0.005508 | 0.37× | 28.99× |
| dense | 96 | 64 | 0.5129 | — | 0.3474 | 0.01402 | 0.68× | 36.61× |
| dense | 128 | 64 | 1.212 | — | 1.259 | 0.02785 | 1.04× | 43.55× |
| dense | 192 | 64 | 4.05 | — | cap (5/5) | 0.0769 | — | 52.67× |
| dense | 256 | 64 | cap (5/5) | — | cap (5/5) | 0.1644 | — | — |
| dense | 32 | 1024 | 0.6735 | — | 0.1748 | 0.1227 | 0.26× | 5.49× |
| dense | 64 | 1024 | 4.365 | — | 3.896 | 0.6704 | 0.89× | 6.51× |
| dense | 96 | 1024 | cap (5/5) | — | cap (5/5) | 1.986 | — | — |
| dense | 128 | 1024 | cap (5/5) | — | cap (5/5) | 4.513 | — | — |
| dense | 192 | 1024 | cap (5/5) | — | cap (5/5) | cap (5/5) | — | — |
| dense | 256 | 1024 | cap (5/5) | — | cap (5/5) | cap (5/5) | — | — |
| unimodular | 32 | 64 | 0.2383 | — | 0.002485 | 0.002631 | 0.01× | 90.82× |
| unimodular | 64 | 64 | 1.141 | — | 0.02016 | 0.01431 | 0.02× | 79.81× |
| unimodular | 96 | 64 | 4.223 | — | 0.06896 | 0.04976 | 0.02× | 84.88× |
| unimodular | 128 | 64 | cap (5/5) | — | 0.1679 | 0.1221 | — | — |
| unimodular | 192 | 64 | cap (5/5) | — | 0.5758 | 0.4322 | — | — |
| unimodular | 256 | 64 | cap (5/5) | — | 1.398 | 1.166 | — | — |

### Public determinant dispatcher

| n | Selected route | Public s | FLINT s | Public / FLINT |
|---:|---|---:|---:|---:|
| 16 | Bareiss | 2.078e-05 | 5.119e-05 | 0.47× |
| 24 | Bareiss | 7.744e-05 | 0.0001084 | 0.77× |
| 32 | Bareiss | 0.0001902 | 0.0001738 | 1.14× |
| 48 | Bareiss | 0.0007159 | 0.0004148 | 1.76× |
| 64 | Bareiss | 0.001859 | 0.001019 | 1.84× |
| 96 | Bareiss | 0.007014 | 0.002442 | 2.88× |
| 128 | Bareiss | 0.01761 | 0.004806 | 3.67× |
| 192 | divisor | 0.03159 | 0.01227 | 2.58× |
| 256 | divisor | 0.05683 | 0.02528 | 2.25× |
| 320 | divisor | 0.08665 | 0.04249 | 2.04× |
| 384 | divisor | 0.1376 | 0.06775 | 2.03× |
| 512 | divisor | 0.2925 | 0.1442 | 2.03× |

Every complete structured rung with a positive adjusted FLINT median meets the 5× public-entry-point threshold. The forced divisor rows above also expose its fixed cost below the crossover.

## hex-modular-matrix-solve-measured

Host `chungus2`, AMD EPYC 9455 48-Core Processor, CPU 46; Lean 4.34.0, python-flint 0.9.0. Protocol median 7.401 µs.

Load before `7.41 7.47 7.38 10/5886 980889`; after `10.79 8.71 7.86 11/5948 995588`. [Raw exports and fingerprints](data/hex-modular-matrix-solve-measured.json).

| Operation | n | Hex s | FLINT s | Hex / FLINT |
|---|---:|---:|---:|---:|
| decomposition | 32 | 0.004308 | — | — |
| integral | 32 | 0.0003189 | 0.0002982 | 1.10× |
| rational | 32 | 0.002308 | 0.0004167 | 5.64× |
| decomposition | 64 | 0.01952 | — | — |
| integral | 64 | 0.001705 | 0.001182 | 1.45× |
| rational | 64 | 0.01676 | 0.001749 | 9.62× |
| decomposition | 96 | 0.05917 | — | — |
| integral | 96 | 0.0049 | 0.002798 | 1.76× |
| rational | 96 | 0.05428 | 0.004042 | 13.45× |
| decomposition | 128 | 0.1349 | — | — |
| integral | 128 | 0.01094 | 0.005324 | 2.06× |
| rational | 128 | 0.1289 | 0.007776 | 16.59× |
| decomposition | 192 | 0.4493 | — | — |
| integral | 192 | 0.03639 | 0.0128 | 2.84× |
| rational | 192 | 0.4414 | 0.02194 | 20.12× |
| decomposition | 256 | 1.107 | — | — |
| integral | 256 | 0.08646 | 0.02504 | 3.45× |
| rational | 256 | 1.042 | 0.05434 | 19.18× |

## hex-modular-matrix-repeated-measured

Host `chungus2`, AMD EPYC 9455 48-Core Processor, CPU 41; Lean 4.34.0, python-flint 0.9.0. Protocol median 7.392 µs.

Load before `7.41 7.47 7.38 12/5887 980888`; after `8.64 8.56 8.31 8/5871 1043017`. [Raw exports and fingerprints](data/hex-modular-matrix-repeated-measured.json).

| n | RHS count | Reused s | Independent s | Independent / reused |
|---:|---:|---:|---:|---:|
| 32 | 1 | 0.00656 | 0.006587 | 1.00× |
| 32 | 8 | 0.02161 | 0.05286 | 2.45× |
| 32 | 32 | 0.07296 | 0.2107 | 2.89× |
| 64 | 1 | 0.0362 | 0.03616 | 1.00× |
| 64 | 8 | 0.1494 | 0.2893 | 1.94× |
| 64 | 64 | 1.082 | 2.335 | 2.16× |
| 96 | 1 | 0.1142 | 0.1143 | 1.00× |
| 96 | 8 | 0.4917 | 0.9109 | 1.85× |
| 96 | 96 | cap (5/5) | cap (5/5) | — |
| 128 | 1 | 0.266 | 0.2654 | 1.00× |
| 128 | 8 | 1.177 | 2.142 | 1.82× |
| 128 | 128 | cap (5/5) | cap (5/5) | — |
| 192 | 1 | 0.8936 | 0.8935 | 1.00× |
| 192 | 8 | 4.005 | cap (5/5) | — |
| 192 | 192 | cap (5/5) | cap (5/5) | — |
| 256 | 1 | 2.161 | 2.159 | 1.00× |
| 256 | 8 | cap (5/5) | cap (5/5) | — |
| 256 | 256 | cap (5/5) | cap (5/5) | — |

## Earlier prepared comparison including ordinary CRT

This retained schedule measures all four forced arms together. It precedes the single-check divisor path and lifting-modulus hoist; ordinary CRT is unchanged. Ratios below use only arms within this schedule. [Raw exports and fingerprints](data/hex-modular-matrix-divisor-prepared.json).

| Family | n | bits | Divisor s | Ordinary CRT s | Bareiss s | FLINT s | Bareiss / divisor | Divisor / FLINT |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| structured | 16 | 8 | 0.006188 | 0.006926 | 2.085e-05 | 5.119e-05 | 0.00× | 141.03× |
| structured | 24 | 8 | 0.006405 | 0.007203 | 7.648e-05 | 0.0001082 | 0.01× | 63.49× |
| structured | 32 | 8 | 0.006706 | 0.009466 | 0.0001878 | 0.0001737 | 0.03× | 40.31× |
| structured | 48 | 8 | 0.007452 | 0.01364 | 0.0007101 | 0.0004122 | 0.10× | 18.40× |
| structured | 64 | 8 | 0.008447 | 0.02101 | 0.001846 | 0.00102 | 0.22× | 8.34× |
| structured | 96 | 8 | 0.01152 | 0.04631 | 0.006862 | 0.002426 | 0.60× | 4.76× |
| structured | 128 | 8 | 0.01969 | 0.109 | 0.01736 | 0.004801 | 0.88× | 4.11× |
| structured | 192 | 8 | 0.03367 | 0.4364 | 0.06144 | 0.01234 | 1.83× | 2.73× |
| structured | 256 | 8 | 0.06137 | 1.294 | 0.1476 | 0.02537 | 2.41× | 2.42× |
| structured | 320 | 8 | 0.09421 | 3.127 | 0.2964 | 0.04281 | 3.15× | 2.20× |
| structured | 384 | 8 | 0.1472 | cap (5/5) | 0.5134 | 0.0678 | 3.49× | 2.17× |
| structured | 512 | 8 | 0.2889 | cap (5/5) | 1.234 | 0.1446 | 4.27× | 2.00× |
| dense | 32 | 8 | 0.01113 | 0.03257 | 0.001837 | 0.0002798 | 0.17× | 40.84× |
| dense | 64 | 8 | 0.0493 | 0.1442 | 0.01741 | 0.001455 | 0.35× | 34.05× |
| dense | 96 | 8 | 0.1566 | 0.5277 | 0.06653 | 0.003876 | 0.42× | 40.49× |
| dense | 128 | 8 | 0.3891 | 1.584 | 0.1738 | 0.007588 | 0.45× | 51.32× |
| dense | 192 | 8 | 1.406 | cap (5/5) | 0.7366 | 0.02105 | 0.52× | 66.82× |
| dense | 256 | 8 | 3.611 | cap (5/5) | 2.164 | 0.04672 | 0.60× | 77.31× |
| dense | 32 | 64 | 0.02943 | 0.2145 | 0.003683 | 0.001145 | 0.13× | 25.87× |
| dense | 64 | 64 | 0.1599 | 0.9865 | 0.05943 | 0.005499 | 0.37× | 29.12× |
| dense | 96 | 64 | 0.52 | 3.649 | 0.3465 | 0.01394 | 0.67× | 37.33× |
| dense | 128 | 64 | 1.215 | cap (5/5) | 1.254 | 0.02766 | 1.03× | 43.94× |
| dense | 192 | 64 | 4.034 | cap (5/5) | cap (5/5) | 0.07634 | — | 52.84× |
| dense | 256 | 64 | cap (5/5) | cap (5/5) | cap (5/5) | 0.1632 | — | — |
| dense | 32 | 1024 | 0.667 | 3.364 | 0.1731 | 0.1218 | 0.26× | 5.48× |
| dense | 64 | 1024 | 4.485 | cap (5/5) | 3.873 | 0.6666 | 0.86× | 6.73× |
| dense | 96 | 1024 | cap (5/5) | cap (5/5) | cap (5/5) | 1.971 | — | — |
| dense | 128 | 1024 | cap (5/5) | cap (5/5) | cap (5/5) | 4.473 | — | — |
| dense | 192 | 1024 | cap (5/5) | cap (5/5) | cap (5/5) | cap (5/5) | — | — |
| dense | 256 | 1024 | cap (5/5) | cap (5/5) | cap (5/5) | cap (5/5) | — | — |
| unimodular | 32 | 64 | 0.2406 | 0.2266 | 0.002523 | 0.002646 | 0.01× | 91.18× |
| unimodular | 64 | 64 | 1.132 | 1.076 | 0.02059 | 0.01434 | 0.02× | 79.00× |
| unimodular | 96 | 64 | 4.176 | 3.984 | 0.06998 | 0.04972 | 0.02× | 84.01× |
| unimodular | 128 | 64 | cap (5/5) | cap (5/5) | 0.1707 | 0.1227 | — | — |
| unimodular | 192 | 64 | cap (5/5) | cap (5/5) | 0.584 | 0.4303 | — | — |
| unimodular | 256 | 64 | cap (5/5) | cap (5/5) | 1.397 | 1.162 | — | — |

## Attribution

The dimension-512 diagnostic uses 67 lifting digits. Its reduced denominator has 882 bits, leaving a 143-bit cofactor bound and a 155-bit CRT modulus. Decomposition took 80.8 ms, solve/reconstruction 93.4 ms, and cofactor reconstruction 91.7 ms. [Stage output and host context](data/hex-modular-matrix-divisor-stages-final.json). These separate diagnostic timings do not replace the repeated comparator medians.

The auxiliary bound computation took 6.0 ms; generating 35 primes took 77.4 ms. The existing prime generator tests candidates by full trial division through their square root. This contributes a fixed cost on small matrices. The production route first probes one prime and sizes the cofactor prefix from its bound, so it need not pay for the whole auxiliary supply.

A pinned profile retained 231 samples with 0 reported lost. Its five largest self-sample entries are:

| Self samples | Symbol |
|---:|---|
| 11.75% | `lp_Hex_Hex_Matrix_Word_dot___redArg` |
| 8.72% | `lean_apply_1` |
| 7.80% | `lean_apply_2` |
| 4.38% | `lean_dec_ref_cold` |
| 3.89% | `lp_Hex_Hex_ZMod64_addImpl___redArg` |

[Profile](data/hex-modular-matrix-divisor-profile-final.txt), [invocation and host](data/hex-modular-matrix-divisor-profile-final-host.json), [benchmark export](data/hex-modular-matrix-divisor-profile-final.json).

## Bound image counts

The ordinary CRT conformance fixtures retain the row-norm and Hadamard bound comparison. Counts include the terminating image. [Raw counts](data/hex-modular-matrix-image-counts.json).

| Case | Row norm | Hadamard |
|---|---:|---:|
| empty | 1 | 1 |
| singleton-negative | 1 | 1 |
| zero | 1 | 1 |
| singular | 1 | 1 |
| swap-sign | 1 | 1 |
| modulus | 2 | 2 |
| two-bad-primes | 3 | 3 |
| large-small-determinant | 133 | 133 |
| scaled-hadamard | 3 | 3 |
| structured-determinant/8 | 1 | 1 |
| dense-random-determinant/8-bit | 2 | 1 |
| dense-random-determinant/64-bit | 9 | 9 |
| dense-random-determinant/1024-bit | 100 | 100 |
| unimodular-determinant/positive | 13 | 13 |
| unimodular-determinant/negative | 13 | 13 |

## Correctness and retained measurements

The full build and conformance suite verify single and multiple RHS solutions, normalisation, lifting congruences, strict digit bounds, zero-dimensional cases, composite moduli, unlucky initial primes, seeds, and forced exhaustion. FLINT checks 159 complete answers. Eight CI smoke anchors pin output hashes. Every completed common comparator result is checked for hash agreement by this report generator.

The reduction regression supplies `y = 3, d = 6` to the production cofactor route for `A = [2], b = [1]`. It must reduce to denominator two. Removing reduction from that route makes the assertion fail; the mutation was built locally. The prime reuse test checks the resulting CRT modulus, and a modulus sharing a factor with the reduced denominator is rejected before its determinant image is computed.

Earlier implementation measurements and profiles are retained below. The initial Gauss–Jordan pass cleared above each pivot immediately, destroying upper-factor sparsity. Forward elimination followed by backward clearing, determinant-only cofactor images, cached inverse rows, sparse integer products, and shorter prime prefixes remove that overhead. These observations motivated changes; their ratios are not controlled before/after evidence.

The earlier `divisor-final`, `solve`, and `repeated` datasets used functions whose pure preparation was moved into timed calls by Lean arity expansion. They therefore include fixture construction; `solve` also includes decomposition. They are retained as end-to-end diagnostics, not presented as separate `solveWith` costs. Early stage files’ `bound_ns` and `supply_ns` were similarly affected by code motion and are not used for attribution. The corrected stage diagnostic forces these values before reading the clock. The `prepared` datasets precede the single-check divisor path and hoisted lifting modulus. Their ordinary-CRT measurements remain applicable because those subsequent changes affect only Dixon. The final `measured` schedule omits that unchanged arm; its full measurements are retained in the prepared export.

- [hex-modular-matrix-baseline-resumed](data/hex-modular-matrix-baseline-resumed.json)
- [hex-modular-matrix-baseline](data/hex-modular-matrix-baseline.json)
- [hex-modular-matrix-collector-check](data/hex-modular-matrix-collector-check.json)
- [hex-modular-matrix-divisor-512](data/hex-modular-matrix-divisor-512.json)
- [hex-modular-matrix-divisor-cached-stages](data/hex-modular-matrix-divisor-cached-stages.json)
- [hex-modular-matrix-divisor-fast-stages](data/hex-modular-matrix-divisor-fast-stages.json)
- [hex-modular-matrix-divisor-final](data/hex-modular-matrix-divisor-final.json)
- [hex-modular-matrix-divisor-prefix-512](data/hex-modular-matrix-divisor-prefix-512.json)
- [hex-modular-matrix-divisor-prefix-stages](data/hex-modular-matrix-divisor-prefix-stages.json)
- [hex-modular-matrix-divisor-prepared-profile](data/hex-modular-matrix-divisor-prepared-profile.json)
- [hex-modular-matrix-divisor-prepared-stages](data/hex-modular-matrix-divisor-prepared-stages.json)
- [hex-modular-matrix-divisor-prepared](data/hex-modular-matrix-divisor-prepared.json)
- [hex-modular-matrix-divisor-profile-final-host](data/hex-modular-matrix-divisor-profile-final-host.json)
- [hex-modular-matrix-divisor-profile-final](data/hex-modular-matrix-divisor-profile-final.json)
- [hex-modular-matrix-divisor-profile-host](data/hex-modular-matrix-divisor-profile-host.json)
- [hex-modular-matrix-divisor-profile](data/hex-modular-matrix-divisor-profile.json)
- [hex-modular-matrix-divisor-row-512](data/hex-modular-matrix-divisor-row-512.json)
- [hex-modular-matrix-divisor-sparse-profile](data/hex-modular-matrix-divisor-sparse-profile.json)
- [hex-modular-matrix-divisor-sparse-repeat-stages](data/hex-modular-matrix-divisor-sparse-repeat-stages.json)
- [hex-modular-matrix-divisor-sparse-stages](data/hex-modular-matrix-divisor-sparse-stages.json)
- [hex-modular-matrix-divisor-stages-final](data/hex-modular-matrix-divisor-stages-final.json)
- [hex-modular-matrix-divisor-stages](data/hex-modular-matrix-divisor-stages.json)
- [hex-modular-matrix-divisor-supply-stages](data/hex-modular-matrix-divisor-supply-stages.json)
- [hex-modular-matrix-divisor-word-512](data/hex-modular-matrix-divisor-word-512.json)
- [hex-modular-matrix-image-counts](data/hex-modular-matrix-image-counts.json)
- [hex-modular-matrix-large-integers](data/hex-modular-matrix-large-integers.json)
- [hex-modular-matrix-profile](data/hex-modular-matrix-profile.json)
- [hex-modular-matrix-repeated-prepared](data/hex-modular-matrix-repeated-prepared.json)
- [hex-modular-matrix-repeated](data/hex-modular-matrix-repeated.json)
- [hex-modular-matrix-smoke](data/hex-modular-matrix-smoke.json)
- [hex-modular-matrix-solve-prepared](data/hex-modular-matrix-solve-prepared.json)
- [hex-modular-matrix-solve](data/hex-modular-matrix-solve.json)

Reproduce: `lake build hexmodularmatrix_bench`, then `HEX_FLINT_BENCH_PYTHON=<python-with-flint> python3 scripts/bench/modmat_flint.py <output.json> --mode divisor --omit-modular` (or `--mode solve`, `--mode repeated`). Omit `--omit-modular` to include ordinary CRT. Render this report with `python3 scripts/bench/modmat_report.py reports/hex-modular-matrix-performance.md reports/data/hex-modular-matrix-divisor-measured.json reports/data/hex-modular-matrix-solve-measured.json reports/data/hex-modular-matrix-repeated-measured.json`.
