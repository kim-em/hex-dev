# Dixon solve and determinant divisor

The implementation reuses a checked modular inverse for p-adic lifting, reconstructs and reduces a common-denominator solution, and checks the integer equation. The determinant route reconstructs the cofactor after extracting the reduced denominator as a determinant divisor. The tables below measure that route against ordinary CRT, Bareiss, and FLINT, and attribute single and repeated solves.

The completed dimension-512 comparator run records 0.279 s for the divisor, 1.263 s for Bareiss (4.52× faster), and 0.153 s for FLINT (1.83× slower after protocol adjustment). [Raw comparison](data/hex-modular-matrix-divisor-prefix-512.json). That run includes fixture construction. The prepared-input schedule below isolates algorithm cost and is retained separately. The structured crossover is dimension 192; the total `detViaDivisor` wrapper uses Bareiss below it, while the benchmarks force each route at every rung.

## Protocol and inputs

- Structured determinant: the shared salt-71 tridiagonal fixture, dimensions 16, 24, 32, 48, 64, 96, 128, 192, 256, 320, 384, 512.
- Dense determinant: splitmix64 seed 10219, signed entry widths 8, 64, 1024; dimensions 32, 64, 96, 128, 192, 256.
- Unimodular determinant: dense `I + u vᵀ`, `u = 1`, alternating `v = ±2⁶⁴`, hence determinant one. This is the divisor’s worst case.
- Single solve: dense 8-bit seed 10220 matrices at the same six dimensions. Integral RHS is `A C`; rational RHS is `C`, with `C[i,j] = (i + 3j) % 17 - 8`. The inverse is prepared outside the timed `solveWith` call; decomposition has its own arm.
- Repeated solve: `r = 1, 8, n`. Reused timing includes one decomposition and `solveMatWith`; independent timing includes `r` complete `solve?` calls. Both use the rational RHS and return the same common-denominator checksum.

Closed memoised fixture values are forced by discarded warmups. Matrix construction, RHS construction, and FLINT request encoding are outside timed calls. Determinant arms include bound computation, prime search, elimination, and reconstruction; a fallback makes the forced modular/divisor benchmark fail. Seed 10220 selects the divisor RHS. FLINT uses a persistent python-flint process. Its determinant comparator is gating under the SPEC’s first-measurement policy; `fmpq_mat_solve` is informational and includes its own decomposition, unlike the separate Hex lifting arm.

Each registration has five fixed repeats, a 0.2-second tuning floor, and discarded outer and inner warmups. Adjacent arms reverse order on alternate rungs. Each collector leases an automatically selected CPU and uses two Lean workers pinned there. Host activity is recorded without filtering. Immutable executable copies and source hashes identify each run; different datasets are not a controlled before/after comparison.

Medians are seconds. FLINT ratios subtract the same dataset’s empty-protocol median from the FLINT denominator. `cap` describes a killed child batch, including setup and warmup; it is not a lower bound on one timed call. Ratios require five successful repeats in both arms. These fixed comparator anchors do not attest an empirical complexity fit. The generic algorithm uses cubic modular elimination, quadratic matrix-vector work per lifting digit, and one elimination per cofactor image; zero skipping and sparse residual products benefit the structured fixture.

## hex-modular-matrix-divisor-prepared

Host `chungus2`, AMD EPYC 9455 48-Core Processor, CPU 20; Lean 4.34.0, python-flint 0.9.0. Protocol median 7.309 µs.

Load before `7.07 6.95 6.87 8/5910 850490`; after `8.89 8.16 7.39 16/5889 866430`. [Raw exports and fingerprints](data/hex-modular-matrix-divisor-prepared.json).

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
| structured | 384 | 8 | 0.1472 | — | — | — | — | — |

## hex-modular-matrix-solve-prepared

Host `chungus2`, AMD EPYC 9455 48-Core Processor, CPU 18; Lean 4.34.0, python-flint 0.9.0. Protocol median 7.306 µs.

Load before `7.07 6.95 6.87 9/5911 850489`; after `9.53 8.14 7.34 10/5885 863923`. [Raw exports and fingerprints](data/hex-modular-matrix-solve-prepared.json).

| Operation | n | Hex s | FLINT s | Hex / FLINT |
|---|---:|---:|---:|---:|
| decomposition | 32 | 0.004331 | — | — |
| integral | 32 | 0.0003134 | 0.0002991 | 1.07× |
| rational | 32 | 0.002279 | 0.0004133 | 5.61× |
| decomposition | 64 | 0.01943 | — | — |
| integral | 64 | 0.00171 | 0.001176 | 1.46× |
| rational | 64 | 0.01632 | 0.00175 | 9.36× |
| decomposition | 96 | 0.0593 | — | — |
| integral | 96 | 0.004885 | 0.002793 | 1.75× |
| rational | 96 | 0.05433 | 0.00404 | 13.47× |
| decomposition | 128 | 0.1339 | — | — |
| integral | 128 | 0.01098 | 0.005334 | 2.06× |
| rational | 128 | 0.1299 | 0.007771 | 16.73× |
| decomposition | 192 | 0.4515 | — | — |
| integral | 192 | 0.03658 | 0.01284 | 2.85× |
| rational | 192 | 0.4417 | 0.02223 | 19.87× |
| decomposition | 256 | 1.096 | — | — |
| integral | 256 | 0.0857 | 0.02571 | 3.33× |
| rational | 256 | 1.054 | 0.05515 | 19.11× |

## hex-modular-matrix-repeated-prepared

Host `chungus2`, AMD EPYC 9455 48-Core Processor, CPU 22; Lean 4.34.0, python-flint 0.9.0. Protocol median 7.337 µs.

Load before `7.07 6.95 6.87 8/5909 850491`; after `9.13 8.32 7.48 12/5934 869236`. [Raw exports and fingerprints](data/hex-modular-matrix-repeated-prepared.json).

| n | RHS count | Reused s | Independent s | Independent / reused |
|---:|---:|---:|---:|---:|
| 32 | 1 | 0.006567 | 0.006554 | 1.00× |
| 32 | 8 | 0.02162 | 0.05256 | 2.43× |
| 32 | 32 | 0.07278 | 0.2099 | 2.88× |
| 64 | 1 | 0.03598 | 0.03633 | 1.01× |
| 64 | 8 | 0.1499 | 0.2915 | 1.94× |
| 64 | 64 | 1.073 | 2.347 | 2.19× |
| 96 | 1 | 0.1134 | 0.1145 | 1.01× |
| 96 | 8 | 0.4929 | 0.9246 | 1.88× |
| 96 | 96 | cap (5/5) | cap (5/5) | — |
| 128 | 1 | 0.2653 | 0.2647 | 1.00× |
| 128 | 8 | 1.179 | — | — |

## Attribution

The final dimension-512 diagnostic uses 67 lifting digits. Its reduced denominator has 882 bits, leaving a 143-bit cofactor bound and five 31-bit images (155-bit CRT modulus). Decomposition took 79 ms, solve/reconstruction 92 ms, and cofactor reconstruction 93 ms in that diagnostic. [Stage output and host context](data/hex-modular-matrix-divisor-prepared-stages.json). These separate diagnostic timings do not replace the repeated comparator medians.

A pinned profile of the prepared divisor arm attributes 11.03% of self samples to closure application, 8.81% to reference-count cleanup, 8.07% to modular multiplication, 6.67% to array push, and 5.96% to the modular dot-product loop. It retained 211 samples with none reported lost. [Profile](data/hex-modular-matrix-divisor-prepared-profile.txt), [invocation and host](data/hex-modular-matrix-divisor-profile-host.json), [benchmark export](data/hex-modular-matrix-divisor-prepared-profile.json). The small-rung FLINT 5× target is missed: prime search and checked decomposition impose fixed costs. Under the SPEC’s first-measurement policy this is a recorded finding; it is not hidden by timing Bareiss in the divisor arm.

## Correctness and retained measurements

The full build and conformance suite verify single and multiple RHS solutions, normalisation, lifting congruences, strict digit bounds, zero-dimensional cases, composite moduli, unlucky initial primes, seeds, and forced exhaustion. FLINT checks 159 complete answers. Eight CI smoke anchors pin output hashes. Every completed common comparator result is checked for hash agreement by this report generator.

The reduction regression supplies `y = 3, d = 6` to the production cofactor route for `A = [2], b = [1]`. It must reduce to denominator two. Removing reduction from that route makes the assertion fail; the mutation was built locally. The prime reuse test checks the resulting CRT modulus, and a modulus sharing a factor with the reduced denominator is rejected before its determinant image is computed.

Earlier implementation measurements and profiles are retained below. The initial Gauss–Jordan pass cleared above each pivot immediately, destroying upper-factor sparsity. Forward elimination followed by backward clearing, determinant-only cofactor images, cached inverse rows, sparse integer products, and shorter prime prefixes remove that overhead. These observations motivated changes; their ratios are not controlled before/after evidence.

The earlier `divisor-final`, `solve`, and `repeated` datasets used functions whose pure preparation was moved into timed calls by Lean arity expansion. They therefore include fixture construction; `solve` also includes decomposition. They are retained as end-to-end diagnostics, not presented as separate `solveWith` costs. Early stage files’ `bound_ns` and `supply_ns` were similarly affected by code motion and are not used for attribution. The corrected stage diagnostic forces these values before reading the clock.

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
- [hex-modular-matrix-divisor-profile-host](data/hex-modular-matrix-divisor-profile-host.json)
- [hex-modular-matrix-divisor-profile](data/hex-modular-matrix-divisor-profile.json)
- [hex-modular-matrix-divisor-row-512](data/hex-modular-matrix-divisor-row-512.json)
- [hex-modular-matrix-divisor-sparse-profile](data/hex-modular-matrix-divisor-sparse-profile.json)
- [hex-modular-matrix-divisor-sparse-repeat-stages](data/hex-modular-matrix-divisor-sparse-repeat-stages.json)
- [hex-modular-matrix-divisor-sparse-stages](data/hex-modular-matrix-divisor-sparse-stages.json)
- [hex-modular-matrix-divisor-stages](data/hex-modular-matrix-divisor-stages.json)
- [hex-modular-matrix-divisor-supply-stages](data/hex-modular-matrix-divisor-supply-stages.json)
- [hex-modular-matrix-divisor-word-512](data/hex-modular-matrix-divisor-word-512.json)
- [hex-modular-matrix-image-counts](data/hex-modular-matrix-image-counts.json)
- [hex-modular-matrix-large-integers](data/hex-modular-matrix-large-integers.json)
- [hex-modular-matrix-profile](data/hex-modular-matrix-profile.json)
- [hex-modular-matrix-repeated](data/hex-modular-matrix-repeated.json)
- [hex-modular-matrix-smoke](data/hex-modular-matrix-smoke.json)
- [hex-modular-matrix-solve](data/hex-modular-matrix-solve.json)

Reproduce: `lake build hexmodularmatrix_bench`, then `HEX_FLINT_BENCH_PYTHON=<python-with-flint> python3 scripts/bench/modmat_flint.py <output.json> --mode divisor` (or `solve`, `repeated`). Render selected exports with `python3 scripts/bench/modmat_report.py <report.md> <exports...>`.
