# Modular integer rank measurements

[Raw samples](data/hex-modular-matrix-rank.json) compare the checked modular
producer (`rankCert? A 3`), the public dispatcher (`rankModular`, eight-prime
budget), hex-rank's direct integer algorithm, and FLINT's `fmpz_mat.rank`.
FLINT is informational: no speed threshold is imposed by this milestone.

The inputs have 8, 16 or 32 rows. Full-rank square inputs are dense
unimodular matrices. Rectangular inputs have four additional columns and
rank `n - 1` or `n / 2`, with identity leading factor blocks and large
remaining entries. The bad-prime family uses 256-bit factor entries and the
product of the first two primes from the actual producer supply. Route
checks confirm two rejected attempts and a successful certificate on the
third attempt at all three sizes. Fuel-exhaustion fallback is tested separately
in conformance and is not substituted for the checked producer measurements.

Each arm uses five fixed repeats, a 0.2-second floor and discarded warmups.
Adjacent arms reverse order on alternate rungs. Every completed sample is
retained. The process tree is pinned to automatically leased CPU 93 on
`chungus2` (AMD EPYC 9455); host load before and after, executable and source
hashes, individual samples and route checks are in the raw artifact. Lean is
4.34.0 and python-flint is 0.9.0. Times below are
host-specific median milliseconds, including FLINT transport and conversion;
the empty FLINT transport median is 0.0065 ms.

| Family | Rows | Rank | Certificate | Public | Direct integer | FLINT |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Full | 8 | 8 | 14.8524 | 38.2205 | 0.0128 | 0.0167 |
| Near | 8 | 7 | 14.0001 | 36.6164 | 0.0172 | 0.0194 |
| Low | 8 | 4 | 13.8649 | 36.8670 | 0.0114 | 0.0201 |
| BadPrimes | 8 | 4 | 29.4526 | 76.5144 | 0.0664 | 2.1805 |
| Full | 16 | 16 | 15.9551 | 39.4679 | 0.0891 | 0.0452 |
| Near | 16 | 15 | 14.2905 | 37.1924 | 0.1062 | 0.0457 |
| Low | 16 | 8 | 14.1324 | 36.8100 | 0.0655 | 0.0496 |
| BadPrimes | 16 | 8 | 32.1371 | 79.5194 | 0.5111 | 6.6176 |
| Full | 32 | 32 | 28.6811 | 55.5121 | 0.6612 | 0.1630 |
| Near | 32 | 31 | 17.1333 | 39.2744 | 0.7233 | 0.1396 |
| Low | 32 | 16 | 15.2594 | 37.6214 | 0.4308 | 0.1663 |
| BadPrimes | 32 | 16 | 45.9045 | 93.3368 | 4.7236 | 22.9820 |

The direct integer algorithm is faster than the modular producer at every
measured point. These inputs establish no crossover in favour of modular rank.
The public dispatcher and the three-prime certificate arm have different
search budgets, including eagerly generated prime supplies and per-attempt
determinant budgets; their times should not be read as certificate-checking
overhead alone. The public dispatcher retains the SPEC's modular-first policy
and total integer fallback.

Reproduce with `lake build hexmodularmatrix_bench`, then
`HEX_FLINT_BENCH_PYTHON=<python-with-flint> python3 scripts/bench/modmat_flint.py
<output.json> --mode rank`. `hexmodularmatrix_bench rank-routes` checks the
bad-prime recovery path; `hexmodularmatrix_bench verify` runs the bounded smoke
checks used in CI.
