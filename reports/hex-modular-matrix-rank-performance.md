# Modular integer rank measurements

[Current raw samples](data/hex-modular-matrix-rank-shared-supply.json) compare
the checked modular producer (`rankCert? A 3`), the public dispatcher
(`rankModular`, eight-prime budget), hex-rank's direct integer algorithm,
and FLINT's `fmpz_mat.rank`. FLINT is informational: no speed threshold is
imposed by this milestone. The [initial 8–32 row samples](data/hex-modular-matrix-rank.json)
are also retained; their implementation regenerated the prime supply for each
determinant attempt. They are separate runs, not an adjacent before/after experiment.

The current inputs have 8, 16, 32, 64, 128 or 256 rows. Full-rank square inputs
are dense unimodular matrices. Rectangular inputs have four additional columns
and rank `n - 1` or `n / 2`, with identity leading factor blocks and large
remaining entries. The bad-prime family uses 256-bit factor entries and the
product of the first two primes from the actual producer supply.

Route checks confirm two rejected attempts and a successful certificate on
the third attempt for every bad-prime size. Every family also produces a
certificate at the public dispatcher's default budget, so none of those
measurements uses its direct-rank fallback. This is distinct from the selected
minor's determinant route: at the default budget, near-full and low-rank
fixtures reconstruct modularly, bad-prime fixtures use Bareiss, and full-rank
fixtures use Bareiss from 32 rows onward. The certificate producer deliberately
combines a modular profile, the ordinary modular/Bareiss determinant route and
Dixon adjugate solves. Fuel-exhaustion rank fallback is tested separately in
conformance and is not substituted for checked producer measurements.

Each arm uses five fixed repeats, a 0.2-second floor and discarded warmups.
Adjacent arms reverse order on alternate rungs. Every completed sample is
retained. The current process tree is pinned to automatically leased CPU 78
on `chungus2` (AMD EPYC 9455); host load before and after, executable and source
hashes, individual samples and route checks are in the raw artifact. Lean is
4.34.0 and python-flint is 0.9.0. All completed calls return the same rank at every point. Entries marked
`>10000 (cap)` exceeded the 10-second per-call operational limit on all five
repeats; those samples remain in the artifact and have no timing median. Times below are host-specific median milliseconds, including FLINT
transport and conversion; the empty FLINT transport median is 0.0061 ms.

| Family | Rows | Rank | Certificate | Public | Direct integer | FLINT |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Full | 8 | 8 | 7.3217 | 18.8118 | 0.0129 | 0.0165 |
| Near | 8 | 7 | 7.0572 | 18.4325 | 0.0173 | 0.0191 |
| Low | 8 | 4 | 6.9080 | 18.2844 | 0.0115 | 0.0199 |
| BadPrimes | 8 | 4 | 7.9896 | 19.7828 | 0.0660 | 2.1773 |
| Full | 16 | 16 | 8.7900 | 20.5751 | 0.0908 | 0.0447 |
| Near | 16 | 15 | 7.4942 | 18.4487 | 0.1074 | 0.0454 |
| Low | 16 | 8 | 7.1381 | 18.4595 | 0.0661 | 0.0495 |
| BadPrimes | 16 | 8 | 10.5283 | 22.2785 | 0.5078 | 6.5351 |
| Full | 32 | 32 | 21.8063 | 37.1494 | 0.6742 | 0.1609 |
| Near | 32 | 31 | 10.0235 | 21.0369 | 0.7453 | 0.1382 |
| Low | 32 | 16 | 8.1750 | 19.4681 | 0.4325 | 0.1645 |
| BadPrimes | 32 | 16 | 24.8623 | 36.8429 | 4.6873 | 22.7354 |
| Full | 64 | 64 | 155.1195 | 192.6259 | 5.2491 | 0.6557 |
| Near | 64 | 63 | 27.7218 | 38.9475 | 5.5034 | 0.4891 |
| Low | 64 | 32 | 14.9246 | 26.4031 | 3.0903 | 0.6207 |
| BadPrimes | 64 | 32 | 137.5125 | 150.8033 | 57.7289 | 85.5211 |
| Full | 128 | 128 | 1770.9351 | 1967.7711 | 40.8720 | 2.9515 |
| Near | 128 | 127 | 160.4159 | 173.3136 | 42.4127 | 1.8640 |
| Low | 128 | 64 | 64.7020 | 76.5646 | 23.3594 | 2.5872 |
| BadPrimes | 128 | 64 | 1231.2717 | 1243.5382 | 934.8876 | 334.8961 |
| Full | 256 | 256 | >10000 (cap) | >10000 (cap) | 318.0350 | 14.6352 |
| Near | 256 | 255 | 1212.1809 | 1234.2805 | 333.6135 | 7.3210 |
| Low | 256 | 128 | 462.1639 | 474.5570 | 184.8402 | 11.7547 |
| BadPrimes | 256 | 128 | >10000 (cap) | >10000 (cap) | >10000 (cap) | 1327.8747 |

The direct integer algorithm is faster at every point with complete Hex
timings. The 256-row bad-prime fixture exceeds the cap for all three Hex
arms, so that point establishes no ordering between them. These inputs
establish no crossover in favour of modular rank. The public dispatcher and
the three-prime certificate arm
have different search budgets, including eagerly generated prime supplies
and per-attempt determinant budgets; their times should not be read as
certificate-checking overhead alone. Each call generates its supply once and
shares it across its determinant attempts. The dispatcher retains the SPEC's
modular-first policy and total integer fallback; no size threshold is inferred
from families that show no modular advantage.

Reproduce with `lake build hexmodularmatrix_bench`, then
`HEX_FLINT_BENCH_PYTHON=<python-with-flint> python3 scripts/bench/modmat_flint.py
<output.json> --mode rank`. `hexmodularmatrix_bench rank-routes` checks bad-prime
recovery, default certification and determinant routes; `hexmodularmatrix_bench
verify` runs the bounded smoke checks used in CI.
