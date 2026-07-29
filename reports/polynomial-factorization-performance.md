# Polynomial Factorization Performance

This is the current performance snapshot for the polynomial-factorization
stack.

## Measurement environment

- Hex public-factor implementation: exact-exponent/factor-only Hensel lift and
  guarded dominant-degree tree at
  `a087b28f6ce4adb8c109542abb7a050633e8ca3b`
- Hex classical/lattice revision: `aaabcf1520121b4acaa793811c8567dddcf39f1f`
- Kernel diagnostic revision: `8c4acebc5fc04bd52b7ec2f6fa15c4f2eb4c6ece`
- Unchanged fixed and lower-layer Hex revision:
  `a1fdbd81ef038faa41765fb39a79cd083109c8ed`; changed BZ/Hensel targets use
  the guarded-tree overlays recorded below
- Hex date: 2026-07-29
- External-comparator date/revision: 2026-07-28 / `5c371a5a`
- Host: `chungus2`, AMD EPYC 9455, Linux x86-64
- Lean: `leanprover/lean4:v4.32.0-rc1`
- External libraries: python-flint 0.9.0; PARI/GP 2.17.3 through
  cypari2 2.2.4; NTL 11.6.0; Isabelle2025-2 with AFP 2026-05-29
- CPU placement: all timing commands pinned with `taskset -c 0`
- Corpus: 392 instances, SHA-256
  `619913904240834c912489e6cc23ba136e8cc5ebf0ea95f83397e0682387284d`,
  10-second cutoff, no early termination

The FLINT, PARI/GP, NTL, and Isabelle corpus services were already current and
were not rerun because this revision changes only Hex. Their exports use the
same host, corpus, CPU, and persistent-line protocol as the fresh Hex sweep.
Exact paired ratios are reported only where those conditions match.

The classical/lattice, kernel, and fresh public-factor exports record clean
worktrees. The finite-field and unchanged BZ
exports from `a1fdbd81` remain current; affected BZ registrations have focused
overlays from the new implementation. Rejected
broad-probe sweeps and a CPU-frequency-contaminated public sweep are not
retained.

The `a1fdbd81` exports themselves record a dirty worktree: they executed with
the native-kernel borrow annotations that were pending at measurement time and
then merged unchanged in `f38614c1`. They are the measured pre-prime-policy
runtime, not a checkout missing that ownership fix.

## Headline outcome

The combined verified hot-path work makes the public dispatcher 2.87× faster
at the solved-row median (1.244 ms to 432.972 µs). Exact-exponent lifting,
omitting the unused final Bezout update, and the guarded tree preserve 373 of
392 solves while cutting p90 from 8.408 ms to 5.437 ms.

Against verified Isabelle BZ, the overhead-filtered eligible-row median falls
from 3.95× to 0.927× Hex/Isabelle. Hex wins 126 eligible rows and Isabelle
112. This is a real aggregate Hex lead but not yet a decisive margin; FLINT,
PARI/GP, and NTL remain much faster overall.

Eligibility uses each run's own measured protocol floor. The new public
service's floor is 16.945 µs, so the 238-row headline is stricter than the
preceding 13.650 µs export's 244-row comparison. Reapplying the lower old Hex
floor gives a 0.899× median over 244 rows; requiring both sides to clear the
larger of the two current floors gives 0.942× over 236 rows. The direction of
the lead is therefore not an overhead-floor artifact, although its broad
0.48×–2.77× p10–p90 band still rules out a claim of uniform superiority.

## Integer-factorization corpus

| System | OK | Timeout | Median | p90 | Slowest solved |
|---|---:|---:|---:|---:|---:|
| Hex public factor | 373 | 19 | 432.972 µs | 5.437 ms | 8.895 s |
| Hex lattice | 369 | 23 | 1.957 ms | 91.186 ms | 10.000 s |
| Hex classical, no decline | 372 | 20 | 423.939 µs | 9.029 ms | 3.845 s |
| FLINT | 391 | 1 | 66.850 µs | 1.184 ms | 1.228 s |
| PARI/GP | 391 | 1 | 99.958 µs | 1.254 ms | 823.201 ms |
| NTL | 391 | 1 | 135.631 µs | 2.714 ms | 1.919 s |
| Verified Isabelle BZ | 371 | 21 | 441.134 µs | 5.128 ms | 8.363 s |
| Verified Isabelle LLL | 314 | 78 | 6.109 ms | 1.219 s | 9.528 s |

Every returned Hex factor-degree multiset with a committed corpus oracle
matched it. Hex times out on every Hoeij-Zimmermann row, so it contributes no
new factor-count result on the seven rows without a committed oracle; the
retained FLINT, PARI/GP, and NTL results agree there.

With both sides at least 10× above protocol overhead:

| Pair | Eligible | Median | p10–p90 | First faster | Second faster |
|---|---:|---:|---:|---:|---:|
| Hex public / Isabelle BZ | 238 | 0.927× | 0.48×–2.77× | 126 | 112 |
| Hex classical / Isabelle BZ | 231 | 1.21× | 0.48×–3.22× | 93 | 138 |
| Hex lattice / Isabelle LLL | 230 | 0.15× | 0.004×–2.25× | 176 | 54 |
| Hex public / Hex classical | 238 | 0.992× | 0.45×–1.10× | 125 | 113 |

The refreshed comparison resolves the apparent public/classical anomaly.
Before this change, no-decline classical won most ordinary rows because public
paid about 1.5% for tier selection while both routes shared the same lifting
work. Exact-exponent and factor-only lifting affects the production public path
where that work matters most: public and classical are now tied at the paired
median (0.992×), public wins 125 of 238 eligible rows, and it alone solves
`sd6`. The classical entry remains useful as an isolated baseline, but it no
longer beats public systematically.

## Bounded prime-width selection and cumulative gains

The shared lifting selector now inspects at most two further good primes on
high-cost transforms and adopts a choice only after at least a 25% modular
factor-count reduction. It also recognizes prime all-one cyclotomics and avoids
speculative probes on even `x^n - 1`, whose difference-of-squares recursion is
already cheap. The table compares the pre-policy export with the current
implementation, so its current column includes both the selector improvement
and the exact/factor-only Hensel improvement isolated in the following section.

| Corpus row | Previous Hex | Current Hex | Change |
|---|---:|---:|---:|
| `sd5_x_phi45` | 9.747 s | 132.013 ms | 73.83× faster |
| `xpow105_minus1` | 1.341 s | 47.148 ms | 28.44× faster |
| `cyclo_phi151` | 237.558 ms | 31.459 ms | 7.55× faster |
| `cyclo_phi179` | 317.151 ms | 44.316 ms | 7.16× faster |
| `cyclo_phi61` | 26.198 ms | 4.783 ms | 5.48× faster |
| `legendre_P30` | 173.071 ms | 32.486 ms | 5.33× faster |

`xpow120_minus1`, the principal downside sentinel, remains solved at
159.898 ms versus 173.545 ms previously. Every former false-probe regression
on composite/sparse cyclotomics returned to baseline.

## Exact production Hensel lift

The production lift now recurses through `ceil(k / 2)` and reduces at every
level, reaching exponent `k` exactly instead of overshooting to the next
power of two. Its final correction computes only the two factors: the public
theorem proves that pair equal to projecting the full factor-and-Bezout result.

| Corpus row | Pre-change public | Exact/factor-only public | Speedup |
|---|---:|---:|---:|
| `conway_p2_n38` | 8.103 ms | 2.988 ms | 2.71× |
| `chebyshev_U24` | 8.724 ms | 7.664 ms | 1.14× |
| `legendre_P30` | 49.550 ms | 32.486 ms | 1.53× |
| `legendre_P38` | 48.032 ms | 37.858 ms | 1.27× |
| `xpow105_minus1` | 54.357 ms | 47.148 ms | 1.15× |

In the retained warmed same-day A/B, omitting only the final Bezout update
improves the all-row paired median by 2.48% and is faster on 283 of 373 rows.
The exact-only side is
`hexbz-factor-sweep-hex-b4b36754-exact-only-chungus2.json` (SHA-256
`4ceadcbb1dd54f7e49d77efdd3ed199cb84633fb54c733a6041afa2118ddf9b2`).
The exact schedule supplies the larger structured-row gains. Chebyshev and
Legendre remain the clearest optimization targets despite that progress.

## Guarded Hensel tree and recursive relift

The multifactor lifter now keeps its count-halving tree unless one modular
factor exceeds half the node degree. Only then does it choose the prefix with
the smallest degree imbalance, avoiding an expensive recursive lift that pairs
the dominant factor with small neighbours. The recursive recombination tier
uses a full sub-floor doubling ladder only on count-balanced four-factor nodes
above precision 300; other wide nodes retain the single cheap probe.

| Corpus row | Exact/factor-only | Guarded tree | Speedup |
|---|---:|---:|---:|
| `chebyshev_U24` | 7.664 ms | 3.099 ms | 2.47× |
| `legendre_P30` | 32.486 ms | 16.483 ms | 1.97× |
| `legendre_P38` | 37.858 ms | 15.842 ms | 2.39× |

Uncommitted diagnostic runs of the unrestricted policy were rejected after
large regressions on `legendre_P16`, `legendre_P28`, and `cyclo_phi385`.
Targeted A/B measurements led to the two guards above; the retained clean corpus sweep is neutral at the paired median
versus the preceding public export (1.001× over 247 overhead-eligible rows),
while preserving the large structured wins.

## Hensel lifting

| Target | Largest rung | Median | Previous | Change |
|---|---:|---:|---:|---:|
| Linear step | 512 | 15.089 ms | 15.077 ms | 1.00× |
| Quadratic step | 512 | 8.681 ms | 128.731 ms | 14.8× faster |
| Iterated linear | `(192,64)` | 142.543 ms | 145.228 ms | 1.02× faster |
| Linear multifactor | `(192,64)` | 143.939 ms | 141.179 ms | 0.98× |
| Quadratic multifactor | `(192,64)` | 67.229 ms | 89.522 ms | 1.33× faster |

The packed UInt64/Montgomery polynomial kernels provide the large quadratic
step gain while transparent Lean definitions retain the proof surface. The
exact/factor-only schedule supplies the quadratic-multifactor gain; the guarded
tree is neutral on this equal-degree registration. Required borrow annotations keep the refreshed quadratic-multifactor
target flat at 61–66 MiB RSS. See `hex-hensel-performance.md` for the complete
nine-target table.

## Finite-field layers

| Target | Largest rung | Median | Verdict |
|---|---:|---:|---|
| Berlekamp matrix | 192 | 10.791 ms | consistent |
| Rabin irreducibility | 64 | 43.606 ms | consistent |
| Berlekamp factorization | 256 | 3.271 ms | consistent |
| Distinct-degree factorization | 96 | 187.058 ms | consistent |

The finite-field factorization headlines are within 2% of the preceding
record. The retained Rabin/DDF FLINT exports include Hex timings from
`5c371a5a`; they show the external gap historically but are not relabelled as
exact current-Hex pairs. The same caveat applies to retained Hensel/FLINT
exports: current Hex values above are paired only with their prior Hex record.

The refreshed `HexPolyFp` upper rungs are 297.714 ms for Frobenius `X`,
45.104 µs for GCD, 659.711 ms for weighted product, 6.569 ms for square-free
decomposition, 339.451 ms for Frobenius power, 148.786 ms for power mod,
960.070 µs for division, and 372.371 ms for modular composition. An A/B/A
control rejected an initially contaminated sample before this export.

## Fixed integer fixtures

| Fixture / operation | Median | Previous |
|---|---:|---:|
| `X⁴ + 1`, public | 31.525 µs | 98.628 µs |
| `(X²-2)(X²-3)`, public | 29.363 µs | 27.154 µs |
| `Phi_15`, public | 91.796 µs | 205.705 µs |
| `SD_3`, modular split | 8.420 µs | 8.122 µs |
| `SD_3`, lattice | 1.583 ms | 2.596 ms |
| `SD_4`, lattice | 29.299 ms | 34.266 ms |

The parametric public degree-24 rung is 1.786 ms. All eight parametric BZ
ladders complete, though their deliberately conservative BHKS models remain
inconclusive on these small fixtures.

## Kernel and diagnostic evidence

Fresh-module factorization import baseline is 897.900 ms and the certificate
baseline is 6.407 s. Direct kernel factorization takes 1.343 s on `quartic_a4`,
1.078 s on `cyclo_phi5`, and 1.694 s on `xpow6_minus1`; all expected checks
complete within 30 seconds with zero unexpected errors. These one-shot totals
and both import baselines are within 2–5% of the preceding export, so the cheap
selector guard adds no visible kernel-level discontinuity;
`hexbz-kernel-factor.md` records every sample.

At split degree 24, the compiled Berlekamp diagnostic records 16.387 ms for a
kernel-rebuilding baseline, 1.245 ms with the kernel shared, and 569.224 µs for
the fixed path. The fixed path is 18.89% matrix, 2.95% nullspace, and 78.17%
witness split. Balanced product construction remains neutral.

The current single-shot hybrid seam reaches `SD_5` in 100.706 ms through the
classical tier and `SD_6` in 9.132 s after a lattice decline; the lattice core
alone takes 8.257 s. In the current persistent corpus service, public `sd5`
takes 90.052 ms and `sd6` completes in 8.895 s—only 11.1% below the cutoff, so
that frontier result has little margin.

## Six presentation graphs

- [Combined cactus](figures/hexbz-cactus-combined.svg)
- [Cyclotomic-products cactus](figures/hexbz-cactus-cyclotomic-products.svg)
- [Random-products runtime by degree](figures/hexbz-runtime-degree-random-products.svg)
- [Swinnerton-Dyer cactus](figures/hexbz-cactus-swinnerton-dyer.svg)
- [Swinnerton-Dyer runtime by degree](figures/hexbz-runtime-degree-swinnerton-dyer.svg)
- [Hoeij-Zimmermann cactus](figures/hexbz-cactus-hoeij-zimmermann.svg)

## Current artifacts

Fresh Hex exports under `reports/bench-results/`:

- `hex-poly-fp-a1fdbd81-chungus2.json`
- `hex-berlekamp-a1fdbd81-chungus2.json`
- `hex-hensel-a1fdbd81-chungus2.json`
- `hex-berlekamp-zassenhaus-parametric-a1fdbd81-chungus2.json`
- `hex-berlekamp-zassenhaus-fixed-a1fdbd81-chungus2.json`
- `hex-berlekamp-zassenhaus-parametric-a484ef54-guarded-tree-overlay-chungus2.json`
  (five changed targets; SHA-256
  `c6a0db5c4f091ef43eda515e08c1ad1c7a68af136bcf97c93df932a1f38d4ea3`)
- `hex-berlekamp-zassenhaus-fixed-daf361c6-guarded-tree-overlay-chungus2.json`
  (five changed targets; SHA-256
  `216a6ed79e7c10802d9ad7e55687cc27ef6b929c5b30994f7872b373034acede`)
- `hexbz-factor-sweep-hex-a087b28f-guarded-tree-chungus2.json` (SHA-256
  `1f03e479ca0d14bedb11a68960da865760072a66b7299d33ee3acd19138bf1e7`)
- `hexbz-factor-sweep-hex-b4b36754-exact-factor-only-chungus2.json`
  (preceding A/B reference; SHA-256
  `090b594a14b12af8332fef091d2bd8ca5652c3e7566e6bd452a984eb473a058a`)
- `hexbz-factor-sweep-hex-b4b36754-exact-only-chungus2.json` (same-day A/B
  reference; SHA-256
  `4ceadcbb1dd54f7e49d77efdd3ed199cb84633fb54c733a6041afa2118ddf9b2`)
- `hex-hensel-quadratic-multifactor-478c3ccc-guarded-tree-chungus2.json`
  (changed target only; SHA-256
  `753540d532379ec5f32932d0ce17830a4bae135edd8ec9276e544b3a35b27b15`)
- `hexbz-factor-sweep-hex-aaabcf15-chungus2.json` (SHA-256
  `30e56da9aa3c6f4f50faca4ef19e5c4d4f6523362542f2d8967ca7665f62f747`)
- `hexbz-kernel-factor-8c4acebc-chungus2.json` (SHA-256
  `0b2105264881c692ac5c91a8febf6d9f5d9a5a23170b01e525af6eadc27ebb97`)
- `berlekamp-diagnostic-a1fdbd81-chungus2.txt`
- `bz-spikes-b4b36754-exact-factor-only-chungus2.txt` (SHA-256
  `1e63599da4da285708b9ac2a6b06fbbb3986b7d418f3452b374682306b3f7efb`)

Unchanged external corpus exports retain their `5c371a5a` filenames: FLINT,
PARI, NTL, and Isabelle BZ/LLL. The two Berlekamp/FLINT and five Hensel/FLINT
exports also remain available, but their Hex half belongs to `5c371a5a` and is
used only as historical paired evidence.
