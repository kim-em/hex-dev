# Polynomial Factorization Performance

This is the current performance snapshot for the polynomial-factorization
stack.

## Measurement environment

- Hex public, classical, and lattice implementation: exact-exponent/factor-only
  Hensel lift, guarded dominant-degree tree, remainder-only GCD,
  inverse-cached finite-field GCD, direct prime-power coefficient reduction,
  and monomial quadratic-division kernel at
  `0b95505b7c926911a9f487bac56676a8c7da48f6`
- Kernel diagnostic revision: `8c4acebc5fc04bd52b7ec2f6fa15c4f2eb4c6ece`
- Finite-field lower-layer revision:
  `f1ab9696cee5fac0cb8ea17bfdfd19caf63bd7c3`; Hensel and BZ use the final
  `0b95505b` revision above
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

Every current Hex export records a clean worktree. All affected lower-layer
ladders were refreshed in full rather than overlaid onto earlier rows. Rejected
broad-probe sweeps, a CPU-frequency-contaminated public sweep, and a measured
slower direct-array `modP` replacement are not used as current evidence.

## Headline outcome

The combined verified hot-path work makes the public dispatcher 3.11× faster
at the solved-row median (1.244 ms to 400.334 µs). Exact-exponent lifting,
omitting the unused final Bezout update, guarded tree, and shared GCD/Hensel
kernels preserve 373 of 392 solves while cutting p90 from 8.408 ms to
4.082 ms.

Against verified Isabelle BZ, the overhead-filtered eligible-row median falls
from 3.95× to 0.887× Hex/Isabelle. Hex wins 135 eligible rows and Isabelle
99. This is a real aggregate Hex lead but not yet a decisive margin; FLINT,
PARI/GP, and NTL remain much faster overall.

Eligibility uses each run's own measured protocol floor. The new public
service's floor is 16.975 µs, so the 234-row headline is stricter than the
preceding 13.650 µs export. Reapplying the lower old Hex floor gives a 0.836×
median over 243 rows; requiring both sides to clear the larger of the two
current floors gives 0.889× over 233 rows. On the preceding fixed 238-row
eligibility set, the current median is 0.870×. The direction of
the lead is therefore not an overhead-floor artifact, although its broad
0.454×–2.513× p10–p90 band still rules out a claim of uniform superiority.

## Integer-factorization corpus

| System | OK | Timeout | Median | p90 | Slowest solved |
|---|---:|---:|---:|---:|---:|
| Hex public factor | 373 | 19 | 400.334 µs | 4.082 ms | 9.047 s |
| Hex lattice | 369 | 23 | 1.812 ms | 87.886 ms | 9.590 s |
| Hex classical, no decline | 372 | 20 | 389.203 µs | 5.561 ms | 3.724 s |
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
| Hex public / Isabelle BZ | 234 | 0.887× | 0.454×–2.513× | 135 | 99 |
| Hex classical / Isabelle BZ | 229 | 0.913× | 0.464×–2.568× | 128 | 101 |
| Hex lattice / Isabelle LLL | 230 | 0.137× | 0.004×–2.437× | 182 | 48 |
| Hex public / Hex classical | 237 | 1.006× | 0.807×–1.128× | 109 | 128 |

The refreshed comparison resolves the apparent public/classical anomaly.
No-decline classical retains a 0.6% paired-median advantage: public/classical
is 1.006×, with a 109–128 win split. That is expected diagnostic overhead, not
a different lifting core: the no-decline entry omits bounded decline/fallback
behavior and the public final product check. Public improves selected hard rows
and alone solves `sd6`.

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
| `sd5_x_phi45` | 9.747 s | 129.024 ms | 75.54× faster |
| `xpow105_minus1` | 1.341 s | 46.196 ms | 29.03× faster |
| `cyclo_phi151` | 237.558 ms | 32.021 ms | 7.42× faster |
| `cyclo_phi179` | 317.151 ms | 44.752 ms | 7.09× faster |
| `cyclo_phi61` | 26.198 ms | 4.682 ms | 5.60× faster |
| `legendre_P30` | 173.071 ms | 13.970 ms | 12.39× faster |

`xpow120_minus1`, the principal downside sentinel, remains solved at
153.698 ms versus 173.545 ms previously. Every former false-probe regression
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
| `chebyshev_U24` | 7.664 ms | 3.049 ms | 2.51× |
| `legendre_P30` | 32.486 ms | 16.237 ms | 2.00× |
| `legendre_P38` | 37.858 ms | 15.528 ms | 2.44× |

Uncommitted diagnostic runs of the unrestricted policy were rejected after
large regressions on `legendre_P16`, `legendre_P28`, and `cyclo_phi385`.
Targeted A/B measurements led to the two guards above. The retained clean
corpus sweep is 0.989× at the paired median versus the preceding public export
over 247 overhead-eligible rows, while preserving the large structured wins.

## Shared GCD and Hensel kernels

The latest stage removes quotient construction when Euclidean GCD only needs a
remainder, caches finite-field divisor inverses, maps prime-power reduction
over the stored coefficient array with the modulus hoisted, and replaces
quadratic-Hensel multiplication by a monomial with an exact shift-and-scale
kernel. Every replacement is tied to a theorem equating it to the transparent
reference definition.

Against the immediately preceding `53bb12e2` public export, the all-row paired
median is 0.964× and current Hex wins 306 of 373 rows. With both runs above
their protocol floors, the ratio is 0.960× over 243 rows with a 205–38 win
split. The eligible family ratios are 0.815× for Chebyshev, 0.816× for
Legendre, 0.847× for random products, 0.949× for Laguerre, and at most 0.988×
for every other populated family. The gain is therefore broad rather than a
single-fixture dispatch effect.

## Hensel lifting

| Target | Largest rung | Median | Previous | Change |
|---|---:|---:|---:|---:|
| Linear step | 512 | 15.568 ms | 15.077 ms | 0.97× |
| Quadratic step | 512 | 8.481 ms | 128.731 ms | 15.2× faster |
| Iterated linear | `(192,64)` | 145.374 ms | 145.228 ms | 1.00× |
| Linear multifactor | `(192,64)` | 147.330 ms | 141.179 ms | 0.96× |
| Quadratic multifactor | `(192,64)` | 48.711 ms | 89.522 ms | 1.84× faster |

The packed UInt64/Montgomery polynomial kernels provide the large quadratic
step gain while transparent Lean definitions retain the proof surface. The
new prime-power reduction and monomial shift-and-scale kernel supply the later
quadratic-multifactor gain; the guarded tree is neutral on this equal-degree
registration. See `hex-hensel-performance.md` for the complete nine-target
table and the rejected `modP` A/B.

## Finite-field layers

| Target | Largest rung | Median | Verdict |
|---|---:|---:|---|
| Berlekamp matrix | 192 | 10.785 ms | consistent |
| Rabin irreducibility | 64 | 45.082 ms | consistent |
| Berlekamp factorization | 256 | 3.493 ms | consistent |
| Distinct-degree factorization | 96 | 190.362 ms | consistent |

Matrix construction is flat versus the preceding record, Rabin and DDF move by
3.4% and 1.8%, and the degree-256 Berlekamp-factor rung is 6.8% slower. The
retained Rabin/DDF FLINT exports include Hex timings from
`5c371a5a`; they show the external gap historically but are not relabelled as
exact current-Hex pairs. The same caveat applies to retained Hensel/FLINT
exports: current Hex values above are paired only with their prior Hex record.

The refreshed `HexPolyFp` upper rungs are 297.287 ms for Frobenius `X`,
43.570 µs for GCD, 668.277 ms for weighted product, 6.492 ms for square-free
decomposition, 337.743 ms for Frobenius power, 147.076 ms for power mod,
998.410 µs for division, and 376.752 ms for modular composition.

## Fixed integer fixtures

| Fixture / operation | Median | Previous |
|---|---:|---:|
| `X⁴ + 1`, public | 28.916 µs | 98.628 µs |
| `(X²-2)(X²-3)`, public | 27.071 µs | 27.154 µs |
| `Phi_15`, public | 86.801 µs | 205.705 µs |
| `SD_3`, modular split | 8.478 µs | 8.122 µs |
| `SD_3`, lattice | 1.593 ms | 2.596 ms |
| `SD_4`, lattice | 29.294 ms | 34.266 ms |

The parametric public degree-24 rung is 1.719 ms. All eight parametric BZ
ladders complete, though their deliberately conservative BHKS models remain
inconclusive on these small fixtures.

## Retained kernel and diagnostic evidence

The one-shot import and phase-attribution measurements below belong to the
revisions encoded in their artifact names. They remain useful localization
evidence but are not relabelled as current timings.

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

In the current persistent corpus service, public `sd5` takes 89.008 ms and
`sd6` completes in 9.047 s; the current isolated lattice entry takes 8.583 s
on `sd6`, while no-decline classical times out. The frontier result is only
9.5% below the cutoff and therefore has little margin.

## Six presentation graphs

- [Combined cactus](figures/hexbz-cactus-combined.svg)
- [Cyclotomic-products cactus](figures/hexbz-cactus-cyclotomic-products.svg)
- [Random-products runtime by degree](figures/hexbz-runtime-degree-random-products.svg)
- [Swinnerton-Dyer cactus](figures/hexbz-cactus-swinnerton-dyer.svg)
- [Swinnerton-Dyer runtime by degree](figures/hexbz-runtime-degree-swinnerton-dyer.svg)
- [Hoeij-Zimmermann cactus](figures/hexbz-cactus-hoeij-zimmermann.svg)

## Current artifacts

Fresh Hex exports under `reports/bench-results/`:

- `hex-poly-fp-f1ab9696-gcd-hensel-chungus2.json` (SHA-256
  `fcb72f342a3edb09cce09214101182765b9037e4ba12f46ea14e32360e8265c3`)
- `hex-berlekamp-f1ab9696-gcd-hensel-chungus2.json` (SHA-256
  `f26d75d214e6d107ee3e374891efcdc53faa7bad8e87bc71facce6867ab8fd18`)
- `hex-hensel-0b95505b-gcd-hensel-chungus2.json` (SHA-256
  `1ef93fd4fbf93109dcc19e9450935e90bc2d68affbe3d7ccc7902bd637a93f65`)
- `hex-berlekamp-zassenhaus-parametric-0b95505b-gcd-hensel-chungus2.json`
  (SHA-256
  `b915b2f27be36251cc8be6603858dbe29f5311502d00a030235351a9a1b1dd70`)
- `hex-berlekamp-zassenhaus-fixed-0b95505b-gcd-hensel-chungus2.json`
  (SHA-256
  `82ddd9e54cfafcfefc936ffeb1f1c8bb7e926e7545cd2b992ecfbc508e1ee78d`)
- `hexbz-factor-sweep-hex-0b95505b-gcd-hensel-final-chungus2.json`
  (current public, lattice, and no-decline classical; SHA-256
  `9f9f63ac9f35b3af6d35e530b085a1a1e47e7d03d958179d7597d7850e59c583`)

Historical stage-isolation artifacts remain in the same directory and are
linked from the corresponding exact-lift and guarded-tree sections above.

- `hexbz-kernel-factor-8c4acebc-chungus2.json` (SHA-256
  `0b2105264881c692ac5c91a8febf6d9f5d9a5a23170b01e525af6eadc27ebb97`)
- `berlekamp-diagnostic-a1fdbd81-chungus2.txt`
- `bz-spikes-b4b36754-exact-factor-only-chungus2.txt` (SHA-256
  `1e63599da4da285708b9ac2a6b06fbbb3986b7d418f3452b374682306b3f7efb`)

Unchanged external corpus exports retain their `5c371a5a` filenames: FLINT,
PARI, NTL, and Isabelle BZ/LLL. The two Berlekamp/FLINT and five Hensel/FLINT
exports also remain available, but their Hex half belongs to `5c371a5a` and is
used only as historical paired evidence.
