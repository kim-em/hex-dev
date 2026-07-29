# Polynomial Factorization Performance

This is the current performance snapshot for the polynomial-factorization
stack.

## Measurement environment

- Hex public-factor revision: `567b5aea0c22d13fcf43541b5371717823870999`
- Lower-layer Hex revision: `a1fdbd81ef038faa41765fb39a79cd083109c8ed`
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

The fresh public-factor export records a clean worktree at `567b5aea`. This
revision changes prime selection only, so the finite-field, Hensel, fixed BZ,
and kernel exports from `a1fdbd81` remain current lower-layer evidence. Rejected
broad-probe sweeps are not retained.

## Headline outcome

The combined verified hot-path work makes the public dispatcher 2.80× faster
at the solved-row median (1.244 ms to 443.618 µs). The latest bounded
prime-width policy preserves 373 of 392 solves while accelerating the hardest
affected rows by 3.49×–71.43×.

Against verified Isabelle BZ, the overhead-filtered eligible-row median falls
from 3.95× to 0.996× Hex/Isabelle. Hex wins 123 eligible rows and Isabelle
121. This is a narrow aggregate Hex victory, not a decisive margin; FLINT,
PARI/GP, and NTL remain much faster overall.

## Integer-factorization corpus

| System | OK | Timeout | Median | p90 | Slowest solved |
|---|---:|---:|---:|---:|---:|
| Hex public factor | 373 | 19 | 443.618 µs | 8.408 ms | 9.161 s |
| Hex lattice | 366 | 26 | 1.864 ms | 89.351 ms | 9.612 s |
| Hex classical, no decline | 371 | 21 | 424.409 µs | 9.484 ms | 3.918 s |
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
| Hex public / Isabelle BZ | 244 | 0.996× | 0.47×–3.04× | 123 | 121 |
| Hex classical / Isabelle BZ | 231 | 1.26× | 0.50×–3.39× | 92 | 139 |
| Hex lattice / Isabelle LLL | 228 | 0.15× | 0.004×–2.55× | 175 | 53 |
| Hex public / Hex classical | 239 | 0.989× | 0.68×–1.08× | 141 | 98 |

Public dispatch now wins most common eligible rows while adding
`sd5_x_phi45` and `sd6`. The old pattern—classical nearly always winning—was
repeated setup and avoidable hot-path work, not the intrinsic price of the
verified public API.

## Bounded prime-width selection

The shared lifting selector now inspects at most two further good primes on
high-cost transforms and adopts a choice only after at least a 25% modular
factor-count reduction. It also recognizes prime all-one cyclotomics and avoids
speculative probes on even `x^n - 1`, whose difference-of-squares recursion is
already cheap.

| Corpus row | Previous Hex | Current Hex | Change |
|---|---:|---:|---:|
| `sd5_x_phi45` | 9.747 s | 136.466 ms | 71.43× faster |
| `xpow105_minus1` | 1.341 s | 54.357 ms | 24.67× faster |
| `cyclo_phi151` | 237.558 ms | 31.654 ms | 7.50× faster |
| `cyclo_phi179` | 317.151 ms | 43.814 ms | 7.24× faster |
| `cyclo_phi61` | 26.198 ms | 4.762 ms | 5.50× faster |
| `legendre_P30` | 173.071 ms | 49.550 ms | 3.49× faster |

`xpow120_minus1`, the principal downside sentinel, remains solved at
164.987 ms versus 173.545 ms previously. Every former false-probe regression
on composite/sparse cyclotomics returned to baseline.

## Hensel lifting

| Target | Largest rung | Median | Previous | Change |
|---|---:|---:|---:|---:|
| Linear step | 512 | 15.089 ms | 15.077 ms | 1.00× |
| Quadratic step | 512 | 8.681 ms | 128.731 ms | 14.8× faster |
| Iterated linear | `(192,64)` | 142.543 ms | 145.228 ms | 1.02× faster |
| Linear multifactor | `(192,64)` | 143.939 ms | 141.179 ms | 0.98× |
| Quadratic multifactor | `(192,64)` | 89.522 ms | 145.140 ms | 1.62× faster |

The packed UInt64/Montgomery polynomial kernels provide the large quadratic
gain while transparent Lean definitions retain the proof surface. Required
borrow annotations keep repeated quadratic runs flat at 65–69 MiB RSS. See
`hex-hensel-performance.md` for the complete nine-target table.

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
| `X⁴ + 1`, public | 30.569 µs | 98.628 µs |
| `(X²-2)(X²-3)`, public | 28.735 µs | 27.154 µs |
| `Phi_15`, public | 90.301 µs | 205.705 µs |
| `SD_3`, modular split | 8.420 µs | 8.122 µs |
| `SD_3`, lattice | 1.613 ms | 2.596 ms |
| `SD_4`, lattice | 29.580 ms | 34.266 ms |

The parametric public degree-24 rung is 2.261 ms. All eight parametric BZ
ladders complete, though their deliberately conservative BHKS models remain
inconclusive on these small fixtures.

## Kernel and diagnostic evidence

Fresh-module factorization import baseline is 877.587 ms and certificate
baseline is 6.243 s. Direct kernel factorization takes 1.316 s on `quartic_a4`,
1.058 s on `cyclo_phi5`, and 1.614 s on `xpow6_minus1`; all expected checks
complete within 30 seconds with zero unexpected errors. Direct kernel times
improve over the preceding record, but the certificate umbrella and tactic
totals regress by about 35%; `hexbz-kernel-factor.md` records both sides.

At split degree 24, the compiled Berlekamp diagnostic records 16.387 ms for a
kernel-rebuilding baseline, 1.245 ms with the kernel shared, and 569.224 µs for
the fixed path. The fixed path is 18.89% matrix, 2.95% nullspace, and 78.17%
witness split. Balanced product construction remains neutral.

The earlier single-shot hybrid seam reaches `SD_5` in 96.895 ms through the
classical tier and `SD_6` in 9.087 s after a lattice decline; the lattice core
alone takes 8.492 s. In the current persistent corpus service, public `sd5`
takes 95.846 ms and `sd6` completes in 9.161 s—only 8.4% below the cutoff, so
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
- `hexbz-factor-sweep-hex-567b5aea-chungus2.json` (SHA-256
  `f3bf572df064788203da76fcb5ede2a20e376bb2fa2ff448c4bc2d244157bd63`)
- `hexbz-kernel-factor-a1fdbd81-chungus2.json`
- `berlekamp-diagnostic-a1fdbd81-chungus2.txt`
- `bz-spikes-a1fdbd81-chungus2.txt`

Unchanged external corpus exports retain their `5c371a5a` filenames: FLINT,
PARI, NTL, and Isabelle BZ/LLL. The two Berlekamp/FLINT and five Hensel/FLINT
exports also remain available, but their Hex half belongs to `5c371a5a` and is
used only as historical paired evidence.
