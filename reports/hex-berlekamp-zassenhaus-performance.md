# HexBerlekampZassenhaus Performance Report

The current public-factor, classical, and lattice corpus measurements cover the
exact-exponent, factor-only Hensel implementation and guarded dominant-degree
tree at `53bb12e21c5107e9da5d837c207eb3254238967f`. The five affected
parametric and five affected fixed registrations were refreshed on the same
runtime; the three unchanged registrations in each table and unchanged
lower-layer measurements remain from
`a1fdbd81ef038faa41765fb39a79cd083109c8ed`. All were measured 2026-07-29 on
`chungus2` (AMD EPYC 9455, Linux x86-64), pinned to CPU 0.

## Bench Targets

Eight parametric targets cover public factorization, the exhaustive backstop,
degree/height, fallback behaviour, and fast-path precision/local-factor axes.
Eight canonical adversarial fixtures are warm fixed benchmarks. All parametric
targets completed three outer trials; their classical BHKS upper-bound models
are loose on these small deterministic fixtures, so the verdicts are
inconclusive rather than failed.

| Target | Largest rung | Median |
|---|---:|---:|
| Public factorization | 24 | 1.786 ms |
| Fallback probe | 24 | 1.558 ms |
| Degree/height | `(6,32)` | 212.853 µs |
| Fast-path precision/local | `(8,32,128,8)` | 1.512 ms |
| Slow factorization | 4 | 12.564 µs |
| Slow degree/height | `(3,8)` | 30.827 µs |
| Public compare domain | 4 | 74.800 µs |
| Slow compare domain | 4 | 12.577 µs |

| Warm fixed fixture | Median | Min–max |
|---|---:|---:|
| `X⁴ + 1`, public | 31.525 µs | 31.348–31.960 µs |
| `X⁴ + 1`, fast setup | 20.751 µs | 20.487–20.800 µs |
| `(X²-2)(X²-3)`, public | 29.363 µs | 29.239–29.456 µs |
| `Phi_15`, public | 91.796 µs | 91.466–92.082 µs |
| `Phi_15`, fast setup | 25.862 µs | 25.718–25.967 µs |
| `SD_3`, modular split | 8.420 µs | 8.243–8.568 µs |
| `SD_3`, lattice factorization | 1.583 ms | 1.578–1.615 ms |
| `SD_4`, lattice factorization | 29.299 ms | 29.128–29.602 ms |

The public `X⁴+1` fixed fixture falls from 98.628 µs to 31.525 µs and
`Phi_15` from 205.705 µs to 91.796 µs. Quadratic multifactor Hensel lifting,
reported separately, is the largest lower-layer improvement.

Exports under `reports/bench-results/`:

- `hex-berlekamp-zassenhaus-parametric-a1fdbd81-chungus2.json`
  (SHA-256
  `6e1c8e966b178f2ebadfbeec1a5283ab044fa0125f99ed9a9a2326b133da79ee`)
- `hex-berlekamp-zassenhaus-fixed-a1fdbd81-chungus2.json`
  (SHA-256
  `49acf7761bc6df09e1192761989f85f3f8acb21733de85d8d01383152951141f`)
- `hex-berlekamp-zassenhaus-parametric-a484ef54-guarded-tree-overlay-chungus2.json`
  (five changed targets; SHA-256
  `c6a0db5c4f091ef43eda515e08c1ad1c7a68af136bcf97c93df932a1f38d4ea3`)
- `hex-berlekamp-zassenhaus-fixed-daf361c6-guarded-tree-overlay-chungus2.json`
  (five changed targets; SHA-256
  `216a6ed79e7c10802d9ad7e55687cc27ef6b929c5b30994f7872b373034acede`)

`list` and every non-scheduled `verify` target passed.

The `a1fdbd81` JSON exports record a dirty worktree because the
borrowed-argument fix and their reports were pending together. The new overlay
exports record clean worktrees. The hashes above identify both measured states
exactly.

## Cross-System Frontier

| System | OK | Timeout | Solved-row median |
|---|---:|---:|---:|
| Hex public factor | 373 | 19 | 420.153 µs |
| Hex lattice | 369 | 23 | 1.838 ms |
| Hex classical, no decline | 372 | 20 | 401.736 µs |
| FLINT 0.9.0 | 391 | 1 | 66.850 µs |
| PARI/GP 2.17.3 | 391 | 1 | 99.958 µs |
| NTL 11.6.0 | 391 | 1 | 135.631 µs |
| Verified Isabelle BZ | 371 | 21 | 441.134 µs |
| Verified Isabelle LLL | 314 | 78 | 6.109 ms |

The external rows are the unchanged current 2026-07-28 measurements from the
same host, corpus, CPU, and protocol. On 238 common rows above each service's
10× protocol-overhead threshold, public Hex / verified Isabelle BZ has median
0.909× and p10–p90 0.47×–2.64×; Hex wins 127 rows and Isabelle 111. This is a
real aggregate Hex lead, but the wide family-dependent range is not yet a
decisive margin. The old eligible-row median was 3.95×.

The public protocol floor is 16.905 µs. Reapplying the preceding, lower
13.650 µs Hex floor gives 0.892× over 244 rows; applying the larger current
pair floor to both sides gives 0.916× over 236 rows. The lead is therefore not
created by the eligibility boundary.

The public row is recorded in
`reports/bench-results/hexbz-factor-sweep-hex-53bb12e2-guarded-tree-all-chungus2.json`
(SHA-256 `926e91245e45523a40e8b915004bf4e0e17f01ed3547feca94589760d3e55e27`).
It records a clean worktree.

The current public/classical comparison has 238 eligible rows and a 1.009×
median ratio; public wins 99 and classical 139. Isolated classical retains a
small ordinary-row advantage, while public is better on selected hard rows and
uniquely solves `sd6`.

The current classical/lattice rows are in the same `53bb12e2` artifact. The
older `aaabcf15` record remains a historical A/B reference.

The bounded prime-width policy drives the large selector wins. It looks ahead by
at most two good primes only on predicted high-cost transforms, requires at
least a 25% modular-width reduction before changing prime, and preserves cheap
even `x^n - 1` recursion. The largest current/pre-policy gains are 73.83× on
`sd5_x_phi45`, 28.44× on `xpow105_minus1`, 7.55× on `cyclo_phi151`, 7.16×
on `cyclo_phi179`, 5.48× on `cyclo_phi61`, and 5.33× on `legendre_P30`.

The latest movement guards a degree-aware Hensel product tree behind the
presence of one modular factor larger than half the node degree, and permits a
deeper relift ladder only for extreme-precision four-factor nodes. Against the
preceding public export, `chebyshev_U24` falls from 7.664 ms to 3.049 ms,
`legendre_P30` from 32.486 ms to 16.237 ms, and `legendre_P38` from 37.858 ms
to 15.528 ms. The changed quadratic-multifactor microbenchmark remains flat at
67.229 ms; its focused export is
`reports/bench-results/hex-hensel-quadratic-multifactor-478c3ccc-guarded-tree-chungus2.json`.

## Diagnostics

- Split degree 24: 16.387 ms rebuilding the kernel, 1.245 ms sharing it,
  569.224 µs on the fixed path.
- Fixed split-degree-24 attribution: 18.89% matrix, 2.95% nullspace,
  78.17% witness splitting.
- Hybrid `SD_5`: 100.706 ms through the classical tier.
- Hybrid `SD_6`: 9.132 s, lattice decline, irreducible fallback.
- Lattice core `SD_6`: 8.257 s.

At degree 24 on the Mignotte schedule, the production balanced lift takes
4.506 ms versus 5.837 ms for the same tree with a full-witness final
correction, a 1.30× factor-only speedup.

Raw diagnostic artifacts:

- `berlekamp-diagnostic-a1fdbd81-chungus2.txt` (SHA-256
  `03e59491ed588ca377ece2ef387450ba699ef9e63d323db50e6c36fa17f265b5`)
- `bz-spikes-b4b36754-exact-factor-only-chungus2.txt` (SHA-256
  `1e63599da4da285708b9ac2a6b06fbbb3986b7d418f3452b374682306b3f7efb`)

Both paths are relative to `reports/bench-results/`.

### Swinnerton-Dyer seam

| Fixture | Hex public | Verified Isabelle BZ | Hex / Isabelle |
|---|---:|---:|---:|
| `SD_5` | 91.491 ms | 22.827 ms | 4.01x |
| `SD_5` shifted by 1 | 78.123 ms | 14.875 ms | 5.25x |
| `SD_5` shifted by 2 | 79.193 ms | 14.907 ms | 5.31x |
| `SD_6` | 9.077 s | timeout | — |

The fresh public service now solves `SD_6`; the no-decline classical service
still times out. The public result and the isolated lattice result (8.285 s)
show that the dispatcher is adding useful reach here. The public measurement
is a single cutoff-limited shot only 9.2% below ten seconds, so this frontier
success has a narrow margin.

## Concerns

- Nineteen public corpus cases still hit the 10-second cutoff.
- FLINT, PARI/GP, and NTL remain much faster in aggregate.
- Hex has a modest aggregate lead over Isabelle BZ, but Chebyshev still favours
  Isabelle by 2.05× and Legendre by 1.85× at their family medians.
- No-decline classical has a 0.9% paired-median lead over public; further broad
  gains must come from the factorization core rather than dispatch alone.
- The lattice route has a much heavier tail than the classical route.
- `wilkinson_56` remains a slower outlier despite the 0.93× cumulative
  Wilkinson-family median.
- The BHKS registrations are useful upper bounds but do not describe the
  observed small-fixture scaling.
