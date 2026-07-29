# HexBerlekampZassenhaus Performance Report

The current public-factor corpus measurement covers the exact-exponent and
factor-only Hensel implementation over base revision
`b4b3675472f58958c9c2f9b2ab2f7aae16c3dc62`; the current classical and lattice
rows are from `aaabcf1520121b4acaa793811c8567dddcf39f1f`. The five affected
parametric and five affected fixed registrations were refreshed over the same
`b4b36754` base; the three unchanged registrations in each table and unchanged
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
| Public factorization | 24 | 1.817 ms |
| Fallback probe | 24 | 1.556 ms |
| Degree/height | `(6,32)` | 214.404 µs |
| Fast-path precision/local | `(8,32,128,8)` | 1.554 ms |
| Slow factorization | 4 | 12.564 µs |
| Slow degree/height | `(3,8)` | 30.827 µs |
| Public compare domain | 4 | 72.460 µs |
| Slow compare domain | 4 | 12.577 µs |

| Warm fixed fixture | Median | Min–max |
|---|---:|---:|
| `X⁴ + 1`, public | 30.871 µs | 30.733–31.058 µs |
| `X⁴ + 1`, fast setup | 20.751 µs | 20.487–20.800 µs |
| `(X²-2)(X²-3)`, public | 29.060 µs | 28.935–30.253 µs |
| `Phi_15`, public | 91.638 µs | 90.852–92.896 µs |
| `Phi_15`, fast setup | 25.862 µs | 25.718–25.967 µs |
| `SD_3`, modular split | 8.420 µs | 8.243–8.568 µs |
| `SD_3`, lattice factorization | 1.624 ms | 1.595–1.717 ms |
| `SD_4`, lattice factorization | 29.573 ms | 29.324–29.663 ms |

The public `X⁴+1` fixed fixture falls from 98.628 µs to 30.871 µs and
`Phi_15` from 205.705 µs to 91.638 µs. Quadratic multifactor Hensel lifting,
reported separately, is the largest lower-layer improvement.

Exports under `reports/bench-results/`:

- `hex-berlekamp-zassenhaus-parametric-a1fdbd81-chungus2.json`
  (SHA-256
  `6e1c8e966b178f2ebadfbeec1a5283ab044fa0125f99ed9a9a2326b133da79ee`)
- `hex-berlekamp-zassenhaus-fixed-a1fdbd81-chungus2.json`
  (SHA-256
  `49acf7761bc6df09e1192761989f85f3f8acb21733de85d8d01383152951141f`)
- `hex-berlekamp-zassenhaus-parametric-b4b36754-exact-factor-only-overlay-chungus2.json`
  (five changed targets; SHA-256
  `37f661697681a80a428592e793ffa1382321e3ee9bdfd69d274a54da34becea3`)
- `hex-berlekamp-zassenhaus-fixed-b4b36754-exact-factor-only-overlay-chungus2.json`
  (five changed targets; SHA-256
  `f426e2c6ececf8d5f22f54bc875b17a26a37f820472969c63c34e6ff7c54f149`)

`list` and every non-scheduled `verify` target passed.

The `a1fdbd81` JSON exports record a dirty worktree because the
borrowed-argument fix and their reports were pending together. The new overlay
exports also record `git_dirty = true`; their worktree differs from base
`b4b36754` only by the exact-exponent/factor-only runtime patch and associated
documentation. The hashes above identify both measured states exactly.

## Cross-System Frontier

| System | OK | Timeout | Solved-row median |
|---|---:|---:|---:|
| Hex public factor | 373 | 19 | 424.039 µs |
| Hex lattice | 369 | 23 | 1.957 ms |
| Hex classical, no decline | 372 | 20 | 423.939 µs |
| FLINT 0.9.0 | 391 | 1 | 66.850 µs |
| PARI/GP 2.17.3 | 391 | 1 | 99.958 µs |
| NTL 11.6.0 | 391 | 1 | 135.631 µs |
| Verified Isabelle BZ | 371 | 21 | 441.134 µs |
| Verified Isabelle LLL | 314 | 78 | 6.109 ms |

The external rows are the unchanged current 2026-07-28 measurements from the
same host, corpus, CPU, and protocol. On 238 common rows above each service's
10× protocol-overhead threshold, public Hex / verified Isabelle BZ has median
0.930× and p10–p90 0.48×–2.91×; Hex wins 126 rows and Isabelle 112. This is a
real aggregate Hex lead, but the wide family-dependent range is not yet a
decisive margin. The old eligible-row median was 3.95×.

The public protocol floor is 17.196 µs. Reapplying the preceding, lower
13.650 µs Hex floor gives 0.904× over 244 rows; applying the larger current
pair floor to both sides gives 0.944× over 235 rows. The lead is therefore not
created by the eligibility boundary.

The public row is recorded in
`reports/bench-results/hexbz-factor-sweep-hex-b4b36754-exact-factor-only-chungus2.json`
(SHA-256 `090b594a14b12af8332fef091d2bd8ca5652c3e7566e6bd452a984eb473a058a`).
It records `git_dirty = true` because the measured runtime patch was pending
over the stated base revision.

The current public/classical comparison has 238 eligible rows and a 0.996×
median ratio; public wins 126 and classical 112. The earlier result—classical
winning 171 of 240 ordinary rows at a 1.5% median margin—was a small tiering
cost before the production lifting work landed, not an intrinsic advantage of
classical factorization. The two are now tied in the middle while public is
substantially better on selected hard rows and uniquely solves `sd6`.

The classical/lattice rows are recorded in
`reports/bench-results/hexbz-factor-sweep-hex-aaabcf15-chungus2.json`
(SHA-256 `30e56da9aa3c6f4f50faca4ef19e5c4d4f6523362542f2d8967ca7665f62f747`).

The bounded prime-width policy drives the large selector wins. It looks ahead by
at most two good primes only on predicted high-cost transforms, requires at
least a 25% modular-width reduction before changing prime, and preserves cheap
even `x^n - 1` recursion. The largest current/pre-policy gains are 73.83× on
`sd5_x_phi45`, 28.44× on `xpow105_minus1`, 7.55× on `cyclo_phi151`, 7.16×
on `cyclo_phi179`, 5.48× on `cyclo_phi61`, and 5.33× on `legendre_P30`.

The latest movement comes from reaching Hensel exponent `k` exactly rather
than overshooting to the next power of two, plus omitting the final Bezout
update when production needs only the factors. Against the preceding public
export, `conway_p2_n38` falls from 8.103 ms to 2.988 ms, `legendre_P30` from
49.550 ms to 32.486 ms, and `legendre_P38` from 48.032 ms to 37.858 ms. The
changed quadratic-multifactor microbenchmark falls from 89.522 ms to
67.862 ms; its focused export is
`reports/bench-results/hex-hensel-quadratic-multifactor-b4b36754-exact-factor-only-chungus2.json`.

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
| `SD_5` | 92.286 ms | 22.827 ms | 4.04x |
| `SD_5` shifted by 1 | 82.206 ms | 14.875 ms | 5.53x |
| `SD_5` shifted by 2 | 82.796 ms | 14.907 ms | 5.55x |
| `SD_6` | 8.986 s | timeout | — |

The fresh public service now solves `SD_6`; the no-decline classical service
still times out. The public result and the isolated lattice result (8.573 s)
show that the dispatcher is adding useful reach here. The public measurement
is a single cutoff-limited shot only 10.1% below ten seconds, so this frontier
success has a narrow margin.

## Concerns

- Nineteen public corpus cases still hit the 10-second cutoff.
- FLINT, PARI/GP, and NTL remain much faster in aggregate.
- Hex has a modest aggregate lead over Isabelle BZ, but Chebyshev and Legendre
  still favour Isabelle by more than 2× at their family medians.
- Public and no-decline classical are tied at their paired median; this means
  further gains must come from the factorization core rather than dispatch.
- The lattice route has a much heavier tail than the classical route.
- `wilkinson_56` regresses by 1.26× against the pre-policy export, although the
  eligible Wilkinson-family median improves to 0.94× current/previous.
- The BHKS registrations are useful upper bounds but do not describe the
  observed small-fixture scaling.
