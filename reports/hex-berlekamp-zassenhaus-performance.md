# HexBerlekampZassenhaus Performance Report

The current public-factor measurement adds verified original-coordinate M1
lifting and bounded modular degree certificates at
`2ee33dc56118b9bd4da5d1800c3807a38158bdb2`. The unchanged
classical-no-decline measurement is at `b0150d2b`; lattice, parametric, and
fixed measurements remain at `0b95505b7c926911a9f487bac56676a8c7da48f6`.
All were measured on `chungus2` (AMD EPYC 9455, Linux x86-64), pinned to CPU
0, from clean worktrees.

## Bench Targets

Eight parametric targets cover public factorization, the exhaustive backstop,
degree/height, fallback behaviour, and fast-path precision/local-factor axes.
Eight canonical adversarial fixtures are warm fixed benchmarks. All parametric
targets completed three outer trials; their classical BHKS upper-bound models
are loose on these small deterministic fixtures, so the verdicts are
inconclusive rather than failed.

| Target | Largest rung | Median |
|---|---:|---:|
| Public factorization | 24 | 1.719 ms |
| Fallback probe | 24 | 1.475 ms |
| Degree/height | `(6,32)` | 199.855 µs |
| Fast-path precision/local | `(8,32,128,8)` | 1.255 ms |
| Slow factorization | 4 | 12.273 µs |
| Slow degree/height | `(3,8)` | 30.940 µs |
| Public compare domain | 4 | 68.589 µs |
| Slow compare domain | 4 | 12.281 µs |

| Warm fixed fixture | Median | Min–max |
|---|---:|---:|
| `X⁴ + 1`, public | 28.916 µs | 28.671–29.082 µs |
| `X⁴ + 1`, fast setup | 20.359 µs | 20.285–20.393 µs |
| `(X²-2)(X²-3)`, public | 27.071 µs | 26.985–27.567 µs |
| `Phi_15`, public | 86.801 µs | 86.342–88.227 µs |
| `Phi_15`, fast setup | 25.437 µs | 25.201–25.609 µs |
| `SD_3`, modular split | 8.478 µs | 8.325–8.802 µs |
| `SD_3`, lattice factorization | 1.593 ms | 1.575–1.604 ms |
| `SD_4`, lattice factorization | 29.294 ms | 29.256–30.226 ms |

The public `X⁴+1` fixed fixture falls from 98.628 µs to 28.916 µs and
`Phi_15` from 205.705 µs to 86.801 µs. Quadratic multifactor Hensel lifting,
reported separately, is the largest lower-layer improvement.

Exports under `reports/bench-results/`:

- `hex-berlekamp-zassenhaus-parametric-0b95505b-gcd-hensel-chungus2.json`
  (SHA-256
  `b915b2f27be36251cc8be6603858dbe29f5311502d00a030235351a9a1b1dd70`)
- `hex-berlekamp-zassenhaus-fixed-0b95505b-gcd-hensel-chungus2.json`
  (SHA-256
  `82ddd9e54cfafcfefc936ffeb1f1c8bb7e926e7545cd2b992ecfbc508e1ee78d`)

`list` and every non-scheduled `verify` target passed.

Both exports record clean worktrees and cover all eight non-scheduled targets,
so no unchanged rows are inherited from an earlier implementation.

## Cross-System Frontier

| System | OK | Timeout | Solved-row median |
|---|---:|---:|---:|
| Hex public factor | 373 | 19 | 400.905 µs |
| Hex lattice | 369 | 23 | 1.812 ms |
| Hex classical, no decline | 372 | 20 | 386.358 µs |
| FLINT 0.9.0 | 391 | 1 | 66.850 µs |
| PARI/GP 2.17.3 | 391 | 1 | 99.958 µs |
| NTL 11.6.0 | 391 | 1 | 135.631 µs |
| Verified Isabelle BZ | 371 | 21 | 441.134 µs |
| Verified Isabelle LLL | 314 | 78 | 6.109 ms |

The external rows are the unchanged current 2026-07-28 measurements from the
same host, corpus, CPU, and protocol. On 234 common rows above each service's
10× protocol-overhead threshold, public Hex / verified Isabelle BZ has median
0.865× and p10–p90 0.466×–2.062×; Hex wins 135 rows and Isabelle 99. This is a
clear aggregate Hex lead, but the wide family-dependent range is not uniform
superiority. The old eligible-row median was 3.95×.

The public protocol floor is 17.466 µs.

The public row is recorded in
`reports/bench-results/hexbz-factor-sweep-hex-2ee33dc5-m1-chungus2.json`
(SHA-256 `a604aaaf492dacf726a0ae6315744f14a46dd21d124033b846a73e00f5511e89`).
It records a clean worktree.

The current public/classical comparison has 237 eligible rows and a 1.003×
median ratio in the pre-M1 record. Comparing current public with that unchanged
diagnostic gives 1.007×, with a 108–129 win split and a wider band because the
production path now uses M1 selectively. Public is better on selected hard
rows and uniquely solves `sd6`.

The current classical row is in the `b0150d2b` artifact; the unchanged lattice
row is in `0b95505b`. The older `aaabcf15` record remains a historical A/B
reference.

At the preceding `b0150d2b` stage, the bounded prime-width policy drives the
large selector wins. It looks ahead by
at most two good primes only on predicted high-cost transforms, requires at
least a 25% modular-width reduction before changing prime, and preserves cheap
even `x^n - 1` recursion. The largest current/pre-policy gains are 75.54× on
`sd5_x_phi45`, 29.03× on `xpow105_minus1`, 12.39× on `legendre_P30`, 7.42×
on `cyclo_phi151`, 7.09× on `cyclo_phi179`, and 5.60× on `cyclo_phi61`.

Cached recombination is the next preceding movement. Against `0b95505b`, the
eligible-row paired median is 0.988× and `b0150d2b` wins 171 of 243 rows. The
targeted `sd5` family improves by 2.24×–2.73× while the full corpus remains
stable.

## Original-coordinate M1

The production classical tier now reuses the adaptive selector's chosen prime
and modular factors, transports them back to the original coordinate, and
Hensel-lifts `monicTarget core` at the original core's Mignotte precision.
Acceptance is independently certified; any failed search or certificate falls
back to the proved M2 route.

The same-prime lift changes include 4.23 ms to 0.24 ms on Chebyshev U24,
4.08 ms to 0.42 ms on Legendre P30, and 5.22 ms to 0.64 ms on Legendre P38.
End to end, U24 falls from 2.610 ms to 0.814 ms, P28 from 8.205 ms to
5.074 ms, P30 from 13.807 ms to 11.367 ms, and P38 from 13.602 ms to
8.701 ms.

The Chebyshev family median against Isabelle improves from 1.619× to 1.197×;
Legendre improves from 1.435× to 1.260×. A degree-aware Mignotte cap, longer
modular singleton scan, and global removal of recursive relifting do not clear
their measured gates. The implementation instead uses a bounded two-prime
degree obstruction and a deterministic M1 cost gate. See
`hexbz-m1-chebyshev-legendre.md` for the complete dependency and measurement
record.

The preceding movement removes discarded quotient construction from Euclidean
GCD, caches finite-field divisor inverses, maps prime-power coefficient
reduction directly over the stored array, and replaces multiplication by a
monomial in quadratic Hensel division with an exact shift-and-scale kernel.
Against the immediately preceding public export, the all-row paired median is
0.964× and current Hex is faster on 306 of 373 rows. `chebyshev_U24` is now
2.608 ms, `legendre_P30` 13.970 ms, `legendre_P38` 13.771 ms, and
`cyclo_phi385` 447.061 ms. The quadratic-multifactor microbenchmark falls from
67.229 ms to 48.711 ms.

## Retained phase diagnostics

The following phase attribution and factor-only A/B belong to their named
earlier revisions; they remain useful localization evidence but are not
relabelled as current timings:

- Split degree 24: 16.387 ms rebuilding the kernel, 1.245 ms sharing it,
  569.224 µs on the fixed path.
- Fixed split-degree-24 attribution: 18.89% matrix, 2.95% nullspace,
  78.17% witness splitting.

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
| `SD_5` | 40.120 ms | 22.827 ms | 1.76x |
| `SD_5` shifted by 1 | 28.420 ms | 14.875 ms | 1.91x |
| `SD_5` shifted by 2 | 30.102 ms | 14.907 ms | 2.02x |
| `SD_6` | 8.994 s | timeout | — |

The fresh public service now solves `SD_6`; the no-decline classical service
still times out. The public result and the isolated lattice result (8.583 s)
show that the dispatcher is adding useful reach here. The public measurement
is a single cutoff-limited shot only 10.1% below ten seconds, so this frontier
success has a narrow margin.

## Concerns

- Nineteen public corpus cases still hit the 10-second cutoff.
- FLINT, PARI/GP, and NTL remain much faster in aggregate.
- Hex has a 13.5% aggregate lead over Isabelle BZ, but Chebyshev still favours
  Isabelle by 1.20× and Legendre by 1.26× at their family medians.
- The unchanged no-decline diagnostic is no longer the same lifting core as
  production; current public/no-decline ratios include the selective M1 route.
- The lattice route has a much heavier tail than the classical route.
- `wilkinson_56` remains a slower outlier despite the 0.60× current
  Wilkinson-family median.
- The BHKS registrations are useful upper bounds but do not describe the
  observed small-fixture scaling.
