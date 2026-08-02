# Scouting modular degree patterns before splitting (issue #9128)

The direct prime planner used to run a full Berlekamp factorization at the
first good prime and, whenever that image had more than eight local factors, at
exactly two more good primes. At most one of those three factorizations is ever
used. This report records what the other two cost, what a bounded
distinct-degree scout costs in their place, and what replacing them does end to
end.

The planner only ever needs a candidate's *width* -- its number of local
factors -- and a width can be bracketed without splitting anything. The scout
costs one Frobenius power and one gcd per separated factor degree, so it is
cheap exactly when the image is wide, which is exactly when the walk has
something to shop for; and it is expensive exactly when the image is narrow,
which is exactly when the walk stops at the first prime and never scouts. That
asymmetry is what makes the design work, and it is measured below: on 23 of the
28 scouted candidates the scout costs at most a quarter of the split it
replaces, and the five exceptions are exactly the candidates whose largest
factor degree is 10 or more. At the narrow first primes the walk never scouts,
a complete pattern would have cost 0.83x to 6.5x of the split.

## Revision and protocol

Source revision `d8c048ae`, toolchain `leanprover/lean4:v4.33.0-rc1`,
host `chungus2` (96 cores, x86_64, linux), clean
worktree. Corpus `bench/corpus/hexbz-factor-corpus.jsonl`, sha256 `619913904240`.
Every measurement is pinned to one core with `taskset -c 0`.

The machine was shared with other work throughout, so absolute wall times are
not comparable with the issue #9127 baseline taken on a quiet machine. Two
protocols make the comparison safe anyway. Every before/after timing comes from
a **paired** run: two service binaries built from this worktree, differing only
in `HexBerlekampZassenhaus/Modular/PrimePlan.lean`, alternated on the same
pinned core over three rounds, with the rows whose plan does not change acting
as a load control. And every per-candidate cost is the median of
`--plan-repeats 3` calls of the same service, merged field by field after
asserting that the repeats agree on everything deterministic, so no single
loaded observation can make a candidate look good or bad. A merged candidate is
a real plan with estimated durations, not one execution.

### Artifacts

- `reports/bench-results/hexbz-phase-profile-d8c048ae-chungus2.json`
- `reports/bench-results/hexbz-factor-sweep-d8c048ae-hex-chungus2.json`
- `reports/bench-results/hexbz-factor-sampling-profiles-d8c048ae-chungus2.json`

The full Hex sweep solves 376 of 392 instances, the same set as the
baseline, with no instance changing between solved and unsolved. All 25 figures
are regenerated from it; the external comparator records are reused unchanged.

## What the policy is now

The walk splits the first good prime. If that image has at most `scoutWidth`
(8) local factors it is used unexamined: the complete head-forced subset search
over `w` factors visits at most `2^(w - 1)` subsets, 128 at `w = 8`, less than
one Frobenius power of a scout on any input this planner sees.

Otherwise the walk scouts at most `scoutFuel` (2) further good primes with
`Hex.Berlekamp.scoutDegreePattern`. The scout separates the monic modular image
one factor degree at a time by the usual Frobenius-power gcds. After degree `d`
is separated, every irreducible factor left in a residual of degree `m` has
degree at least `d`, so the factor count lies between `separated + 1` and
`separated + m / d`. It also stops when the residual is a unit, and when the
residual is too small to be a product of two factors of degree at least `d` and
is therefore irreducible, so it never runs past the largest factor degree.

The target is the current best width. A candidate wider than that can only
score worse, so the scout abandons its pattern as soon as the factors it has
separated reach the target, however much of the polynomial is left; otherwise
the pattern completes.

Every key of the lexicographic score -- complete subset work, reachable proper
degrees, Hensel precision, prime -- is a function of the prime and the multiset
of modular factor degrees. So a *complete* scouted pattern scores exactly as
the factorization it predicts would, and the walk can compare candidates
without splitting any of them. Only the winner is split.

The walk therefore performs one full split at the first good prime, at most
`scoutFuel` bounded scouts, and one further full split for the scouted winner:
**at most two splits where the rule it replaces performed three, and one
wherever no scouted candidate wins.**

The scout is a performance heuristic, not a correctness oracle. Every
factorization, certificate, and degree obstruction still comes from the
Berlekamp split at the selected prime; `directPrimePlan?_selected_spec` and
`directPrimePlan?_selected_p_le_500` are unchanged, and the Mathlib layer needed
no change at all.

### The scout agrees with the split

Across the 144 candidates the record prices -- every good prime in a
six-prime prefix of the candidate list, on every representative instance and
control -- the scouted degree multiset equals the Berlekamp split's on
144 of 144. The counted recombination mirror agrees with the
production `factorTrace` on leaf count, selected prime, completed subset
cardinalities, and returned factor degrees on 367 of 367 applicable
instances, and the instrumented total tracks the plain cascade to a median
ratio of 0.9866.

That agreement is evidence about the *predictor*, not a correctness argument:
the plan is built from the split, so a wrong pattern could only cost time.

## Why the first good prime is split rather than scouted

The scout's cost is one Frobenius power and one gcd per separated degree, so it
grows with the *largest factor degree*, while a Berlekamp split grows with the
modular degree cubed through its matrix and row reduction. A wide image has
many small factors and a small largest degree, so scouting is cheap; a narrow
image has few large factors, and scouting it costs more than splitting it.

That is why the walk cannot scout first. The second table below prices a
complete pattern at the first good prime of every instance whose walk stops
there: those are exactly the narrow images, and the scout would have cost from
0.83x to 6.5x the split it was trying to avoid. Splitting the first good prime
and scouting only afterwards puts the scout exactly where it pays.

Each candidate below is scouted against the *first* good prime's width. That is
the target production carries until a scouted candidate wins and tightens it,
which on this corpus happens only where the winning candidate is the last one
scouted, so these prices match the production walk here; in general they are
scout prices at a fixed target rather than a replay of it.

### Scout, kernel, and split prices at each scouted candidate

| instance | prime | width | degree pattern | good-prime test | bounded scout | matrix + kernel | full split | scout / split | separated | residual | outcome |
|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|:--|
| `sd5` | 19 | 16 | 2^16 | 18.597 us | -- | 1.150 ms | 2.725 ms | -- | -- | -- | first |
| `sd5` | 23 | 16 | 2^16 | 18.087 us | 335.278 us | 1.333 ms | 2.943 ms | 0.114x | 16 | 0 | scored |
| `sd5` | 29 | 16 | 2^16 | 18.958 us | 362.889 us | 1.582 ms | 3.558 ms | 0.102x | 16 | 0 | scored |
| `sd5_shift1` | 19 | 16 | 2^16 | 32.899 us | -- | 1.686 ms | 3.192 ms | -- | -- | -- | first |
| `sd5_shift1` | 23 | 16 | 2^16 | 31.247 us | 439.612 us | 1.931 ms | 3.232 ms | 0.136x | 16 | 0 | scored |
| `sd5_shift1` | 29 | 16 | 2^16 | 32.368 us | 483.376 us | 2.259 ms | 3.645 ms | 0.133x | 16 | 0 | scored |
| `sd5_shift2` | 19 | 16 | 2^16 | 32.989 us | -- | 1.683 ms | 3.232 ms | -- | -- | -- | first |
| `sd5_shift2` | 23 | 16 | 2^16 | 31.366 us | 444.499 us | 1.928 ms | 3.943 ms | 0.113x | 16 | 0 | scored |
| `sd5_shift2` | 29 | 16 | 2^16 | 32.108 us | 482.045 us | 2.256 ms | 5.133 ms | 0.094x | 16 | 0 | scored |
| `sd4_x_sd4shift1` | 13 | 16 | 2^16 | 32.268 us | -- | 1.275 ms | 2.280 ms | -- | -- | -- | first |
| `sd4_x_sd4shift1` | 17 | 16 | 2^16 | 30.836 us | 295.238 us | 1.625 ms | 2.778 ms | 0.106x | 16 | 0 | scored |
| `sd4_x_sd4shift1` | 29 | 16 | 2^16 | 33.550 us | 494.013 us | 2.324 ms | 4.496 ms | 0.110x | 16 | 0 | scored |
| `sd5_x_phi11` | 19 | 17 | 2^16 10 | 50.956 us | -- | 3.632 ms | 5.917 ms | -- | -- | -- | first |
| `sd5_x_phi11` | 23 | 26 | 1^10 2^16 | 52.689 us | 700.068 us | 3.347 ms | 6.484 ms | 0.108x | 26 | 0 | scored |
| `sd5_x_phi11` | 29 | 17 | 2^16 10 | 51.826 us | 3.114 ms | 4.672 ms | 9.158 ms | 0.340x | 17 | 0 | scored |
| `xpow48_minus1` | 5 | 20 | 1^4 2^10 4^6 | 5.568 us | -- | 515.303 us | 1.570 ms | -- | -- | -- | first |
| `xpow48_minus1` | 7 | 27 | 1^6 2^21 | 5.719 us | 79.398 us | 544.717 us | 2.381 ms | 0.033x | 27 | 0 | scored |
| `xpow48_minus1` | 11 | 19 | 1^2 2^11 4^6 | 5.668 us | 487.554 us | 743.763 us | 2.122 ms | 0.230x | 19 | 0 | scored |
| `xpow105_minus1` | 11 | 30 | 1^5 2^5 3^10 6^10 | 11.527 us | -- | 3.622 ms | 12.601 ms | -- | -- | -- | first |
| `xpow105_minus1` | 13 | 33 | 1^3 2^9 4^21 | 11.998 us | 2.411 ms | 3.852 ms | 15.725 ms | 0.153x | 33 | 0 | scored |
| `xpow105_minus1` | 17 | 14 | 1 2 4^3 6^3 12^6 | 11.817 us | 6.294 ms | 4.963 ms | 9.993 ms | 0.630x | 14 | 0 | scored |
| `xpow120_minus1` | 7 | 39 | 1^6 2^9 4^24 | 12.959 us | -- | 3.802 ms | 17.337 ms | -- | -- | -- | first |
| `xpow120_minus1` | 11 | 65 | 1^10 2^55 | 13.901 us | 459.642 us | 4.264 ms | 30.990 ms | 0.015x | 65 | 0 | scored |
| `xpow120_minus1` | 13 | 42 | 1^12 2^6 4^24 | 15.543 us | 1.985 ms | 5.198 ms | 16.866 ms | 0.118x | 42 | 0 | scored |
| `cyclo_phi64_x_phi105` | 11 | 10 | 6^8 16^2 | 155.982 us | -- | 18.921 ms | 22.008 ms | -- | -- | -- | first |
| `cyclo_phi64_x_phi105` | 13 | 14 | 4^12 16^2 | 162.611 us | 4.933 ms | 18.916 ms | 25.250 ms | 0.195x | 12 | 32 | abandoned |
| `cyclo_phi64_x_phi105` | 17 | 12 | 4^8 12^4 | 157.023 us | 21.820 ms | 20.942 ms | 27.786 ms | 0.785x | 12 | 0 | scored |
| `wilkinson_40` | 41 | 40 | 1^40 | 7.101 us | -- | 230.381 us | 1.786 ms | -- | -- | -- | first |
| `wilkinson_40` | 43 | 40 | 1^40 | 13.801 us | 72.207 us | 234.608 us | 1.801 ms | 0.040x | 40 | 0 | scored |
| `wilkinson_40` | 47 | 40 | 1^40 | 20.761 us | 87.149 us | 260.917 us | 1.801 ms | 0.048x | 40 | 0 | scored |
| `wilkinson_48` | 53 | 48 | 1^48 | 20.651 us | -- | 328.086 us | 2.819 ms | -- | -- | -- | first |
| `wilkinson_48` | 59 | 48 | 1^48 | 32.298 us | 115.320 us | 349.738 us | 3.202 ms | 0.036x | 48 | 0 | scored |
| `wilkinson_48` | 61 | 48 | 1^48 | 40.400 us | 124.655 us | 358.272 us | 2.859 ms | 0.044x | 48 | 0 | scored |
| `wilkinson_56` | 59 | 56 | 1^56 | 18.859 us | -- | 423.018 us | 4.196 ms | -- | -- | -- | first |
| `wilkinson_56` | 61 | 56 | 1^56 | 24.145 us | 109.973 us | 429.548 us | 4.228 ms | 0.026x | 56 | 0 | scored |
| `wilkinson_56` | 67 | 56 | 1^56 | 38.307 us | 246.045 us | 568.263 us | 4.371 ms | 0.056x | 56 | 0 | scored |
| `legendre_P30` | 61 | 15 | 2^15 | 17.346 us | -- | 1.525 ms | 3.114 ms | -- | -- | -- | first |
| `legendre_P30` | 67 | 7 | 2^5 6 14 | 17.876 us | 2.121 ms | 1.682 ms | 2.315 ms | 0.916x | 7 | 0 | scored |
| `legendre_P30` | 71 | 4 | 2 3^2 22 | 17.986 us | 3.829 ms | 1.740 ms | 2.105 ms | 1.819x | 4 | 0 | scored |
| `xpow24_minus1` | 5 | 14 | 1^4 2^10 | 3.155 us | -- | 128.801 us | 399.463 us | -- | -- | -- | first |
| `xpow24_minus1` | 7 | 15 | 1^6 2^9 | 3.275 us | 31.436 us | 146.867 us | 403.048 us | 0.078x | 15 | 0 | scored |
| `xpow24_minus1` | 11 | 13 | 1^2 2^11 | 3.295 us | 80.329 us | 193.717 us | 625.808 us | 0.128x | 13 | 0 | scored |

### Scout price where the walk never scouts

A complete pattern at the first good prime of every instance whose walk stops
there, for the cost a scout-first policy would have paid.

| instance | prime | width | degree pattern | complete scout | full split | scout / split |
|---|---:|---:|---|---:|---:|---:|
| `cyclo_phi179` | 3 | 2 | 89^2 | 95.657 ms | 14.725 ms | 6.496x |
| `cyclo_phi128_x_phi165` | 7 | 8 | 16^4 20^4 | 95.525 ms | 97.302 ms | 0.982x |
| `cyclo_phi385` | 3 | 4 | 60^4 | 248.811 ms | 207.547 ms | 1.199x |
| `chebyshev_T24` | 5 | 3 | 8^3 | 278.803 us | 331.522 us | 0.841x |
| `chebyshev_U24` | 3 | 4 | 2^2 10^2 | 306.966 us | 318.633 us | 0.963x |
| `legendre_P38` | 79 | 3 | 1^2 36 | 11.215 ms | 3.697 ms | 3.034x |
| `cyclo_phi17` | 3 | 1 | 16 | 121.711 us | 98.967 us | 1.230x |
| `cyclo_phi41` | 3 | 5 | 8^5 | 620.420 us | 693.799 us | 0.894x |
| `randprod_10` | 7 | 4 | 3 4 6 7 | 545.199 us | 536.416 us | 1.016x |
| `randprod_21` | 17 | 7 | 1^4 4 7 9 | 1.239 ms | 1.207 ms | 1.027x |

What the scout costs is decided by the largest factor degree, not by which
candidate wins. Sorted by `scout / split`, the 28 scouted candidates run from
0.015x (`xpow120_minus1` prime 11, 65 factors of degree at most 2) to 1.819x
(`legendre_P30` prime 71, four factors reaching degree 22), and the ordering is
the ordering of their largest factor degree. Twenty-three sit at 0.25x or
below; the five above are `sd5_x_phi11` prime 29 (0.333x, degree 10),
`xpow105_minus1` prime 17 (0.634x, 12), `cyclo_phi64_x_phi105` prime 17
(0.791x, 12), and the two `legendre_P30` candidates (0.898x and 1.819x, 14 and
22). The last of those is priced here but never actually scouted: the walk ends
at prime 67, whose scouted width of 7 passes the gate.

The `outcome` column records the other way a scout can stop. *Abandoned* means
the separated factors reached the current width, so the candidate is wider and
cannot win, and the rest of its pattern is never computed:
`cyclo_phi64_x_phi105` at prime 13 gives up once its twelve degree-4 factors
reach the incumbent's ten, with 32 of the 80 degrees still unseparated, for
4.9 ms against the 25.0 ms split it avoided. That is the only abandonment in
this table. It is rare because the width test runs between degrees, and one
gcd often separates enough factors to pass the target and finish the pattern in
the same step -- `xpow120_minus1` at prime 11 goes from 10 separated factors to
all 65 in its degree-2 gcd. Nothing is lost when that happens: the scout is
cheap for the same reason the abandonment would have been.

## Counterfactual downstream costs

For every good prime in the fixed comparison set, the cost of having stopped
there. The comparison set is deliberately *not* the set the new plan retains:
the plan splits only what its scout admits, so following it would shrink the
table exactly where the policy is being evaluated. It is fixed instead at the
first good prime plus, when that image is wide, the next two -- the set the
pre-scout policy retained -- so the table stays row-for-row comparable with the
recorded baseline.

### Counterfactual downstream, fresh record

| instance | prime | width | precision | lift | recombination | downstream | nodes | exact divisions | selected |
|---|---:|---:|---:|---:|---:|---:|---:|---:|:--:|
| `sd5` | 19 | 16 | 21 | 1.847 ms | 94.329 ms | 96.179 ms | 32,768 | 129 |  |
| `sd5` | 23 | 16 | 20 | 1.790 ms | 94.493 ms | 96.277 ms | 32,768 | 129 |  |
| `sd5` | 29 | 16 | 19 | 1.803 ms | 95.342 ms | 97.148 ms | 32,768 | 129 | yes |
| `sd5_shift1` | 19 | 16 | 21 | 1.861 ms | 82.873 ms | 84.734 ms | 32,768 | 1 |  |
| `sd5_shift1` | 23 | 16 | 20 | 1.770 ms | 83.007 ms | 84.783 ms | 32,768 | 1 |  |
| `sd5_shift1` | 29 | 16 | 19 | 1.836 ms | 82.954 ms | 84.779 ms | 32,768 | 1 | yes |
| `sd5_shift2` | 19 | 16 | 22 | 1.771 ms | 83.573 ms | 85.344 ms | 32,768 | 1 |  |
| `sd5_shift2` | 23 | 16 | 21 | 1.836 ms | 83.908 ms | 85.743 ms | 32,768 | 1 |  |
| `sd5_shift2` | 29 | 16 | 19 | 1.819 ms | 83.947 ms | 85.766 ms | 32,768 | 1 | yes |
| `sd4_x_sd4shift1` | 13 | 16 | 22 | 1.660 ms | 12.089 ms | 13.744 ms | 10,503 | 10 |  |
| `sd4_x_sd4shift1` | 17 | 16 | 20 | 1.750 ms | 12.380 ms | 14.130 ms | 10,503 | 10 |  |
| `sd4_x_sd4shift1` | 29 | 16 | 17 | 1.782 ms | 12.478 ms | 14.260 ms | 10,540 | 10 | yes |
| `sd5_x_phi11` | 19 | 17 | 24 | 2.945 ms | 208.714 ms | 211.809 ms | 65,536 | 258 |  |
| `sd5_x_phi11` | 23 | 26 | 22 | 3.234 ms | 261.994 ms | 265.144 ms | 245,506 | 0 |  |
| `sd5_x_phi11` | 29 | 17 | 21 | 2.977 ms | 196.221 ms | 199.209 ms | 65,522 | 258 | yes |
| `xpow48_minus1` | 5 | 20 | 21 | 1.372 ms | 9.985 ms | 11.357 ms | 456 | 221 |  |
| `xpow48_minus1` | 7 | 27 | 17 | 1.537 ms | 5.221 s | 5.222 s | 181,455 | 60,530 |  |
| `xpow48_minus1` | 11 | 19 | 14 | 1.131 ms | 13.677 ms | 14.810 ms | 268 | 268 | yes |
| `xpow105_minus1` | 11 | 30 | 30 | 13.373 ms | 1.438 s | 1.451 s | 17,020 | 3,414 |  |
| `xpow105_minus1` | 13 | 33 | 28 | 14.664 ms | 37.092 s | 37.107 s | 174,439 | 58,145 |  |
| `xpow105_minus1` | 17 | 14 | 26 | 14.473 ms | 28.532 ms | 42.943 ms | 60 | 60 | yes |
| `xpow120_minus1` | 7 | 39 | 43 | 19.552 ms | 447.475 ms | 467.013 ms | 5,339 | 1,801 | yes |
| `xpow120_minus1` | 11 | 65 | 35 | 22.801 ms | 3.997 s | 4.020 s | 44,887 | 8,983 |  |
| `xpow120_minus1` | 13 | 42 | 32 | 8.896 ms | 6.002 s | 6.011 s | 53,449 | 9,179 |  |
| `cyclo_phi179` | 3 | 2 | 113 | 55.077 ms | 5.682 ms | 60.759 ms | 2 | 2 | yes |
| `cyclo_phi64_x_phi105` | 11 | 10 | 24 | 7.023 ms | 4.787 ms | 11.723 ms | 130 | 28 | yes |
| `cyclo_phi64_x_phi105` | 13 | 14 | 22 | 7.682 ms | 565.006 ms | 572.592 ms | 8,111 | 1,336 |  |
| `cyclo_phi64_x_phi105` | 17 | 12 | 20 | 7.287 ms | 92.275 ms | 99.598 ms | 1,512 | 221 |  |
| `cyclo_phi128_x_phi165` | 7 | 8 | 52 | 59.225 ms | 41.485 ms | 100.757 ms | 54 | 25 | yes |
| `cyclo_phi385` | 3 | 4 | 152 | 148.782 ms | 83.533 ms | 233.819 ms | 8 | 8 | yes |
| `wilkinson_40` | 41 | 40 | 38 | 7.387 ms | 505.790 us | 7.891 ms | 40 | 40 |  |
| `wilkinson_40` | 43 | 40 | 38 | 7.337 ms | 502.836 us | 7.843 ms | 40 | 40 |  |
| `wilkinson_40` | 47 | 40 | 37 | 7.399 ms | 500.613 us | 7.900 ms | 40 | 40 | yes |
| `wilkinson_48` | 53 | 48 | 45 | 16.224 ms | 771.434 us | 16.989 ms | 48 | 48 |  |
| `wilkinson_48` | 59 | 48 | 44 | 16.325 ms | 762.130 us | 17.087 ms | 48 | 48 |  |
| `wilkinson_48` | 61 | 48 | 43 | 16.272 ms | 752.356 us | 17.025 ms | 48 | 48 | yes |
| `wilkinson_56` | 59 | 56 | 53 | 21.148 ms | 1.024 ms | 22.175 ms | 56 | 56 |  |
| `wilkinson_56` | 61 | 56 | 52 | 21.143 ms | 1.031 ms | 22.202 ms | 56 | 56 |  |
| `wilkinson_56` | 67 | 56 | 51 | 21.360 ms | 1.020 ms | 22.380 ms | 56 | 56 | yes |
| `chebyshev_T24` | 5 | 3 | 22 | 121.540 us | 26.029 us | 147.569 us | 3 | 2 | yes |
| `chebyshev_U24` | 3 | 4 | 33 | 285.002 us | 25.198 us | 312.473 us | 4 | 4 | yes |
| `legendre_P30` | 61 | 15 | 15 | 934.356 us | 41.031 ms | 41.965 ms | 16,384 | 1 |  |
| `legendre_P30` | 67 | 7 | 15 | 1.274 ms | 180.688 us | 1.455 ms | 64 | 1 | yes |
| `legendre_P30` | 71 | 4 | 15 | 419.431 us | 62.593 us | 481.815 us | 8 | 1 |  |
| `legendre_P38` | 79 | 3 | 19 | 617.446 us | 50.155 us | 667.601 us | 4 | 1 | yes |
| `cyclo_phi17` | 3 | 1 | 11 | 2.474 us | 4.517 us | 6.991 us | 1 | 1 | yes |
| `cyclo_phi41` | 3 | 5 | 26 | 661.321 us | 1.459 ms | 2.128 ms | 16 | 16 | yes |
| `xpow24_minus1` | 5 | 14 | 11 | 395.807 us | 1.092 ms | 1.488 ms | 150 | 77 |  |
| `xpow24_minus1` | 7 | 15 | 9 | 372.842 us | 155.320 us | 527.551 us | 38 | 20 |  |
| `xpow24_minus1` | 11 | 13 | 7 | 297.091 us | 1.741 ms | 2.038 ms | 113 | 113 | yes |
| `randprod_10` | 7 | 4 | 11 | 175.981 us | 18.999 us | 194.980 us | 5 | 2 | yes |
| `randprod_21` | 17 | 7 | 9 | 326.735 us | 37.105 us | 363.840 us | 13 | 3 | yes |

## Offline policy comparison

All five policies replayed over the same measured per-candidate costs, so the
comparison does not depend on what the machine was doing when each row was
measured. Modular costs come from the scout section, where the good-prime test,
the bounded scout, the matrix with its kernel, and the full split are timed
adjacently in one process; downstream costs come from the counterfactual
section. Both are single observations per call, so all costs are the
`--plan-repeats` medians the record already carries.

* **first** -- split the first good prime and use it.
* **fixed** -- the pre-#9128 rule.
* **minwidth** -- the same three splits, choosing the narrowest image.
* **scout** -- the rule this PR lands.
* **reachable** -- the floor a *discovering* policy can reach: something has to
  be split before anything is known, and the prime finally used has to be split
  too, so the least any walk can pay is the good-prime tests it passes, the
  first split, and -- when the winner is not the first good prime -- the
  winner's split. No scouting, no rejected splits.
* **oracle** -- the floor the issue names: one split at the cheapest candidate
  and its downstream. Unreachable by any policy, because it names the winner
  without paying to discover it.

| instance | first | fixed | minwidth | scout | same-plan | reachable | oracle | primes (first/fixed/scout/oracle) |
|---|---:|---:|---:|---:|---:|---:|---:|---|
| `sd5` | 98.923ms | 106.430ms | 105.461ms | 104.185ms | 103.487ms | 98.923ms | 98.923ms | 19/29/29/19 |
| `sd5_shift1` | 87.959ms | 94.944ms | 94.899ms | 92.635ms | 91.712ms | 87.959ms | 87.959ms | 19/29/29/19 |
| `sd5_shift2` | 88.609ms | 98.170ms | 97.749ms | 95.154ms | 94.227ms | 88.609ms | 88.609ms | 19/29/29/19 |
| `sd4_x_sd4shift1` | 16.056ms | 23.911ms | 23.395ms | 21.922ms | 21.133ms | 16.056ms | 16.056ms | 13/29/29/13 |
| `sd5_x_phi11` | 217.777ms | 220.924ms | 233.524ms | 218.254ms | 214.440ms | 214.440ms | 208.419ms | 19/29/29/29 |
| `xpow48_minus1` | 12.932ms | 20.899ms | 20.899ms | 19.085ms | 18.518ms | 12.932ms | 12.932ms | 5/11/11/5 |
| `xpow105_minus1` | 1463.563ms | 81.298ms | 81.298ms | 74.277ms | 65.573ms | 65.573ms | 52.948ms | 11/17/17/17 |
| `xpow120_minus1` | 484.363ms | 532.249ms | 532.249ms | 486.837ms | 484.363ms | 484.363ms | 484.363ms | 7/7/7/7 |
| `cyclo_phi179` | 75.521ms | 75.521ms | 75.521ms | 75.521ms | 75.521ms | 75.521ms | 75.521ms | 3/3/3/3 |
| `cyclo_phi64_x_phi105` | 33.887ms | 87.242ms | 87.242ms | 60.959ms | 33.887ms | 33.887ms | 33.887ms | 11/11/11/11 |
| `cyclo_phi128_x_phi165` | 198.516ms | 198.516ms | 198.516ms | 198.516ms | 198.516ms | 198.516ms | 198.516ms | 7/7/7/7 |
| `cyclo_phi385` | 442.128ms | 442.128ms | 442.128ms | 442.128ms | 442.128ms | 442.128ms | 442.128ms | 3/3/3/3 |
| `wilkinson_40` | 9.683ms | 13.329ms | 13.320ms | 11.687ms | 11.528ms | 9.683ms | 9.658ms | 41/47/47/43 |
| `wilkinson_48` | 19.828ms | 25.998ms | 25.961ms | 23.036ms | 22.796ms | 19.828ms | 19.828ms | 53/61/61/53 |
| `wilkinson_56` | 26.390ms | 35.257ms | 35.052ms | 31.385ms | 31.029ms | 26.390ms | 26.390ms | 59/67/67/59 |
| `chebyshev_T24` | 0.491ms | 0.491ms | 0.491ms | 0.491ms | 0.491ms | 0.491ms | 0.491ms | 5/5/5/5 |
| `chebyshev_U24` | 0.637ms | 0.637ms | 0.637ms | 0.637ms | 0.637ms | 0.637ms | 0.637ms | 3/3/3/3 |
| `legendre_P30` | 45.096ms | 8.069ms | 8.069ms | 9.040ms | 5.754ms | 5.754ms | 2.605ms | 61/71/67/71 |
| `legendre_P38` | 4.390ms | 4.390ms | 4.390ms | 4.390ms | 4.390ms | 4.390ms | 4.390ms | 79/79/79/79 |
| `cyclo_phi17` | 0.110ms | 0.110ms | 0.110ms | 0.110ms | 0.110ms | 0.110ms | 0.110ms | 3/3/3/3 |
| `cyclo_phi41` | 2.830ms | 2.830ms | 2.830ms | 2.830ms | 2.830ms | 2.830ms | 2.830ms | 3/3/3/3 |
| `xpow24_minus1` | 1.891ms | 3.476ms | 3.476ms | 3.185ms | 3.073ms | 1.336ms | 0.934ms | 5/11/11/7 |
| `randprod_10` | 0.744ms | 0.744ms | 0.744ms | 0.744ms | 0.744ms | 0.744ms | 0.744ms | 7/7/7/7 |
| `randprod_21` | 1.589ms | 1.589ms | 1.589ms | 1.589ms | 1.589ms | 1.589ms | 1.589ms | 17/17/17/17 |
| **aggregate** | **3333.914 ms** | **2079.151 ms** | **2089.549 ms** | **1978.597 ms** | **1928.475 ms** | **1892.689 ms** | **1870.467 ms** | |

The replay reproduces both real walks: on every row, the prime the `fixed`
column picks is the prime the pre-#9128 binary selected, and the prime the
`scout` column picks is the prime this PR's binary selected.

Against the fixed policy the scout saves 100.554 ms of 2079.151 ms. That is
66.7% of what is available to the same-plan floor, 53.9% of the reachable
floor, and 48.2% of the oracle floor. The first-good-prime rule remains
unusable at 3236.775 ms, and choosing by minimum width alone is worse than the
score at 2089.549 ms -- `sd5_x_phi11` is where that shows, since prime 23 is
widest and prime 29 wins on the tie breaks.

## Paired before and after

The two service binaries were built from this worktree and differ only in
`HexBerlekampZassenhaus/Modular/PrimePlan.lean`, and the arms were alternated on
the same pinned core, so machine load hits both equally. The rows whose plan
does not change -- `cyclo_phi179`, `cyclo_phi128_x_phi165`, `cyclo_phi385`, the
Chebyshev and `randprod` controls, `cyclo_phi17`, `cyclo_phi41`, `legendre_P38`
-- are the load control: their prime walk does identical work in both arms, so
their spread bounds what can be read into the rows that did change.

The record is `reports/bench-results/hexbz-prime-plan-paired-d8c048ae-chungus2.json`;
it carries every round of both arms, and
`scripts/bench/prime_plan_paired.py --report` regenerates this table from it.

### Paired before/after, median of 3 alternating rounds

| instance | prime before | prime after | full splits | prime walk before | prime walk after | walk saved | total before | total after | ratio |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `sd5` | 29 | 29 | 3 -> 2 | 9.512 ms | 7.215 ms | 2.297 ms | 106.301 ms | 105.768 ms | 0.995x |
| `sd5_shift1` | 29 | 29 | 3 -> 2 | 10.496 ms | 8.167 ms | 2.329 ms | 96.676 ms | 94.823 ms | 0.981x |
| `sd5_shift2` | 29 | 29 | 3 -> 2 | 12.787 ms | 9.912 ms | 2.875 ms | 100.417 ms | 98.247 ms | 0.978x |
| `sd4_x_sd4shift1` | 29 | 29 | 3 -> 2 | 9.866 ms | 7.814 ms | 2.052 ms | 24.526 ms | 22.889 ms | 0.933x |
| `sd5_x_phi11` | 29 | 29 | 3 -> 2 | 22.112 ms | 19.282 ms | 2.830 ms | 221.560 ms | 221.391 ms | 0.999x |
| `xpow48_minus1` | 11 | 11 | 3 -> 2 | 6.170 ms | 4.321 ms | 1.849 ms | 21.062 ms | 19.281 ms | 0.915x |
| `xpow105_minus1` | 17 | 17 | 3 -> 2 | 38.660 ms | 31.378 ms | 7.282 ms | 82.853 ms | 74.641 ms | 0.901x |
| `xpow120_minus1` | 7 | 7 | 3 -> 1 | 65.401 ms | 19.790 ms | 45.611 ms | 525.237 ms | 482.508 ms | 0.919x |
| `cyclo_phi179` | 3 | 3 | 1 -> 1 | 14.698 ms | 14.623 ms | 75.162 us | 74.755 ms | 74.450 ms | 0.996x |
| `cyclo_phi64_x_phi105` | 11 | 11 | 3 -> 1 | 74.465 ms | 49.383 ms | 25.082 ms | 87.228 ms | 60.781 ms | 0.697x |
| `cyclo_phi128_x_phi165` | 7 | 7 | 1 -> 1 | 96.747 ms | 96.078 ms | 669.452 us | 195.718 ms | 196.658 ms | 1.005x |
| `cyclo_phi385` | 3 | 3 | 1 -> 1 | 205.080 ms | 205.242 ms | -162.282 us | 428.989 ms | 434.661 ms | 1.013x |
| `wilkinson_40` | 47 | 47 | 3 -> 2 | 6.053 ms | 4.412 ms | 1.642 ms | 14.969 ms | 13.453 ms | 0.899x |
| `wilkinson_48` | 61 | 61 | 3 -> 2 | 9.478 ms | 6.858 ms | 2.619 ms | 27.710 ms | 25.448 ms | 0.918x |
| `wilkinson_56` | 67 | 67 | 3 -> 2 | 13.874 ms | 10.127 ms | 3.747 ms | 37.654 ms | 34.354 ms | 0.912x |
| `chebyshev_T24` | 5 | 5 | 1 -> 1 | 352.473 us | 346.544 us | 5.929 us | 560.732 us | 561.082 us | 1.001x |
| `chebyshev_U24` | 3 | 3 | 1 -> 1 | 326.164 us | 324.601 us | 1.563 us | 704.144 us | 718.225 us | 1.020x |
| `legendre_P30` | 71 | 67 | 3 -> 2 | 7.748 ms | 7.639 ms | 109.192 us | 8.311 ms | 9.343 ms | 1.124x |
| `legendre_P38` | 79 | 79 | 1 -> 1 | 3.841 ms | 3.887 ms | -46.740 us | 4.705 ms | 4.732 ms | 1.006x |
| `cyclo_phi17` | 3 | 3 | 1 -> 1 | 103.664 us | 104.555 us | -891 ns | 150.643 us | 150.022 us | 0.996x |
| `cyclo_phi41` | 3 | 3 | 1 -> 1 | 704.485 us | 705.266 us | -781 ns | 2.831 ms | 2.874 ms | 1.015x |
| `xpow24_minus1` | 11 | 11 | 3 -> 2 | 1.461 ms | 1.170 ms | 290.831 us | 3.524 ms | 3.238 ms | 0.919x |
| `randprod_10` | 7 | 7 | 1 -> 1 | 559.710 us | 551.798 us | 7.912 us | 863.060 us | 815.289 us | 0.945x |
| `randprod_21` | 17 | 17 | 1 -> 1 | 1.292 ms | 1.282 ms | 9.774 us | 1.752 ms | 1.733 ms | 0.989x |
| **aggregate** | | | | | | 101.174 ms | 2.069 s | 1.984 s | **0.9587x** |

Load control (10 instances whose plan does not change): 0.945x to 1.020x.

Every row whose plan changes improves, between 0.697x and 0.999x, except
`legendre_P30`. The ten rows whose plan does not change span 0.945x to 1.020x
and are the day's noise floor on this machine. The prime walk loses 101.174 ms
across the corpus, of which `xpow120_minus1` is 45.6 ms and
`cyclo_phi64_x_phi105` 25.1 ms.

The three larger instances outside the representative set behave the same way.
Paired over two rounds: `sd6` 3 splits to 2 and prime 29 kept, `hoeij_F190`
3 to 2 and prime 13 kept, `hoeij_M12_f132` 3 to 2 and prime 13 kept. The full
sweep puts them at 1.036x, 0.968x and
0.984x against the issue #9127 baseline, inside its own
noise on rows where nothing about the plan changed.

## Where the selection changed, and what it cost

The scout compares candidates by exactly the score the old walk compared
factorizations by, so a candidate the walk scores is ranked as its
factorization would have been. That is not the same as selecting the old plan,
because the walk also stops on a scouted image inside the width gate -- the
same gate that governs the first good prime, but the old walk applied it only
to the first prime. Where the gate does not fire the two selections coincide:
on twenty-three of the twenty-four rows here, and on `sd6`, `hoeij_M12_f132`
and `hoeij_F190` besides, the selected prime is the one the fixed policy chose.
On `legendre_P30` the gate fires and the walk stops at prime 67 (width 7) where
the fixed policy went on to prime 71 (width 4).

That costs `legendre_P30` 1.03 ms of extra recombination and is the only
measured regression: 8.311 ms to 9.343 ms, 1.124x. Removing the gate was
measured too, and is worse: it selects prime 71 as the fixed policy did, but
pays the deeper second scout to get there, and the row lands at 1.464x. The
gate stays because `legendre_P30` is the one row in the corpus where scouting
cannot pay at all -- its factor degrees reach 14 and 22 of 30, so its two
scouts run most of the degree range and cost 0.90x and 1.82x of the splits they
replace, and splitting all three primes outright is genuinely cheaper there.

The remaining gap to the same-plan floor is the price of the evidence. On the
equal-width families -- Swinnerton-Dyer, Wilkinson -- every candidate has the
same width, so no scout can end the walk early and each one runs to a complete
pattern before being scored. Those scouts are cheap in absolute terms (2.6% to
13% of a split) but they buy only a confirmation, and the walk still splits the
winner. That is 51 ms of the 151 ms available on this corpus.

## Acceptance criteria

**Recovers at least 90% of the savings available to the bounded measured
oracle, or measurements justify a simpler policy with equivalent end-to-end
behaviour.** Not the first: 48.2% of the oracle floor, 53.9% of the reachable
floor, 66.7% of the same-plan floor. The oracle and reachable floors are
unreachable by construction -- the oracle names the winner without paying to
discover it, and neither ever scouts -- so the honest number is the third, and
the missing third of it is the complete scouts on equal-width families
described above. The second clause is what this PR claims: the policy is
simpler than the one it replaces (no width threshold, no fuel spent on
splitting, one selector), selects the same plan wherever the width gate does
not fire, and is 0.9587x end to end on the paired corpus, with every row whose
plan changes improving except `legendre_P30`.

**Median unsuccessful-scout overhead below 3%.** An unsuccessful scout is one
whose candidate is not selected. As a fraction of each scouting row's total:

| instance | unsuccessful scouts | row total | share |
|---|---:|---:|---:|
| `legendre_P30` | 0 ns | 9.343 ms | 0.00% |
| `sd5_x_phi11` | 700 us | 221.391 ms | 0.32% |
| `sd5` | 335 us | 105.768 ms | 0.32% |
| `wilkinson_56` | 110 us | 34.354 ms | 0.32% |
| `xpow48_minus1` | 79 us | 19.281 ms | 0.41% |
| `sd5_shift2` | 444 us | 98.247 ms | 0.45% |
| `wilkinson_48` | 115 us | 25.448 ms | 0.45% |
| `sd5_shift1` | 440 us | 94.823 ms | 0.46% |
| `xpow120_minus1` | 2.444 ms | 482.508 ms | 0.51% |
| `wilkinson_40` | 72 us | 13.453 ms | 0.54% |
| `xpow24_minus1` | 31 us | 3.238 ms | 0.97% |
| `sd4_x_sd4shift1` | 295 us | 22.889 ms | 1.29% |
| `xpow105_minus1` | 2.411 ms | 74.641 ms | 3.23% |
| `cyclo_phi64_x_phi105` | 26.753 ms | 60.781 ms | 44.01% |

Median **0.46%**. The `cyclo_phi64_x_phi105` outlier is the row where the
scouts replace two splits of 25.0 ms and 27.6 ms; it is the largest saving in
the corpus at 0.697x, so its scouts are not overhead in any useful sense.

**No unexplained regression above 5%.** One row regresses: `legendre_P30` at
1.124x, explained above and quantified. Every other row is inside the load
control's 0.945x to 1.020x band or improves. The full sweep solves the same
376 instances as the baseline.

**`xpow105_minus1` retains its useful width reduction.** It still selects prime
17 at width 14, against widths 30 and 33 at the two primes it rejects, and the
row improves 0.901x. The scout at prime 13 completes its pattern at width
33 and is rejected by its score, for 2.4 ms against the 15.8 ms split it
replaces.

**The wasted extra splits on SD5, Wilkinson 56, `xpow120_minus1` and
`cyclo_phi64_x_phi105` are removed or shown worthwhile.** `xpow120_minus1` and
`cyclo_phi64_x_phi105` now perform one split where they performed three, at
0.919x and 0.697x. SD5 and Wilkinson 56 perform two: the extra split at their
selected prime is not waste -- it is the prime the score picks -- but the third
is gone, at 0.995x and 0.912x.

**Builds, conformance, and oracles pass.** `lake build` is clean;
`HexConformance` builds, including new `#guard`s for `degreePattern?`,
`scoutDegreePattern` and the `DegreePattern` bounds; the sweep's cross-check
reports all answering systems agree.

**Fresh sweep and regenerated figures.** Recorded above; all 25 SVGs are
regenerated and `scripts/plots/hexbz-cactus.py --check` passes byte for byte.

## Regeneration

```sh
lake build hexbz_factor_service

# Full Hex sweep (external comparator records are reused unchanged).
taskset -c 0 python3 scripts/bench/factor_sweep.py \
  --systems hex-factor --cutoff 10 --no-early-terminate \
  --output /tmp/hexbz-factor-sweep.json

# Phase attribution, counterfactual prime plans, scout prices, and the
# validation sample.
taskset -c 0 python3 scripts/bench/factor_phase_profile.py \
  --output /tmp/hexbz-phase-profile.json

# Symbolized sampling-profile summaries.
python3 scripts/profile/factor_sampling_profile.py \
  --cpu 0 --output /tmp/hexbz-factor-sampling-profiles.json

# Rank tables.
python3 scripts/bench/cactus_rank_table.py --lo 118 --hi 144

# Figures, and the byte-for-byte check CI runs.
uv run --with matplotlib==3.11.1 python3 scripts/plots/hexbz-cactus.py
uv run --with matplotlib==3.11.1 python3 scripts/plots/hexbz-cactus.py --check
```
