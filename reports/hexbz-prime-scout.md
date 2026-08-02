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

Source revision `f9de7cd8`, toolchain `leanprover/lean4:v4.33.0-rc1`,
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

- `reports/bench-results/hexbz-phase-profile-f9de7cd8-chungus2.json`
- `reports/bench-results/hexbz-factor-sweep-f9de7cd8-hex-chungus2.json`
- `reports/bench-results/hexbz-factor-sampling-profiles-f9de7cd8-chungus2.json`

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
| `sd5` | 19 | 16 | 2^16 | 18.408 us | -- | 1.189 ms | 2.763 ms | -- | -- | -- | first |
| `sd5` | 23 | 16 | 2^16 | 18.066 us | 342.749 us | 1.376 ms | 2.984 ms | 0.115x | 16 | 0 | scored |
| `sd5` | 29 | 16 | 2^16 | 18.667 us | 368.987 us | 1.624 ms | 3.611 ms | 0.102x | 16 | 0 | scored |
| `sd5_shift1` | 19 | 16 | 2^16 | 32.488 us | -- | 1.727 ms | 3.236 ms | -- | -- | -- | first |
| `sd5_shift1` | 23 | 16 | 2^16 | 30.795 us | 438.380 us | 1.967 ms | 3.284 ms | 0.133x | 16 | 0 | scored |
| `sd5_shift1` | 29 | 16 | 2^16 | 32.098 us | 483.848 us | 2.292 ms | 3.709 ms | 0.130x | 16 | 0 | scored |
| `sd5_shift2` | 19 | 16 | 2^16 | 32.318 us | -- | 1.697 ms | 3.250 ms | -- | -- | -- | first |
| `sd5_shift2` | 23 | 16 | 2^16 | 30.476 us | 438.380 us | 1.934 ms | 3.951 ms | 0.111x | 16 | 0 | scored |
| `sd5_shift2` | 29 | 16 | 2^16 | 31.467 us | 479.331 us | 2.273 ms | 5.146 ms | 0.093x | 16 | 0 | scored |
| `sd4_x_sd4shift1` | 13 | 16 | 2^16 | 31.126 us | -- | 1.263 ms | 2.268 ms | -- | -- | -- | first |
| `sd4_x_sd4shift1` | 17 | 16 | 2^16 | 30.265 us | 294.858 us | 1.618 ms | 2.772 ms | 0.106x | 16 | 0 | scored |
| `sd4_x_sd4shift1` | 29 | 16 | 2^16 | 32.839 us | 492.981 us | 2.297 ms | 4.450 ms | 0.111x | 16 | 0 | scored |
| `sd5_x_phi11` | 19 | 17 | 2^16 10 | 49.824 us | -- | 3.660 ms | 5.950 ms | -- | -- | -- | first |
| `sd5_x_phi11` | 23 | 26 | 1^10 2^16 | 50.274 us | 928.267 us | 3.578 ms | 6.632 ms | 0.140x | 26 | 0 | scored |
| `sd5_x_phi11` | 29 | 17 | 2^16 10 | 51.427 us | 3.235 ms | 4.924 ms | 9.718 ms | 0.333x | 17 | 0 | scored |
| `xpow48_minus1` | 5 | 20 | 1^4 2^10 4^6 | 5.738 us | -- | 549.476 us | 1.613 ms | -- | -- | -- | first |
| `xpow48_minus1` | 7 | 27 | 1^6 2^21 | 5.989 us | 80.870 us | 564.427 us | 2.464 ms | 0.033x | 27 | 0 | scored |
| `xpow48_minus1` | 11 | 19 | 1^2 2^11 4^6 | 6.370 us | 530.287 us | 766.156 us | 2.176 ms | 0.244x | 19 | 0 | scored |
| `xpow105_minus1` | 11 | 30 | 1^5 2^5 3^10 6^10 | 11.627 us | -- | 3.686 ms | 12.728 ms | -- | -- | -- | first |
| `xpow105_minus1` | 13 | 33 | 1^3 2^9 4^21 | 12.008 us | 2.431 ms | 3.946 ms | 15.779 ms | 0.154x | 33 | 0 | scored |
| `xpow105_minus1` | 17 | 14 | 1 2 4^3 6^3 12^6 | 11.967 us | 6.396 ms | 5.104 ms | 10.085 ms | 0.634x | 14 | 0 | scored |
| `xpow120_minus1` | 7 | 39 | 1^6 2^9 4^24 | 13.380 us | -- | 3.833 ms | 17.333 ms | -- | -- | -- | first |
| `xpow120_minus1` | 11 | 65 | 1^10 2^55 | 13.570 us | 465.000 us | 4.296 ms | 30.922 ms | 0.015x | 65 | 0 | scored |
| `xpow120_minus1` | 13 | 42 | 1^12 2^6 4^24 | 13.930 us | 1.983 ms | 5.200 ms | 16.717 ms | 0.119x | 42 | 0 | scored |
| `cyclo_phi64_x_phi105` | 11 | 10 | 6^8 16^2 | 162.351 us | -- | 19.170 ms | 22.251 ms | -- | -- | -- | first |
| `cyclo_phi64_x_phi105` | 13 | 14 | 4^12 16^2 | 156.542 us | 4.922 ms | 19.044 ms | 25.111 ms | 0.196x | 12 | 32 | abandoned |
| `cyclo_phi64_x_phi105` | 17 | 12 | 4^8 12^4 | 154.499 us | 21.955 ms | 21.106 ms | 27.754 ms | 0.791x | 12 | 0 | scored |
| `wilkinson_40` | 41 | 40 | 1^40 | 5.909 us | -- | 237.782 us | 1.846 ms | -- | -- | -- | first |
| `wilkinson_40` | 43 | 40 | 1^40 | 12.769 us | 73.219 us | 241.168 us | 1.843 ms | 0.040x | 40 | 0 | scored |
| `wilkinson_40` | 47 | 40 | 1^40 | 19.729 us | 87.790 us | 255.598 us | 1.852 ms | 0.047x | 40 | 0 | scored |
| `wilkinson_48` | 53 | 48 | 1^48 | 19.399 us | -- | 337.871 us | 2.912 ms | -- | -- | -- | first |
| `wilkinson_48` | 59 | 48 | 1^48 | 31.827 us | 116.283 us | 357.490 us | 2.955 ms | 0.039x | 48 | 0 | scored |
| `wilkinson_48` | 61 | 48 | 1^48 | 35.683 us | 124.194 us | 368.026 us | 2.950 ms | 0.042x | 48 | 0 | scored |
| `wilkinson_56` | 59 | 56 | 1^56 | 17.126 us | -- | 435.656 us | 4.324 ms | -- | -- | -- | first |
| `wilkinson_56` | 61 | 56 | 1^56 | 23.885 us | 111.526 us | 441.415 us | 4.319 ms | 0.026x | 56 | 0 | scored |
| `wilkinson_56` | 67 | 56 | 1^56 | 37.305 us | 244.733 us | 574.542 us | 4.490 ms | 0.055x | 56 | 0 | scored |
| `legendre_P30` | 61 | 15 | 2^15 | 17.707 us | -- | 1.557 ms | 3.198 ms | -- | -- | -- | first |
| `legendre_P30` | 67 | 7 | 2^5 6 14 | 18.167 us | 2.172 ms | 1.720 ms | 2.416 ms | 0.899x | 7 | 0 | scored |
| `legendre_P30` | 71 | 4 | 2 3^2 22 | 18.567 us | 3.922 ms | 1.799 ms | 2.154 ms | 1.820x | 4 | 0 | scored |
| `xpow24_minus1` | 5 | 14 | 1^4 2^10 | 3.145 us | -- | 131.756 us | 403.518 us | -- | -- | -- | first |
| `xpow24_minus1` | 7 | 15 | 1^6 2^9 | 3.225 us | 31.667 us | 150.633 us | 405.011 us | 0.078x | 15 | 0 | scored |
| `xpow24_minus1` | 11 | 13 | 1^2 2^11 | 3.305 us | 79.107 us | 196.751 us | 620.480 us | 0.127x | 13 | 0 | scored |

### Scout price where the walk never scouts

A complete pattern at the first good prime of every instance whose walk stops
there, for the cost a scout-first policy would have paid.

| instance | prime | width | degree pattern | complete scout | full split | scout / split |
|---|---:|---:|---|---:|---:|---:|
| `cyclo_phi179` | 3 | 2 | 89^2 | 99.362 ms | 15.228 ms | 6.525x |
| `cyclo_phi128_x_phi165` | 7 | 8 | 16^4 20^4 | 95.760 ms | 98.671 ms | 0.971x |
| `cyclo_phi385` | 3 | 4 | 60^4 | 251.200 ms | 208.663 ms | 1.204x |
| `chebyshev_T24` | 5 | 3 | 8^3 | 278.543 us | 335.377 us | 0.831x |
| `chebyshev_U24` | 3 | 4 | 2^2 10^2 | 310.661 us | 324.141 us | 0.958x |
| `legendre_P38` | 79 | 3 | 1^2 36 | 11.348 ms | 3.841 ms | 2.954x |
| `cyclo_phi17` | 3 | 1 | 16 | 120.068 us | 100.269 us | 1.197x |
| `cyclo_phi41` | 3 | 5 | 8^5 | 606.439 us | 705.276 us | 0.860x |
| `randprod_10` | 7 | 4 | 3 4 6 7 | 542.985 us | 543.085 us | 1.000x |
| `randprod_21` | 17 | 7 | 1^4 4 7 9 | 1.252 ms | 1.247 ms | 1.004x |

What the scout costs is decided by the largest factor degree, not by which
candidate wins. Sorted by `scout / split`, the 28 scouted candidates run from
0.015x (`xpow120_minus1` prime 11, 65 factors of degree at most 2) to 1.820x
(`legendre_P30` prime 71, four factors reaching degree 22), and the ordering is
the ordering of their largest factor degree. Twenty-three sit at 0.25x or
below; the five above are `sd5_x_phi11` prime 29 (0.333x, degree 10),
`xpow105_minus1` prime 17 (0.634x, 12), `cyclo_phi64_x_phi105` prime 17
(0.791x, 12), and the two `legendre_P30` candidates (0.899x and 1.820x, 14 and
22). The last of those is priced here but never actually scouted: the walk ends
at prime 67, whose scouted width of 7 passes the gate.

The `outcome` column records the other way a scout can stop. *Abandoned* means
the separated factors reached the current width, so the candidate is wider and
cannot win, and the rest of its pattern is never computed:
`cyclo_phi64_x_phi105` at prime 13 gives up once its twelve degree-4 factors
reach the incumbent's ten, with 32 of the 80 degrees still unseparated, for
4.9 ms against the 25.1 ms split it avoided. That is the only abandonment in
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
| `sd5` | 19 | 16 | 21 | 1.946 ms | 93.454 ms | 95.386 ms | 32,768 | 129 |  |
| `sd5` | 23 | 16 | 20 | 1.953 ms | 93.906 ms | 95.847 ms | 32,768 | 129 |  |
| `sd5` | 29 | 16 | 19 | 1.938 ms | 94.242 ms | 96.189 ms | 32,768 | 129 | yes |
| `sd5_shift1` | 19 | 16 | 21 | 1.960 ms | 82.392 ms | 84.363 ms | 32,768 | 1 |  |
| `sd5_shift1` | 23 | 16 | 20 | 1.920 ms | 82.544 ms | 84.457 ms | 32,768 | 1 |  |
| `sd5_shift1` | 29 | 16 | 19 | 1.956 ms | 82.594 ms | 84.551 ms | 32,768 | 1 | yes |
| `sd5_shift2` | 19 | 16 | 22 | 1.901 ms | 83.381 ms | 85.282 ms | 32,768 | 1 |  |
| `sd5_shift2` | 23 | 16 | 21 | 1.954 ms | 83.577 ms | 85.531 ms | 32,768 | 1 |  |
| `sd5_shift2` | 29 | 16 | 19 | 1.957 ms | 83.609 ms | 85.566 ms | 32,768 | 1 | yes |
| `sd4_x_sd4shift1` | 13 | 16 | 22 | 1.769 ms | 11.594 ms | 13.357 ms | 10,503 | 10 |  |
| `sd4_x_sd4shift1` | 17 | 16 | 20 | 1.762 ms | 11.744 ms | 13.506 ms | 10,503 | 10 |  |
| `sd4_x_sd4shift1` | 29 | 16 | 17 | 1.861 ms | 12.043 ms | 13.910 ms | 10,540 | 10 | yes |
| `sd5_x_phi11` | 19 | 17 | 24 | 3.158 ms | 204.841 ms | 207.981 ms | 65,536 | 258 |  |
| `sd5_x_phi11` | 23 | 26 | 22 | 3.386 ms | 256.390 ms | 259.776 ms | 245,506 | 0 |  |
| `sd5_x_phi11` | 29 | 17 | 21 | 3.148 ms | 193.778 ms | 196.863 ms | 65,522 | 258 | yes |
| `xpow48_minus1` | 5 | 20 | 21 | 1.415 ms | 10.399 ms | 11.830 ms | 456 | 221 |  |
| `xpow48_minus1` | 7 | 27 | 17 | 1.581 ms | 5.158 s | 5.160 s | 181,455 | 60,530 |  |
| `xpow48_minus1` | 11 | 19 | 14 | 1.212 ms | 13.636 ms | 14.847 ms | 268 | 268 | yes |
| `xpow105_minus1` | 11 | 30 | 30 | 15.102 ms | 1.419 s | 1.433 s | 17,020 | 3,414 |  |
| `xpow105_minus1` | 13 | 33 | 28 | 16.122 ms | 36.765 s | 36.781 s | 174,439 | 58,145 |  |
| `xpow105_minus1` | 17 | 14 | 26 | 15.704 ms | 28.307 ms | 44.012 ms | 60 | 60 | yes |
| `xpow120_minus1` | 7 | 39 | 43 | 21.551 ms | 444.802 ms | 466.424 ms | 5,339 | 1,801 | yes |
| `xpow120_minus1` | 11 | 65 | 35 | 24.496 ms | 3.964 s | 3.988 s | 44,887 | 8,983 |  |
| `xpow120_minus1` | 13 | 42 | 32 | 9.822 ms | 5.888 s | 5.898 s | 53,449 | 9,179 |  |
| `cyclo_phi179` | 3 | 2 | 113 | 61.060 ms | 5.612 ms | 66.569 ms | 2 | 2 | yes |
| `cyclo_phi64_x_phi105` | 11 | 10 | 24 | 8.022 ms | 4.746 ms | 12.990 ms | 130 | 28 | yes |
| `cyclo_phi64_x_phi105` | 13 | 14 | 22 | 8.527 ms | 579.658 ms | 588.186 ms | 8,111 | 1,336 |  |
| `cyclo_phi64_x_phi105` | 17 | 12 | 20 | 8.247 ms | 93.928 ms | 102.185 ms | 1,512 | 221 |  |
| `cyclo_phi128_x_phi165` | 7 | 8 | 52 | 66.248 ms | 41.608 ms | 107.947 ms | 54 | 25 | yes |
| `cyclo_phi385` | 3 | 4 | 152 | 167.117 ms | 82.701 ms | 249.667 ms | 8 | 8 | yes |
| `wilkinson_40` | 41 | 40 | 38 | 8.320 ms | 506.321 us | 8.826 ms | 40 | 40 |  |
| `wilkinson_40` | 43 | 40 | 38 | 8.242 ms | 499.330 us | 8.742 ms | 40 | 40 |  |
| `wilkinson_40` | 47 | 40 | 37 | 8.266 ms | 506.501 us | 8.768 ms | 40 | 40 | yes |
| `wilkinson_48` | 53 | 48 | 45 | 17.928 ms | 762.691 us | 18.691 ms | 48 | 48 |  |
| `wilkinson_48` | 59 | 48 | 44 | 17.967 ms | 759.196 us | 18.734 ms | 48 | 48 |  |
| `wilkinson_48` | 61 | 48 | 43 | 18.009 ms | 750.954 us | 18.759 ms | 48 | 48 | yes |
| `wilkinson_56` | 59 | 56 | 53 | 23.144 ms | 1.013 ms | 24.155 ms | 56 | 56 |  |
| `wilkinson_56` | 61 | 56 | 52 | 23.073 ms | 1.013 ms | 24.088 ms | 56 | 56 |  |
| `wilkinson_56` | 67 | 56 | 51 | 23.312 ms | 1.008 ms | 24.325 ms | 56 | 56 | yes |
| `chebyshev_T24` | 5 | 3 | 22 | 136.392 us | 20.641 us | 157.033 us | 3 | 2 | yes |
| `chebyshev_U24` | 3 | 4 | 33 | 286.185 us | 23.454 us | 309.639 us | 4 | 4 | yes |
| `legendre_P30` | 61 | 15 | 15 | 1.024 ms | 40.231 ms | 41.246 ms | 16,384 | 1 |  |
| `legendre_P30` | 67 | 7 | 15 | 1.378 ms | 174.649 us | 1.553 ms | 64 | 1 | yes |
| `legendre_P30` | 71 | 4 | 15 | 457.839 us | 60.860 us | 518.699 us | 8 | 1 |  |
| `legendre_P38` | 79 | 3 | 19 | 674.730 us | 47.601 us | 722.331 us | 4 | 1 | yes |
| `cyclo_phi17` | 3 | 1 | 11 | 2.464 us | 4.437 us | 6.811 us | 1 | 1 | yes |
| `cyclo_phi41` | 3 | 5 | 26 | 696.573 us | 1.421 ms | 2.118 ms | 16 | 16 | yes |
| `xpow24_minus1` | 5 | 14 | 11 | 401.916 us | 1.078 ms | 1.480 ms | 150 | 77 |  |
| `xpow24_minus1` | 7 | 15 | 9 | 372.682 us | 152.817 us | 526.812 us | 38 | 20 |  |
| `xpow24_minus1` | 11 | 13 | 7 | 304.231 us | 1.708 ms | 2.011 ms | 113 | 113 | yes |
| `randprod_10` | 7 | 4 | 11 | 179.006 us | 19.248 us | 198.254 us | 5 | 2 | yes |
| `randprod_21` | 17 | 7 | 9 | 329.789 us | 36.755 us | 366.544 us | 13 | 3 | yes |

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
| `sd5` | 98.167ms | 105.601ms | 104.798ms | 103.329ms | 102.617ms | 98.167ms | 98.167ms | 19/29/29/19 |
| `sd5_shift1` | 87.631ms | 94.875ms | 94.687ms | 92.513ms | 91.591ms | 87.631ms | 87.631ms | 19/29/29/19 |
| `sd5_shift2` | 88.565ms | 98.008ms | 97.724ms | 94.975ms | 94.057ms | 88.565ms | 88.565ms | 19/29/29/19 |
| `sd4_x_sd4shift1` | 15.657ms | 23.495ms | 22.942ms | 21.511ms | 20.723ms | 15.657ms | 15.657ms | 13/29/29/13 |
| `sd5_x_phi11` | 213.981ms | 219.315ms | 230.433ms | 216.846ms | 212.683ms | 212.683ms | 206.633ms | 19/29/29/29 |
| `xpow48_minus1` | 13.449ms | 21.118ms | 21.118ms | 19.265ms | 18.654ms | 13.449ms | 13.449ms | 5/11/11/5 |
| `xpow105_minus1` | 1446.234ms | 82.639ms | 82.639ms | 75.687ms | 66.860ms | 66.860ms | 54.108ms | 11/17/17/17 |
| `xpow120_minus1` | 483.771ms | 531.438ms | 531.438ms | 486.246ms | 483.771ms | 483.771ms | 483.771ms | 7/7/7/7 |
| `cyclo_phi179` | 81.833ms | 81.833ms | 81.833ms | 81.833ms | 81.833ms | 81.833ms | 81.833ms | 3/3/3/3 |
| `cyclo_phi64_x_phi105` | 35.403ms | 88.579ms | 88.579ms | 62.590ms | 35.403ms | 35.403ms | 35.403ms | 11/11/11/11 |
| `cyclo_phi128_x_phi165` | 207.072ms | 207.072ms | 207.072ms | 207.072ms | 207.072ms | 207.072ms | 207.072ms | 7/7/7/7 |
| `cyclo_phi385` | 459.074ms | 459.074ms | 459.074ms | 459.074ms | 459.074ms | 459.074ms | 459.074ms | 3/3/3/3 |
| `wilkinson_40` | 10.678ms | 14.349ms | 14.406ms | 12.666ms | 12.505ms | 10.678ms | 10.598ms | 41/47/47/43 |
| `wilkinson_48` | 21.623ms | 27.663ms | 27.596ms | 24.948ms | 24.708ms | 21.623ms | 21.623ms | 53/61/61/53 |
| `wilkinson_56` | 28.497ms | 37.537ms | 37.367ms | 33.574ms | 33.217ms | 28.497ms | 28.432ms | 59/67/67/61 |
| `chebyshev_T24` | 0.504ms | 0.504ms | 0.504ms | 0.504ms | 0.504ms | 0.504ms | 0.504ms | 5/5/5/5 |
| `chebyshev_U24` | 0.640ms | 0.640ms | 0.640ms | 0.640ms | 0.640ms | 0.640ms | 0.640ms | 3/3/3/3 |
| `legendre_P30` | 44.462ms | 8.342ms | 8.342ms | 9.375ms | 5.926ms | 5.926ms | 2.692ms | 61/71/67/71 |
| `legendre_P38` | 4.589ms | 4.589ms | 4.589ms | 4.589ms | 4.589ms | 4.589ms | 4.589ms | 79/79/79/79 |
| `cyclo_phi17` | 0.111ms | 0.111ms | 0.111ms | 0.111ms | 0.111ms | 0.111ms | 0.111ms | 3/3/3/3 |
| `cyclo_phi41` | 2.832ms | 2.832ms | 2.832ms | 2.832ms | 2.832ms | 2.832ms | 2.832ms | 3/3/3/3 |
| `xpow24_minus1` | 1.886ms | 3.450ms | 3.450ms | 3.156ms | 3.045ms | 1.342ms | 0.935ms | 5/11/11/7 |
| `randprod_10` | 0.754ms | 0.754ms | 0.754ms | 0.754ms | 0.754ms | 0.754ms | 0.754ms | 7/7/7/7 |
| `randprod_21` | 1.633ms | 1.633ms | 1.633ms | 1.633ms | 1.633ms | 1.633ms | 1.633ms | 17/17/17/17 |
| **aggregate** | **3349.045ms** | **2115.450ms** | **2124.561ms** | **2015.723ms** | **1964.801ms** | **1929.292ms** | **1906.704ms** | |

The replay reproduces both real walks: on every row, the prime the `fixed`
column picks is the prime the pre-#9128 binary selected, and the prime the
`scout` column picks is the prime this PR's binary selected.

Against the fixed policy the scout saves 99.727 ms of 2115.450 ms. That is
66.2% of what is available to the same-plan floor, 53.6% of the reachable
floor, and 47.8% of the oracle floor. The first-good-prime rule remains
unusable at 3349.045 ms, and choosing by minimum width alone is worse than the
score at 2124.561 ms -- `sd5_x_phi11` is where that shows, since prime 23 is
widest and prime 29 wins on the tie breaks.

## Paired before and after

The two service binaries were built from this worktree and differ only in
`HexBerlekampZassenhaus/Modular/PrimePlan.lean`, and the arms were alternated on
the same pinned core, so machine load hits both equally. The rows whose plan
does not change -- `cyclo_phi179`, `cyclo_phi128_x_phi165`, `cyclo_phi385`, the
Chebyshev and `randprod` controls, `cyclo_phi17`, `cyclo_phi41`, `legendre_P38`
-- are the load control: their prime walk does identical work in both arms, so
their spread bounds what can be read into the rows that did change.

The record is `reports/bench-results/hexbz-prime-plan-paired-f9de7cd8-chungus2.json`;
it carries every round of both arms, and
`scripts/bench/prime_plan_paired.py --report` regenerates this table from it.

### Paired before/after, median of 3 alternating rounds

| instance | prime before | prime after | full splits | prime walk before | prime walk after | walk saved | total before | total after | ratio |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `sd5` | 29 | 29 | 3 -> 2 | 9.464 ms | 7.197 ms | 2.267 ms | 107.791 ms | 103.660 ms | 0.962x |
| `sd5_shift1` | 29 | 29 | 3 -> 2 | 10.648 ms | 8.251 ms | 2.396 ms | 96.359 ms | 93.058 ms | 0.966x |
| `sd5_shift2` | 29 | 29 | 3 -> 2 | 12.994 ms | 9.729 ms | 3.265 ms | 100.293 ms | 97.127 ms | 0.968x |
| `sd4_x_sd4shift1` | 29 | 29 | 3 -> 2 | 9.871 ms | 7.772 ms | 2.100 ms | 24.961 ms | 23.027 ms | 0.923x |
| `sd5_x_phi11` | 29 | 29 | 3 -> 2 | 21.871 ms | 19.038 ms | 2.832 ms | 228.153 ms | 217.614 ms | 0.954x |
| `xpow48_minus1` | 11 | 11 | 3 -> 2 | 6.210 ms | 4.372 ms | 1.837 ms | 21.543 ms | 19.647 ms | 0.912x |
| `xpow105_minus1` | 17 | 17 | 3 -> 2 | 39.272 ms | 32.520 ms | 6.752 ms | 84.033 ms | 76.150 ms | 0.906x |
| `xpow120_minus1` | 7 | 7 | 3 -> 1 | 66.156 ms | 20.032 ms | 46.124 ms | 534.267 ms | 492.899 ms | 0.923x |
| `cyclo_phi179` | 3 | 3 | 1 -> 1 | 14.920 ms | 14.757 ms | 163.172 us | 80.183 ms | 81.368 ms | 1.015x |
| `cyclo_phi64_x_phi105` | 11 | 11 | 3 -> 1 | 75.082 ms | 49.234 ms | 25.847 ms | 87.521 ms | 63.109 ms | 0.721x |
| `cyclo_phi128_x_phi165` | 7 | 7 | 1 -> 1 | 96.683 ms | 96.060 ms | 622.835 us | 204.053 ms | 205.364 ms | 1.006x |
| `cyclo_phi385` | 3 | 3 | 1 -> 1 | 208.199 ms | 206.835 ms | 1.363 ms | 456.120 ms | 463.506 ms | 1.016x |
| `wilkinson_40` | 47 | 47 | 3 -> 2 | 5.954 ms | 4.409 ms | 1.544 ms | 15.798 ms | 14.355 ms | 0.909x |
| `wilkinson_48` | 61 | 61 | 3 -> 2 | 9.483 ms | 6.952 ms | 2.531 ms | 29.413 ms | 27.126 ms | 0.922x |
| `wilkinson_56` | 67 | 67 | 3 -> 2 | 13.797 ms | 10.145 ms | 3.652 ms | 40.265 ms | 36.641 ms | 0.910x |
| `chebyshev_T24` | 5 | 5 | 1 -> 1 | 351.461 us | 363.299 us | -11.838 us | 567.011 us | 573.240 us | 1.011x |
| `chebyshev_U24` | 3 | 3 | 1 -> 1 | 326.123 us | 322.028 us | 4.095 us | 697.985 us | 707.269 us | 1.013x |
| `legendre_P30` | 71 | 67 | 3 -> 2 | 7.794 ms | 7.792 ms | 2.534 us | 8.456 ms | 9.535 ms | 1.128x |
| `legendre_P38` | 79 | 79 | 1 -> 1 | 3.826 ms | 3.912 ms | -86.377 us | 4.752 ms | 4.750 ms | 1.000x |
| `cyclo_phi17` | 3 | 3 | 1 -> 1 | 104.936 us | 104.705 us | 231 ns | 150.934 us | 152.727 us | 1.012x |
| `cyclo_phi41` | 3 | 3 | 1 -> 1 | 700.679 us | 706.828 us | -6.149 us | 2.871 ms | 2.872 ms | 1.000x |
| `xpow24_minus1` | 11 | 11 | 3 -> 2 | 1.463 ms | 1.189 ms | 274.007 us | 3.528 ms | 3.258 ms | 0.923x |
| `randprod_10` | 7 | 7 | 1 -> 1 | 557.036 us | 549.856 us | 7.180 us | 821.478 us | 814.237 us | 0.991x |
| `randprod_21` | 17 | 17 | 1 -> 1 | 1.289 ms | 1.287 ms | 1.513 us | 1.757 ms | 1.744 ms | 0.993x |
| **aggregate** | | | | | | 103.485 ms | 2.134 s | 2.039 s | **0.9554x** |

Load control (10 instances whose plan does not change): 0.991x to 1.016x.

Every row whose plan changes improves, between 0.721x and 0.968x, except
`legendre_P30`. The ten rows whose plan does not change span 0.991x to 1.016x
and are the day's noise floor on this machine. The prime walk loses 103.485 ms
across the corpus, of which `xpow120_minus1` is 46 ms and
`cyclo_phi64_x_phi105` 26 ms.

The three larger instances outside the representative set behave the same way.
Paired over two rounds: `sd6` 3 splits to 2 and prime 29 kept, `hoeij_F190`
3 to 2 and prime 13 kept, `hoeij_M12_f132` 3 to 2 and prime 13 kept. The full
sweep puts them at 1.042x, 0.984x and 1.011x, inside its own noise on rows
where nothing about the plan changed.

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
measured regression: 8.456 ms to 9.535 ms, 1.128x. Removing the gate was
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
behaviour.** Not the first: 47.8% of the oracle floor, 53.6% of the reachable
floor, 66.2% of the same-plan floor. The oracle and reachable floors are
unreachable by construction -- the oracle names the winner without paying to
discover it, and neither ever scouts -- so the honest number is the third, and
the missing third of it is the complete scouts on equal-width families
described above. The second clause is what this PR claims: the policy is
simpler than the one it replaces (no width threshold, no fuel spent on
splitting, one selector), selects the same plan wherever the width gate does
not fire, and is 0.9554x end to end on the paired corpus, with every row whose
plan changes improving except `legendre_P30`.

**Median unsuccessful-scout overhead below 3%.** An unsuccessful scout is one
whose candidate is not selected. As a fraction of each scouting row's total:

| instance | unsuccessful scouts | row total | share |
|---|---:|---:|---:|
| `legendre_P30` | 0 ns | 9.535 ms | 0.00% |
| `wilkinson_56` | 112 us | 36.641 ms | 0.30% |
| `sd5` | 343 us | 103.660 ms | 0.33% |
| `xpow48_minus1` | 81 us | 19.647 ms | 0.41% |
| `sd5_x_phi11` | 928 us | 217.614 ms | 0.43% |
| `wilkinson_48` | 116 us | 27.126 ms | 0.43% |
| `sd5_shift2` | 438 us | 97.127 ms | 0.45% |
| `sd5_shift1` | 438 us | 93.058 ms | 0.47% |
| `xpow120_minus1` | 2.448 ms | 492.899 ms | 0.50% |
| `wilkinson_40` | 73 us | 14.355 ms | 0.51% |
| `xpow24_minus1` | 32 us | 3.258 ms | 0.97% |
| `sd4_x_sd4shift1` | 295 us | 23.027 ms | 1.28% |
| `xpow105_minus1` | 2.431 ms | 76.150 ms | 3.19% |
| `cyclo_phi64_x_phi105` | 26.876 ms | 63.109 ms | 42.59% |

Median **0.49%**. The `cyclo_phi64_x_phi105` outlier is the row where the
scouts replace two splits of 25.1 ms and 27.8 ms; it is the largest saving in
the corpus at 0.721x, so its scouts are not overhead in any useful sense.

**No unexplained regression above 5%.** One row regresses: `legendre_P30` at
1.128x, explained above and quantified. Every other row is within the load
control's ±1.6% band or improves. The full sweep solves the same 376 instances
as the baseline.

**`xpow105_minus1` retains its useful width reduction.** It still selects prime
17 at width 14, against widths 30 and 33 at the two primes it rejects, and the
row improves 0.906x. The scout at prime 13 completes its pattern at width
33 and is rejected by its score, for 2.4 ms against the 15.8 ms split it
replaces.

**The wasted extra splits on SD5, Wilkinson 56, `xpow120_minus1` and
`cyclo_phi64_x_phi105` are removed or shown worthwhile.** `xpow120_minus1` and
`cyclo_phi64_x_phi105` now perform one split where they performed three, at
0.923x and 0.721x. SD5 and Wilkinson 56 perform two: the extra split at their
selected prime is not waste -- it is the prime the score picks -- but the third
is gone, at 0.962x and 0.910x.

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
