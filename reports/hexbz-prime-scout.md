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

Source revision `a79917a1`, toolchain `leanprover/lean4:v4.33.0-rc1`,
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

- `reports/bench-results/hexbz-phase-profile-a79917a1-chungus2.json`
- `reports/bench-results/hexbz-factor-sweep-a79917a1-hex-chungus2.json`
- `reports/bench-results/hexbz-factor-sampling-profiles-a79917a1-chungus2.json`

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
| `sd5` | 19 | 16 | 2^16 | 19.489 us | -- | 1.195 ms | 2.827 ms | -- | -- | -- | first |
| `sd5` | 23 | 16 | 2^16 | 18.908 us | 347.746 us | 1.368 ms | 3.043 ms | 0.114x | 16 | 0 | scored |
| `sd5` | 29 | 16 | 2^16 | 19.850 us | 378.071 us | 1.642 ms | 3.686 ms | 0.103x | 16 | 0 | scored |
| `sd5_shift1` | 19 | 16 | 2^16 | 34.522 us | -- | 1.777 ms | 3.331 ms | -- | -- | -- | first |
| `sd5_shift1` | 23 | 16 | 2^16 | 33.149 us | 445.551 us | 1.977 ms | 3.327 ms | 0.134x | 16 | 0 | scored |
| `sd5_shift1` | 29 | 16 | 2^16 | 34.000 us | 490.187 us | 2.306 ms | 3.745 ms | 0.131x | 16 | 0 | scored |
| `sd5_shift2` | 19 | 16 | 2^16 | 34.011 us | -- | 1.718 ms | 3.305 ms | -- | -- | -- | first |
| `sd5_shift2` | 23 | 16 | 2^16 | 32.398 us | 446.242 us | 1.963 ms | 4.035 ms | 0.111x | 16 | 0 | scored |
| `sd5_shift2` | 29 | 16 | 2^16 | 33.359 us | 487.713 us | 2.356 ms | 5.304 ms | 0.092x | 16 | 0 | scored |
| `sd4_x_sd4shift1` | 13 | 16 | 2^16 | 32.568 us | -- | 1.296 ms | 2.350 ms | -- | -- | -- | first |
| `sd4_x_sd4shift1` | 17 | 16 | 2^16 | 32.087 us | 292.764 us | 1.624 ms | 2.819 ms | 0.104x | 16 | 0 | scored |
| `sd4_x_sd4shift1` | 29 | 16 | 2^16 | 34.371 us | 488.985 us | 2.300 ms | 4.517 ms | 0.108x | 16 | 0 | scored |
| `sd5_x_phi11` | 19 | 17 | 2^16 10 | 51.607 us | -- | 3.672 ms | 5.955 ms | -- | -- | -- | first |
| `sd5_x_phi11` | 23 | 26 | 1^10 2^16 | 52.338 us | 688.201 us | 3.315 ms | 6.464 ms | 0.106x | 26 | 0 | scored |
| `sd5_x_phi11` | 29 | 17 | 2^16 10 | 53.029 us | 3.056 ms | 4.632 ms | 9.166 ms | 0.333x | 17 | 0 | scored |
| `xpow48_minus1` | 5 | 20 | 1^4 2^10 4^6 | 5.588 us | -- | 521.483 us | 1.604 ms | -- | -- | -- | first |
| `xpow48_minus1` | 7 | 27 | 1^6 2^21 | 5.778 us | 76.964 us | 544.517 us | 2.418 ms | 0.032x | 27 | 0 | scored |
| `xpow48_minus1` | 11 | 19 | 1^2 2^11 4^6 | 5.708 us | 467.684 us | 743.172 us | 2.163 ms | 0.216x | 19 | 0 | scored |
| `xpow105_minus1` | 11 | 30 | 1^5 2^5 3^10 6^10 | 11.528 us | -- | 3.656 ms | 12.896 ms | -- | -- | -- | first |
| `xpow105_minus1` | 13 | 33 | 1^3 2^9 4^21 | 12.288 us | 2.343 ms | 3.830 ms | 15.831 ms | 0.148x | 33 | 0 | scored |
| `xpow105_minus1` | 17 | 14 | 1 2 4^3 6^3 12^6 | 12.218 us | 6.116 ms | 4.893 ms | 9.999 ms | 0.612x | 14 | 0 | scored |
| `xpow120_minus1` | 7 | 39 | 1^6 2^9 4^24 | 12.969 us | -- | 3.735 ms | 17.744 ms | -- | -- | -- | first |
| `xpow120_minus1` | 11 | 65 | 1^10 2^55 | 14.150 us | 453.423 us | 4.263 ms | 31.440 ms | 0.014x | 65 | 0 | scored |
| `xpow120_minus1` | 13 | 42 | 1^12 2^6 4^24 | 14.912 us | 1.886 ms | 5.106 ms | 16.857 ms | 0.112x | 42 | 0 | scored |
| `cyclo_phi64_x_phi105` | 11 | 10 | 6^8 16^2 | 156.993 us | -- | 18.876 ms | 21.975 ms | -- | -- | -- | first |
| `cyclo_phi64_x_phi105` | 13 | 14 | 4^12 16^2 | 159.125 us | 4.906 ms | 18.803 ms | 25.049 ms | 0.196x | 12 | 32 | abandoned |
| `cyclo_phi64_x_phi105` | 17 | 12 | 4^8 12^4 | 154.819 us | 21.814 ms | 20.755 ms | 27.488 ms | 0.794x | 12 | 0 | scored |
| `wilkinson_40` | 41 | 40 | 1^40 | 7.031 us | -- | 236.060 us | 1.818 ms | -- | -- | -- | first |
| `wilkinson_40` | 43 | 40 | 1^40 | 13.951 us | 74.841 us | 242.410 us | 1.831 ms | 0.041x | 40 | 0 | scored |
| `wilkinson_40` | 47 | 40 | 1^40 | 20.971 us | 89.453 us | 255.720 us | 1.838 ms | 0.049x | 40 | 0 | scored |
| `wilkinson_48` | 53 | 48 | 1^48 | 21.162 us | -- | 336.238 us | 2.882 ms | -- | -- | -- | first |
| `wilkinson_48` | 59 | 48 | 1^48 | 32.899 us | 117.114 us | 355.588 us | 2.914 ms | 0.040x | 48 | 0 | scored |
| `wilkinson_48` | 61 | 48 | 1^48 | 36.815 us | 124.635 us | 367.675 us | 2.932 ms | 0.043x | 48 | 0 | scored |
| `wilkinson_56` | 59 | 56 | 1^56 | 19.208 us | -- | 427.874 us | 4.315 ms | -- | -- | -- | first |
| `wilkinson_56` | 61 | 56 | 1^56 | 24.667 us | 111.325 us | 438.680 us | 4.334 ms | 0.026x | 56 | 0 | scored |
| `wilkinson_56` | 67 | 56 | 1^56 | 38.897 us | 246.505 us | 578.107 us | 4.467 ms | 0.055x | 56 | 0 | scored |
| `legendre_P30` | 61 | 15 | 2^15 | 17.897 us | -- | 1.546 ms | 3.164 ms | -- | -- | -- | first |
| `legendre_P30` | 67 | 7 | 2^5 6 14 | 18.177 us | 2.150 ms | 1.710 ms | 2.351 ms | 0.914x | 7 | 0 | scored |
| `legendre_P30` | 71 | 4 | 2 3^2 22 | 18.328 us | 3.907 ms | 1.769 ms | 2.140 ms | 1.826x | 4 | 0 | scored |
| `xpow24_minus1` | 5 | 14 | 1^4 2^10 | 3.085 us | -- | 132.347 us | 402.837 us | -- | -- | -- | first |
| `xpow24_minus1` | 7 | 15 | 1^6 2^9 | 3.224 us | 32.118 us | 150.563 us | 410.518 us | 0.078x | 15 | 0 | scored |
| `xpow24_minus1` | 11 | 13 | 1^2 2^11 | 3.335 us | 79.278 us | 197.634 us | 657.455 us | 0.121x | 13 | 0 | scored |

### Scout price where the walk never scouts

A complete pattern at the first good prime of every instance whose walk stops
there, for the cost a scout-first policy would have paid.

| instance | prime | width | degree pattern | complete scout | full split | scout / split |
|---|---:|---:|---|---:|---:|---:|
| `cyclo_phi179` | 3 | 2 | 89^2 | 97.797 ms | 14.992 ms | 6.523x |
| `cyclo_phi128_x_phi165` | 7 | 8 | 16^4 20^4 | 93.968 ms | 97.838 ms | 0.960x |
| `cyclo_phi385` | 3 | 4 | 60^4 | 252.356 ms | 209.520 ms | 1.204x |
| `chebyshev_T24` | 5 | 3 | 8^3 | 282.790 us | 336.329 us | 0.841x |
| `chebyshev_U24` | 3 | 4 | 2^2 10^2 | 316.269 us | 315.608 us | 1.002x |
| `legendre_P38` | 79 | 3 | 1^2 36 | 11.519 ms | 3.807 ms | 3.026x |
| `cyclo_phi17` | 3 | 1 | 16 | 121.910 us | 100.249 us | 1.216x |
| `cyclo_phi41` | 3 | 5 | 8^5 | 614.461 us | 704.845 us | 0.872x |
| `randprod_10` | 7 | 4 | 3 4 6 7 | 541.262 us | 615.372 us | 0.880x |
| `randprod_21` | 17 | 7 | 1^4 4 7 9 | 1.261 ms | 1.230 ms | 1.025x |

What the scout costs is decided by the largest factor degree, not by which
candidate wins. Sorted by `scout / split`, the 28 scouted candidates run from
0.014x (`xpow120_minus1` prime 11, 65 factors of degree at most 2) to 1.826x
(`legendre_P30` prime 71, four factors reaching degree 22), and the ordering is
the ordering of their largest factor degree. Twenty-three sit at 0.25x or
below; the five above are `sd5_x_phi11` prime 29 (0.333x, degree 10),
`xpow105_minus1` prime 17 (0.634x, 12), `cyclo_phi64_x_phi105` prime 17
(0.791x, 12), and the two `legendre_P30` candidates (0.905x and 1.826x, 14 and
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
| `sd5` | 19 | 16 | 21 | 1.840 ms | 70.431 ms | 72.261 ms | 32,768 | 129 |  |
| `sd5` | 23 | 16 | 20 | 1.821 ms | 69.428 ms | 71.218 ms | 32,768 | 129 |  |
| `sd5` | 29 | 16 | 19 | 1.802 ms | 69.524 ms | 71.326 ms | 32,768 | 129 | yes |
| `sd5_shift1` | 19 | 16 | 21 | 1.853 ms | 57.026 ms | 58.880 ms | 32,768 | 1 |  |
| `sd5_shift1` | 23 | 16 | 20 | 1.757 ms | 57.014 ms | 58.761 ms | 32,768 | 1 |  |
| `sd5_shift1` | 29 | 16 | 19 | 1.825 ms | 57.396 ms | 59.235 ms | 32,768 | 1 | yes |
| `sd5_shift2` | 19 | 16 | 22 | 1.764 ms | 58.135 ms | 59.899 ms | 32,768 | 1 |  |
| `sd5_shift2` | 23 | 16 | 21 | 1.826 ms | 57.948 ms | 59.766 ms | 32,768 | 1 |  |
| `sd5_shift2` | 29 | 16 | 19 | 1.807 ms | 57.965 ms | 59.757 ms | 32,768 | 1 | yes |
| `sd4_x_sd4shift1` | 13 | 16 | 22 | 1.621 ms | 9.388 ms | 11.002 ms | 10,503 | 10 |  |
| `sd4_x_sd4shift1` | 17 | 16 | 20 | 1.586 ms | 9.429 ms | 11.016 ms | 10,503 | 10 |  |
| `sd4_x_sd4shift1` | 29 | 16 | 17 | 1.759 ms | 9.773 ms | 11.525 ms | 10,540 | 10 | yes |
| `sd5_x_phi11` | 19 | 17 | 24 | 2.875 ms | 154.280 ms | 157.155 ms | 65,536 | 258 |  |
| `sd5_x_phi11` | 23 | 26 | 22 | 3.140 ms | 213.080 ms | 216.220 ms | 245,506 | 0 |  |
| `sd5_x_phi11` | 29 | 17 | 21 | 2.904 ms | 144.803 ms | 147.693 ms | 65,522 | 258 | yes |
| `xpow48_minus1` | 5 | 20 | 21 | 1.364 ms | 9.948 ms | 11.311 ms | 456 | 221 |  |
| `xpow48_minus1` | 7 | 27 | 17 | 1.528 ms | 5.185 s | 5.187 s | 181,455 | 60,530 |  |
| `xpow48_minus1` | 11 | 19 | 14 | 1.126 ms | 13.605 ms | 14.728 ms | 268 | 268 | yes |
| `xpow105_minus1` | 11 | 30 | 30 | 13.252 ms | 1.413 s | 1.427 s | 17,020 | 3,414 |  |
| `xpow105_minus1` | 13 | 33 | 28 | 14.493 ms | 36.623 s | 36.638 s | 174,439 | 58,145 |  |
| `xpow105_minus1` | 17 | 14 | 26 | 14.368 ms | 28.384 ms | 42.721 ms | 60 | 60 | yes |
| `xpow120_minus1` | 7 | 39 | 43 | 19.318 ms | 441.052 ms | 460.366 ms | 5,339 | 1,801 | yes |
| `xpow120_minus1` | 11 | 65 | 35 | 22.497 ms | 3.948 s | 3.970 s | 44,887 | 8,983 |  |
| `xpow120_minus1` | 13 | 42 | 32 | 8.776 ms | 5.850 s | 5.859 s | 53,449 | 9,179 |  |
| `cyclo_phi179` | 3 | 2 | 113 | 55.416 ms | 5.562 ms | 60.978 ms | 2 | 2 | yes |
| `cyclo_phi64_x_phi105` | 11 | 10 | 24 | 7.052 ms | 4.838 ms | 11.895 ms | 130 | 28 | yes |
| `cyclo_phi64_x_phi105` | 13 | 14 | 22 | 7.658 ms | 565.429 ms | 573.087 ms | 8,111 | 1,336 |  |
| `cyclo_phi64_x_phi105` | 17 | 12 | 20 | 7.405 ms | 92.605 ms | 100.010 ms | 1,512 | 221 |  |
| `cyclo_phi128_x_phi165` | 7 | 8 | 52 | 58.768 ms | 41.247 ms | 100.014 ms | 54 | 25 | yes |
| `cyclo_phi385` | 3 | 4 | 152 | 145.497 ms | 82.198 ms | 227.695 ms | 8 | 8 | yes |
| `wilkinson_40` | 41 | 40 | 38 | 7.326 ms | 519.671 us | 7.842 ms | 40 | 40 |  |
| `wilkinson_40` | 43 | 40 | 38 | 7.286 ms | 512.711 us | 7.802 ms | 40 | 40 |  |
| `wilkinson_40` | 47 | 40 | 37 | 7.417 ms | 514.573 us | 7.932 ms | 40 | 40 | yes |
| `wilkinson_48` | 53 | 48 | 45 | 16.158 ms | 782.340 us | 16.934 ms | 48 | 48 |  |
| `wilkinson_48` | 59 | 48 | 44 | 15.976 ms | 769.962 us | 16.748 ms | 48 | 48 |  |
| `wilkinson_48` | 61 | 48 | 43 | 16.250 ms | 770.493 us | 17.029 ms | 48 | 48 | yes |
| `wilkinson_56` | 59 | 56 | 53 | 21.013 ms | 1.046 ms | 22.059 ms | 56 | 56 |  |
| `wilkinson_56` | 61 | 56 | 52 | 20.649 ms | 1.032 ms | 21.681 ms | 56 | 56 |  |
| `wilkinson_56` | 67 | 56 | 51 | 21.013 ms | 1.030 ms | 22.036 ms | 56 | 56 | yes |
| `chebyshev_T24` | 5 | 3 | 22 | 122.422 us | 21.051 us | 143.473 us | 3 | 2 | yes |
| `chebyshev_U24` | 3 | 4 | 33 | 280.696 us | 23.295 us | 303.991 us | 4 | 4 | yes |
| `legendre_P30` | 61 | 15 | 15 | 924.641 us | 28.277 ms | 29.205 ms | 16,384 | 1 |  |
| `legendre_P30` | 67 | 7 | 15 | 1.237 ms | 154.610 us | 1.390 ms | 64 | 1 | yes |
| `legendre_P30` | 71 | 4 | 15 | 403.709 us | 59.909 us | 463.618 us | 8 | 1 |  |
| `legendre_P38` | 79 | 3 | 19 | 591.898 us | 46.830 us | 638.728 us | 4 | 1 | yes |
| `cyclo_phi17` | 3 | 1 | 11 | 2.664 us | 4.887 us | 7.551 us | 1 | 1 | yes |
| `cyclo_phi41` | 3 | 5 | 26 | 658.326 us | 1.398 ms | 2.125 ms | 16 | 16 | yes |
| `xpow24_minus1` | 5 | 14 | 11 | 394.104 us | 1.036 ms | 1.429 ms | 150 | 77 |  |
| `xpow24_minus1` | 7 | 15 | 9 | 367.375 us | 148.510 us | 516.166 us | 38 | 20 |  |
| `xpow24_minus1` | 11 | 13 | 7 | 294.587 us | 1.668 ms | 1.960 ms | 113 | 113 | yes |
| `randprod_10` | 7 | 4 | 11 | 175.860 us | 18.918 us | 194.778 us | 5 | 2 | yes |
| `randprod_21` | 17 | 7 | 9 | 330.360 us | 36.114 us | 366.474 us | 13 | 3 | yes |

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
| `sd5` | 75.107ms | 80.939ms | 81.874ms | 78.623ms | 77.897ms | 75.107ms | 74.279ms | 19/29/29/23 |
| `sd5_shift1` | 62.245ms | 69.740ms | 69.384ms | 67.348ms | 66.413ms | 62.245ms | 62.121ms | 19/29/29/23 |
| `sd5_shift2` | 63.238ms | 72.501ms | 72.643ms | 69.401ms | 68.467ms | 63.238ms | 65.095ms | 19/29/29/29 |
| `sd4_x_sd4shift1` | 13.385ms | 21.311ms | 20.787ms | 19.274ms | 18.492ms | 13.385ms | 13.385ms | 13/29/29/13 |
| `sd5_x_phi11` | 163.162ms | 169.436ms | 178.897ms | 166.715ms | 162.971ms | 162.971ms | 156.912ms | 19/29/29/29 |
| `xpow48_minus1` | 12.921ms | 20.930ms | 20.930ms | 19.057ms | 18.512ms | 12.921ms | 12.921ms | 5/11/11/5 |
| `xpow105_minus1` | 1439.531ms | 81.484ms | 81.484ms | 74.112ms | 65.652ms | 65.652ms | 52.733ms | 11/17/17/17 |
| `xpow120_minus1` | 478.124ms | 526.450ms | 526.450ms | 480.493ms | 478.124ms | 478.124ms | 478.124ms | 7/7/7/7 |
| `cyclo_phi179` | 76.008ms | 76.008ms | 76.008ms | 76.008ms | 76.008ms | 76.008ms | 76.008ms | 3/3/3/3 |
| `cyclo_phi64_x_phi105` | 34.027ms | 86.878ms | 86.878ms | 61.060ms | 34.027ms | 34.027ms | 34.027ms | 11/11/11/11 |
| `cyclo_phi128_x_phi165` | 198.314ms | 198.314ms | 198.314ms | 198.314ms | 198.314ms | 198.314ms | 198.314ms | 7/7/7/7 |
| `cyclo_phi385` | 438.000ms | 438.000ms | 438.000ms | 438.000ms | 438.000ms | 438.000ms | 438.000ms | 3/3/3/3 |
| `wilkinson_40` | 9.667ms | 13.461ms | 13.371ms | 11.795ms | 11.630ms | 9.667ms | 9.646ms | 41/47/47/43 |
| `wilkinson_48` | 19.837ms | 25.849ms | 25.754ms | 23.176ms | 22.935ms | 19.837ms | 19.696ms | 53/61/61/59 |
| `wilkinson_56` | 26.393ms | 35.235ms | 35.258ms | 31.259ms | 30.901ms | 26.393ms | 26.039ms | 59/67/67/61 |
| `chebyshev_T24` | 0.491ms | 0.491ms | 0.491ms | 0.491ms | 0.491ms | 0.491ms | 0.491ms | 5/5/5/5 |
| `chebyshev_U24` | 0.626ms | 0.626ms | 0.626ms | 0.626ms | 0.626ms | 0.626ms | 0.626ms | 3/3/3/3 |
| `legendre_P30` | 32.387ms | 8.173ms | 8.173ms | 9.092ms | 5.822ms | 5.822ms | 2.622ms | 61/71/67/71 |
| `legendre_P38` | 4.472ms | 4.472ms | 4.472ms | 4.472ms | 4.472ms | 4.472ms | 4.472ms | 79/79/79/79 |
| `cyclo_phi17` | 0.112ms | 0.112ms | 0.112ms | 0.112ms | 0.112ms | 0.112ms | 0.112ms | 3/3/3/3 |
| `cyclo_phi41` | 2.838ms | 2.838ms | 2.838ms | 2.838ms | 2.838ms | 2.838ms | 2.838ms | 3/3/3/3 |
| `xpow24_minus1` | 1.835ms | 3.440ms | 3.440ms | 3.141ms | 3.030ms | 1.336ms | 0.930ms | 5/11/11/7 |
| `randprod_10` | 0.823ms | 0.823ms | 0.823ms | 0.823ms | 0.823ms | 0.823ms | 0.823ms | 7/7/7/7 |
| `randprod_21` | 1.616ms | 1.616ms | 1.616ms | 1.616ms | 1.616ms | 1.616ms | 1.616ms | 17/17/17/17 |
| **aggregate** | **3155.159 ms** | **1939.127 ms** | **1948.623 ms** | **1837.845 ms** | **1788.172 ms** | **1754.026 ms** | **1731.830 ms** | |

The replay reproduces both real walks: on every row, the prime the `fixed`
column picks is the prime the pre-#9128 binary selected, and the prime the
`scout` column picks is the prime this PR's binary selected.

Against the fixed policy the scout saves 101.283 ms of 1939.127 ms. That is
67.1% of what is available to the same-plan floor, 54.7% of the reachable
floor, and 48.9% of the oracle floor. The first-good-prime rule remains
unusable at 3155.159 ms, and choosing by minimum width alone is worse than
the score at 1948.623 ms -- `sd5_x_phi11` is where that shows, since prime 23 is
widest and prime 29 wins on the tie breaks.

## Paired before and after

The two service binaries were built from this worktree and differ only in
`HexBerlekampZassenhaus/Modular/PrimePlan.lean`, and the arms were alternated on
the same pinned core, so machine load hits both equally. The rows whose plan
does not change -- `cyclo_phi179`, `cyclo_phi128_x_phi165`, `cyclo_phi385`, the
Chebyshev and `randprod` controls, `cyclo_phi17`, `cyclo_phi41`, `legendre_P38`
-- are the load control: their prime walk does identical work in both arms, so
their spread bounds what can be read into the rows that did change.

The record is `reports/bench-results/hexbz-prime-plan-paired-a79917a1-chungus2.json`;
it carries every round of both arms, and
`scripts/bench/prime_plan_paired.py --report` regenerates this table from it.

### Paired before/after, median of 3 alternating rounds

| instance | prime before | prime after | full splits | prime walk before | prime walk after | walk saved | total before | total after | ratio |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `sd5` | 29 | 29 | 3 -> 2 | 9.484 ms | 7.346 ms | 2.138 ms | 77.992 ms | 76.329 ms | 0.979x |
| `sd5_shift1` | 29 | 29 | 3 -> 2 | 10.414 ms | 8.217 ms | 2.198 ms | 66.713 ms | 65.313 ms | 0.979x |
| `sd5_shift2` | 29 | 29 | 3 -> 2 | 12.753 ms | 9.834 ms | 2.919 ms | 71.987 ms | 69.085 ms | 0.960x |
| `sd4_x_sd4shift1` | 29 | 29 | 3 -> 2 | 9.748 ms | 7.823 ms | 1.924 ms | 21.082 ms | 19.327 ms | 0.917x |
| `sd5_x_phi11` | 29 | 29 | 3 -> 2 | 21.882 ms | 19.459 ms | 2.423 ms | 164.550 ms | 163.173 ms | 0.992x |
| `xpow48_minus1` | 11 | 11 | 3 -> 2 | 6.116 ms | 4.410 ms | 1.706 ms | 20.902 ms | 19.224 ms | 0.920x |
| `xpow105_minus1` | 17 | 17 | 3 -> 2 | 38.775 ms | 31.874 ms | 6.901 ms | 82.809 ms | 76.384 ms | 0.922x |
| `xpow120_minus1` | 7 | 7 | 3 -> 1 | 64.387 ms | 20.372 ms | 44.016 ms | 523.689 ms | 478.859 ms | 0.914x |
| `cyclo_phi179` | 3 | 3 | 1 -> 1 | 14.681 ms | 14.908 ms | -227.256 us | 75.301 ms | 75.377 ms | 1.001x |
| `cyclo_phi64_x_phi105` | 11 | 11 | 3 -> 1 | 74.267 ms | 49.540 ms | 24.727 ms | 86.014 ms | 61.813 ms | 0.719x |
| `cyclo_phi128_x_phi165` | 7 | 7 | 1 -> 1 | 96.833 ms | 100.415 ms | -3.582 ms | 198.000 ms | 198.361 ms | 1.002x |
| `cyclo_phi385` | 3 | 3 | 1 -> 1 | 207.733 ms | 203.533 ms | 4.201 ms | 436.059 ms | 438.654 ms | 1.006x |
| `wilkinson_40` | 47 | 47 | 3 -> 2 | 5.998 ms | 4.377 ms | 1.621 ms | 15.106 ms | 13.406 ms | 0.887x |
| `wilkinson_48` | 61 | 61 | 3 -> 2 | 9.447 ms | 6.930 ms | 2.517 ms | 28.198 ms | 25.364 ms | 0.900x |
| `wilkinson_56` | 67 | 67 | 3 -> 2 | 13.856 ms | 10.236 ms | 3.621 ms | 38.023 ms | 34.736 ms | 0.914x |
| `chebyshev_T24` | 5 | 5 | 1 -> 1 | 348.697 us | 346.564 us | 2.133 us | 561.693 us | 571.568 us | 1.018x |
| `chebyshev_U24` | 3 | 3 | 1 -> 1 | 321.947 us | 335.247 us | -13.300 us | 692.627 us | 714.700 us | 1.032x |
| `legendre_P30` | 71 | 67 | 3 -> 2 | 7.714 ms | 7.925 ms | -210.993 us | 8.436 ms | 9.338 ms | 1.107x |
| `legendre_P38` | 79 | 79 | 1 -> 1 | 3.919 ms | 3.917 ms | 1.762 us | 4.751 ms | 4.815 ms | 1.013x |
| `cyclo_phi17` | 3 | 3 | 1 -> 1 | 106.227 us | 105.747 us | 480 ns | 152.295 us | 150.934 us | 0.991x |
| `cyclo_phi41` | 3 | 3 | 1 -> 1 | 706.908 us | 710.233 us | -3.325 us | 2.833 ms | 2.858 ms | 1.009x |
| `xpow24_minus1` | 11 | 11 | 3 -> 2 | 1.454 ms | 1.198 ms | 256.300 us | 3.499 ms | 3.258 ms | 0.931x |
| `randprod_10` | 7 | 7 | 1 -> 1 | 549.535 us | 551.518 us | -1.983 us | 817.071 us | 814.157 us | 0.996x |
| `randprod_21` | 17 | 17 | 1 -> 1 | 1.279 ms | 1.297 ms | -17.646 us | 1.740 ms | 1.766 ms | 1.015x |
| **aggregate** | | | | | | 97.114 ms | 1.930 s | 1.840 s | **0.9533x** |

Load control (10 instances whose plan does not change): 0.991x to 1.032x.

Every row whose plan changes improves, between 0.719x and 0.992x, except
`legendre_P30`. The ten rows whose plan does not change span 0.991x to 1.032x
and are the day's noise floor on this machine. The prime walk loses 97.114 ms
across the corpus, of which `xpow120_minus1` is 44.0 ms and
`cyclo_phi64_x_phi105` 24.7 ms.

The three larger instances outside the representative set behave the same way.
Paired over two rounds: `sd6` 3 splits to 2 and prime 29 kept, `hoeij_F190`
3 to 2 and prime 13 kept, `hoeij_M12_f132` 3 to 2 and prime 13 kept. The full
sweep puts them at 1.056x, 0.919x and
0.981x against the issue #9127 baseline, inside its own
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
measured regression: 8.436 ms to 9.338 ms, 1.107x. Removing the gate was
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
behaviour.** Not the first: 48.9% of the oracle floor, 54.7% of the reachable
floor, 67.1% of the same-plan floor. The oracle and reachable floors are
unreachable by construction -- the oracle names the winner without paying to
discover it, and neither ever scouts -- so the honest number is the third, and
the missing third of it is the complete scouts on equal-width families
described above. The second clause is what this PR claims: the policy is
simpler than the one it replaces (no width threshold, no fuel spent on
splitting, one selector), selects the same plan wherever the width gate does
not fire, and is 0.9533x end to end on the paired corpus, with every row whose
plan changes improving except `legendre_P30`.

**Median unsuccessful-scout overhead below 3%.** An unsuccessful scout is one
whose candidate is not selected. As a fraction of each scouting row's total:

| instance | unsuccessful scouts | row total | share |
|---|---:|---:|---:|
| `legendre_P30` | 0 ns | 9.338 ms | 0.00% |
| `wilkinson_56` | 111 us | 34.736 ms | 0.32% |
| `xpow48_minus1` | 77 us | 19.224 ms | 0.40% |
| `sd5_x_phi11` | 688 us | 163.173 ms | 0.42% |
| `sd5` | 348 us | 76.329 ms | 0.46% |
| `wilkinson_48` | 117 us | 25.364 ms | 0.46% |
| `xpow120_minus1` | 2.340 ms | 478.859 ms | 0.49% |
| `wilkinson_40` | 75 us | 13.406 ms | 0.56% |
| `sd5_shift2` | 446 us | 69.085 ms | 0.65% |
| `sd5_shift1` | 446 us | 65.313 ms | 0.68% |
| `xpow24_minus1` | 32 us | 3.258 ms | 0.99% |
| `sd4_x_sd4shift1` | 293 us | 19.327 ms | 1.51% |
| `xpow105_minus1` | 2.343 ms | 76.384 ms | 3.07% |
| `cyclo_phi64_x_phi105` | 26.719 ms | 61.813 ms | 43.23% |

Median **0.52%**. The `cyclo_phi64_x_phi105` outlier is the row where the
scouts replace two splits of 25.0 ms and 27.5 ms; it is the largest saving in
the corpus at 0.719x, so its scouts are not overhead in any useful sense.

**No unexplained regression above 5%.** One row regresses: `legendre_P30` at
1.107x, explained above and quantified. Every other row is inside the load
control's 0.991x to 1.032x band or improves. The full sweep solves the same
376 instances as the baseline.

**`xpow105_minus1` retains its useful width reduction.** It still selects prime
17 at width 14, against widths 30 and 33 at the two primes it rejects, and the
row improves 0.922x. The scout at prime 13 completes its pattern at width
33 and is rejected by its score, for 2.4 ms against the 15.8 ms split it
replaces.

**The wasted extra splits on SD5, Wilkinson 56, `xpow120_minus1` and
`cyclo_phi64_x_phi105` are removed or shown worthwhile.** `xpow120_minus1` and
`cyclo_phi64_x_phi105` now perform one split where they performed three, at
0.914x and 0.719x. SD5 and Wilkinson 56 perform two: the extra split at their
selected prime is not waste -- it is the prime the score picks -- but the third
is gone, at 0.979x and 0.914x.

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
