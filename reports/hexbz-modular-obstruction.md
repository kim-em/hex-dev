# HexBZ recombination: rejecting impossible divisors over a word-sized prime

Classical recombination accepted a candidate only by dividing the integer
target by it exactly.  Almost every candidate fails, and on the `x^n - 1` rows
that failure was being established by dense multi-limb long division.  This
page records what a finite-field necessary condition costs, what it removes,
and where it does not help.  It continues
[reports/hexbz-support-traversal.md](hexbz-support-traversal.md), which is
#9129's record and this change's starting point.

## The obstruction

Reduction modulo a prime `q` is a ring homomorphism `ℤ[X] → 𝔽_q[X]`.  If
`candidate ∣ target` over `ℤ` then the reduced candidate divides the reduced
target, and division in `𝔽_q[X]` leaves no remainder.  Contrapositively a
nonzero `𝔽_q[X]` remainder proves the candidate does not divide, in machine-word
arithmetic.

`Hex.obstructs` is that test and `Hex.obstructs_eq_false_of_dvd` is the
statement that it never rejects a genuine divisor.  Both traversals reach exact
division only through `Hex.obstructedQuotient?`, whose equation
`obstructedQuotient?_eq` says guarding exact division by the obstruction does
not change its value; `Hex.directCandidateAfterObstruction_eq` lifts that to the
head-forced leaf, so `Hex.directLeaf_eq` and the classical completeness proofs
above it are unchanged.

The obstruction is one-sided.  It can reject; it cannot accept.  Exact integer
division remains the only accepting test and the only exact-quotient
implementation.

`q = 67108859 = 2^26 - 5`, fixed at compile time, with its primality proved by
kernel-checked trial division (`Hex.obstructionPrime_prime`, about one second of
build time).  Any prime below `2^31` satisfies `ZMod64.Bounds`; the size only
governs how often a non-divisor slips through, and a candidate that slips
through costs exactly the exact division that would have run anyway.

### There is no inconclusive branch

The issue anticipated an "inconclusive" result when reduction makes the divisor
zero or drops its leading coefficient.  Neither needs a branch.
`DensePoly.DivModLaws.mod_eq_zero_of_dvd` is stated for every divisor including
zero, so the no-false-rejection theorem covers those cases with no side
condition, and the executable `divMod` returns `(0, p)` on a zero divisor
without entering its loop.  A reduced candidate that is a nonzero constant
divides everything and simply never fires.  The inconclusive count is
structurally zero, not merely empirically zero.

### Why the filter runs after the candidate is built, not before

The issue asked for the modular product to be assembled from cached reductions
of the lifted factors, rejecting a support before the integer candidate is
materialized.  That is not available, and the reason is worth recording.

The candidate is

```text
normalizeFactorSign (primitivePart (centeredLift (coreLc * ∏ g_i) mod p^k)).
```

Centred lifting sends a coefficient `c` to `c - p^k * round (c / p^k)`.  Its
value modulo `q` therefore depends on `round (c / p^k)`, that is on the full
integer `c`, not on `c mod q`; and the primitive part divides through by a
content that is likewise a function of the integer coefficients.  So the
candidate's image in `𝔽_q[X]` is *not* a function of the lifted factors'
images in `𝔽_q[X]`, and no cached per-factor reduction can produce it.

What survives of the issue's intent is the ordering: the metadata-only degree
and trailing-coefficient filters still run first and still reject before
anything is built, and the obstruction sits between candidate construction
(`Hex.directCandidate`, a `p^k`-modular product) and exact division.  On
`xpow120_minus1` construction is 14.7% of the old total and exact division is
71.2%; the filter removes the second, not the first.

## Revision and protocol

- Source revision `4b75d9d6` (clean worktree), Lean toolchain
  `leanprover/lean4:v4.33.0-rc1`.
- Baseline `9d3590500d551dfebf6c9bb5940f2f961753f53e`, this branch's merge base,
  built and swept on the same host in the same session.  The committed
  `f8477abd` record is *not* usable as the baseline: `main` moved between it and
  this branch point, and rows this change cannot touch (`cyclo_phi121` 1.99x,
  `legendre_P20` 1.95x against it) move more than rows it can.
- Host `chungus2`, AMD EPYC 9455, Linux x86-64, 96 cores, measured service
  pinned to CPU 70.
- Corpus `bench/corpus/hexbz-factor-corpus.jsonl`, 392 rows, SHA-256
  `619913904240834c912489e6cc23ba136e8cc5ebf0ea95f83397e0682387284d`.
- Sweep: persistent warm service, ten-second per-call cutoff, median of five
  calls below one second and one call otherwise, early termination disabled.

### Repeats, interleaving, and the noise floor

Other agents were building and measuring on this host throughout, so a single
sweep pair cannot resolve small differences.  **Six complete sweeps per
revision**, both sides spread over the same two-hour window, and the middle of
that window run as an interleave -- rebuild, sweep the baseline, rebuild, sweep
this revision -- so a drift in host load cannot land preferentially on one
side.  (Baseline repeats are at 04:35, 04:39, 05:48, 05:55, 06:15, 06:22;
this revision's at 06:11, 06:18, 06:25, 06:35, 06:38, 06:41.)  Every number
below is a median over the six repeats on each side.

The floor those medians sit on is measured the same way.  Splitting each side's
six repeats into its own first three against its own last three -- identical
binaries, same protocol, spread over the same window -- gives whole-corpus
medians of **0.994** for the baseline and **0.999** for this revision.  So a
whole-corpus median within about 0.6% of 1.0 is not resolved by this
measurement, and differences of a few percent on individual small rows are not
either.  The three-order-of-magnitude results below are far outside it; the
near-1.0 results are reported as bounded, not as point estimates.

### Artifacts

All under `reports/bench-results/`.  Every repeat is committed, so the medians
are reproducible rather than asserted.  The plotting and freshness tools select
the newest record, which is `…-4b75d9d6-…-run6.json`.

| Record | SHA-256 |
|---|---|
| `hexbz-factor-sweep-4b75d9d6-hex-chungus2-run6.json` (published curve) | `3aedb5f4b6c980025fd0e23cff6e32b8a99c8ca7390a34e9d410c3180bd11623` |
| `hexbz-factor-sweep-4b75d9d6-hex-chungus2-run{1..5}.json` | the other five repeats at this revision |
| `hexbz-factor-sweep-9d359050-hex-chungus2-run1.json` | `19d9392493a08e2d9a4a25cc101fb4ea6f4d577ab10a1f11cab39ccf752002df` |
| `hexbz-factor-sweep-9d359050-hex-chungus2-run{2..6}.json` | the other five repeats at the merge base |
| `hexbz-phase-profile-4b75d9d6-chungus2.json` | `327e56edc2764637b282a312cf6946a2c039789bb83198f4cb71b836dda81f39` |
| `hexbz-phase-profile-9d359050-chungus2.json` | `cadf62d3f4c099f19a8880ae9e5b89d498295e99486701ba12b65c7bc9e5dc29` |
| `hexbz-factor-sampling-profiles-4b75d9d6-chungus2.json` | `e75daab7d1cd7b29f967be46aea1042c0a7839563dc209d9b2fdb6e31a458b9f` |
| `hexbz-factor-sampling-profiles-9d359050-chungus2.json` | `4758e485ed025ed4a4bbf9386cb884154e0d9a346abb30e267153ef3d5255105` |
| `hexbz-obstruction-probe-4b75d9d6-chungus2.json` | `ecbe216a375010f64868808e713af95630b290a8df4d991c25f99d23f4880b2c` |

The comparator record `hexbz-factor-sweep-aa68c920-chungus2.json` (FLINT, NTL,
PARI, both Isabelle extractions) is reused unchanged.

## What the filter rejects

`scripts/bench/obstruction_probe.py` drives
`hexbz_factor_service --entry obstructionProbe`, which runs the counted
recombination mirror four times on one input -- filtered (the production leaf),
unfiltered, filtered, unfiltered -- and reports every stage-counter set and
every span.  The mirror was built and measured before production consumed the
filter; it is now the before/after instrument, and its output is a committed
record.

The order is counterbalanced because a fixed one would confound the filter with
allocator warmth: each variant is timed both early and late, and the columns
below show the two timings of each.  Each repeat is given its own runtime-zero
budget offset, because otherwise the compiler shares one evaluation across the
syntactically identical calls and the repeats return in a few hundred
nanoseconds; `sameRepeatCounters` in the record is the check that the repeats
really are the same search.

| instance | reached filter | rejected | fell through | filtered (early, late) | unfiltered (early, late) | ratio |
|---|---:|---:|---:|---:|---:|---:|
| `cyclo_phi385` | 8 | 7 | 1 | 10.22, 10.24 ms | 81.9, 81.5 ms | **0.125x** |
| `cyclo_phi128_x_phi165` | 25 | 23 | 2 | 5.93, 5.91 ms | 41.4, 41.6 ms | **0.143x** |
| `cyclo_phi275` | 512 | 511 | 1 | 594, 595 ms | 3.568, 3.566 s | **0.166x** |
| `xpow105_minus1` | 60 | 52 | 8 | 4.86, 4.85 ms | 28.6, 28.4 ms | **0.171x** |
| `cyclo_phi179` | 2 | 1 | 1 | 1.19, 1.17 ms | 5.57, 5.55 ms | **0.212x** |
| `xpow120_minus1` | 1,801 | 1,785 | 16 | 114.7, 115.5 ms | 446, 444 ms | **0.259x** |
| `xpow48_minus1` | 268 | 258 | 10 | 5.36, 5.34 ms | 15.11, 15.12 ms | **0.353x** |
| `xpow60_minus1` | 31 | 19 | 12 | 484, 470 us | 1.14, 1.10 ms | 0.428x |
| `cyclo_phi105_x_phi128` | 28 | 26 | 2 | 2.50, 2.47 ms | 5.18, 5.09 ms | 0.485x |
| `cyclo_phi64_x_phi105` | 28 | 26 | 2 | 2.39, 2.36 ms | 4.81, 4.75 ms | 0.496x |
| `xpow24_minus1` | 113 | 105 | 8 | 896, 868 us | 1.71, 1.68 ms | 0.517x |
| `cyclo_phi41` | 16 | 15 | 1 | 823, 811 us | 1.49, 1.42 ms | 0.570x |
| `hoeij_M12_f132` | 462 | 461 | 1 | 710, 710 ms | 1.213, 1.216 s | 0.585x |
| `sd5_x_phi45` | 515 | 513 | 2 | 293, 291 ms | 368, 367 ms | 0.793x |
| `sd4` | 9 | 8 | 1 | 254, 230 us | 293, 278 us | 0.825x |
| `sd5_x_phi11` | 258 | 256 | 2 | 130, 129 ms | 148, 147 ms | 0.877x |
| `sd5` | 129 | 128 | 1 | 64.9, 64.8 ms | 69.7, 69.7 ms | 0.930x |
| `sd4_x_sd4shift1` | 10 | 8 | 2 | 9.70, 9.65 ms | 9.98, 9.95 ms | 0.971x |
| `sd5_shift2` | 1 | 0 | 1 | 60.1, 60.3 ms | 60.3, 60.5 ms | 0.997x |
| `sd5_shift1` | 1 | 0 | 1 | 59.0, 59.2 ms | 58.8, 59.2 ms | 1.003x |
| `legendre_P30` (control) | 1 | 0 | 1 | 188, 164 us | 172, 161 us | 1.024x |
| `legendre_P38` (control) | 1 | 0 | 1 | 63.5, 53.0 us | 50.3, 48.9 us | 1.085x |
| `xpow36_minus1` | 11 | 2 | 9 | 87.9, 74.9 us | 71.5, 66.2 us | 1.132x |
| `chebyshev_T24` (control) | 2 | 0 | 2 | 36.5, 24.9 us | 21.8, 20.3 us | 1.227x |
| `randprod_10` (control) | 2 | 0 | 2 | 32.2, 24.0 us | 19.8, 18.9 us | 1.270x |
| `randprod_21` (control) | 3 | 0 | 3 | 53.8, 43.3 us | 34.9, 33.9 us | 1.277x |
| `cyclo_phi17` (control) | 1 | 0 | 1 | 11.9, 5.8 us | 5.1, 4.5 us | 1.306x |
| `chebyshev_U24` (control) | 4 | 0 | 4 | 41.6, 39.2 us | 25.0, 24.6 us | 1.595x |

Over the 32 probed instances, **4,302 candidates reached the filter, 4,204 were
rejected, and 98 fell through -- and all 98 were genuine divisors.**  Every
non-divisor that reached the filter was rejected, and no divisor was.  Ratios
are the better of each variant's two timings, so the ordering does not decide
them; on the large rows the two timings of a variant agree to well under a
percent.

On rows that answer through proposal replay or the lattice tier
(`wilkinson_40/48/56`, `sd6`) the head-forced traversal is not entered at all,
so they have no row here; the sweep still covers them.

The record also checks that the filtered and unfiltered executions return the
same factor *polynomials* (not merely the same degrees), the same decline, the
same divisor count, completed cardinalities, leaves and recordable count.  They
agree on every row.

The last group is the cost side, isolated: on inputs where every candidate that
reaches the filter is a real divisor, the obstruction is pure overhead and
recombination costs up to 1.6x.  It is a small phase on those rows -- see below.

## Measured effect

### Total factor time (sweep)

Median of six baseline sweeps against median of six at this revision.

| instance | baseline | now | |
|---|---:|---:|---:|
| `cyclo_phi1031` | timeout (>10 s) | 6.566 s | **now solves** |
| `cyclo_phi275` | 3.924 s | 940.992 ms | **0.240x** |
| `xpow120_minus1` | 477.889 ms | 153.554 ms | **0.321x** |
| `xpow48_minus1` | 19.563 ms | 11.014 ms | **0.563x** |
| `hoeij_F190` | 6.638 s | 3.852 s | **0.580x** |
| `cyclo_phi61` | 10.728 ms | 7.009 ms | **0.653x** |
| `xpow105_minus1` | 74.742 ms | 51.808 ms | **0.693x** |
| `hoeij_M12_f132` | 1.630 s | 1.155 s | **0.708x** |
| `xpow24_minus1` | 3.300 ms | 2.426 ms | **0.735x** |
| `cyclo_phi41` | 2.923 ms | 2.220 ms | **0.759x** |
| `sd5_x_phi45` | 416.933 ms | 330.012 ms | **0.792x** |
| `cyclo_phi105` | 9.005 ms | 7.188 ms | **0.798x** |
| `cyclo_phi128_x_phi165` | 198.110 ms | 163.068 ms | **0.823x** |
| `cyclo_phi385` | 434.391 ms | 362.367 ms | **0.834x** |
| `sd5_x_phi11` | 164.480 ms | 143.128 ms | **0.870x** |
| `sd4_x_phi35` | 23.034 ms | 20.638 ms | 0.896x |
| `sd5` | 75.999 ms | 71.119 ms | 0.936x |
| `cyclo_phi179` | 74.572 ms | 70.461 ms | 0.945x |
| `cyclo_phi64_x_phi105` | 61.497 ms | 58.229 ms | 0.947x |
| `sd4_x_sd4shift1` | 19.739 ms | 19.112 ms | 0.968x |
| `sd5_shift2` | 68.753 ms | 68.356 ms | 0.994x |
| `sd5_shift1` | 66.247 ms | 65.903 ms | 0.995x |
| `sd6` | 8.371 s | 8.400 s | 1.003x |
| `legendre_P30` (control) | 9.304 ms | 9.362 ms | 1.006x |
| `randprod_21` (control) | 1.762 ms | 1.777 ms | 1.008x |
| `xpow36_minus1` | 2.933 ms | 2.957 ms | 1.008x |
| `chebyshev_T24` (control) | 560.677 us | 568.854 us | 1.015x |
| `wilkinson_56` | 34.383 ms | 35.896 ms | 1.044x |
| `wilkinson_48` | 25.224 ms | 26.364 ms | 1.045x |
| `wilkinson_16` | 1.152 ms | 1.221 ms | 1.061x |
| `wilkinson_24` | 3.510 ms | 3.730 ms | 1.062x |

Aggregate `xpow48 + xpow105 + xpow120`: 572.194 ms to 216.376 ms, **0.378x**.
Summed over the 376 rows both revisions solve: 23.764 s to 16.949 s, **0.713x**.

Distribution over the whole corpus, against the 0.994 to 0.999 noise floor:

| set | n | median | p10 | p90 |
|---|---:|---:|---:|---:|
| all rows | 376 | 1.0092 | 0.9782 | 1.0328 |
| rows above 1 ms | 101 | 1.0024 | 0.7982 | 1.0134 |
| Swinnerton-Dyer families | 22 | 0.9939 | 0.8960 | 1.0235 |
| rows where nearly every candidate divides | 10 | 1.0082 | 0.9948 | 1.0275 |

By family:

| family | n | median | | family | n | median |
|---|---:|---:|---|---|---:|---:|
| hoeij-zimmermann | 2 | **0.644** | | conway | 186 | 1.007 |
| sd-products | 10 | **0.942** | | legendre | 20 | 1.010 |
| cyclotomic-products | 19 | **0.977** | | laguerre | 20 | 1.014 |
| swinnerton-dyer | 12 | 1.001 | | random-products | 30 | 1.016 |
| cyclotomic | 33 | 1.003 | | chebyshev | 28 | 1.030 |
| | | | | wilkinson | 15 | 1.053 |

### The regressions, and which are explained

`wilkinson` is a real, reproducible **+5%** family, not noise: it appears in
every repeat, and ten of its rows exceed 1.05.  The mechanism is exact.
Wilkinson inputs answer through the proposal tier, whose unforced sweep peels
one linear factor `(x - k)` at a time, and `factorTrace` reports
`unforcedRecordable = unforcedExactDivisions` on every one of them:
`wilkinson_24` puts 24 candidates to the filter and the filter rejects **zero**,
because all 24 are genuine divisors.  So the filter cannot help there and its
whole cost shows.  The cost per peel is dominated by reducing the target, which
`Hex.supportMeta` does once per subset-cardinality level and the peel loop
re-enters after every split; hoisting the per-target metadata out of that level
loop would remove most of it, and is the natural follow-up.

The other rows above 1.05 -- `chebyshev_T4` (37 us), `conway_p7_n3` (44 us),
`chebyshev_U8` (142 us) -- are at or below the repeat spread of the same rows
between identical builds.

`chebyshev` at 1.030 and `random-products` at 1.016 are the same effect as
wilkinson at smaller scale: these are products of small distinct factors, where
most candidates reaching the filter divide.

### Where the time went (sampling profiles)

Shares of each run's own total, so the two columns are not the same absolute
time; the whole-run factor from the sweep is given with each block.

| `xpow120_minus1` (0.321x overall) | before | after |
|---|---:|---:|
| `Hex.directLeaf` | 86.67% | 72.00% |
| ... `Hex.directCandidate` (the `p^k` product) | 14.74% | 42.69% |
| ... `Hex.obstructs` | -- | 25.94% |
| ... ... `Hex.FpPoly.modCached` | -- | 24.18% |
| ... `Hex.exactQuotient?` | 71.19% | below threshold |
| `Hex.DensePoly.divModArray` (integer long division) | 73.94% | 9.36% |
| allocator time, all allocators | 70.94% | 48.10% |

| `xpow48_minus1` (0.563x overall) | before | after |
|---|---:|---:|
| `Hex.directLeaf` | 71.58% | 47.93% |
| ... `Hex.directCandidate` | 12.69% | 24.25% |
| ... `Hex.obstructs` | -- | 20.79% |
| ... `Hex.exactQuotient?` | 57.65% | below threshold |
| `Hex.DensePoly.divModArray` | 67.33% | 19.96% |
| allocator time, all allocators | 61.75% | 35.10% |

Rescaling `xpow120_minus1` by its 0.321x whole-run factor: candidate
construction is 14.7% of the old total before and 13.7% after (unchanged, as it
must be), the obstruction costs 8.3% of the old total, and it removes 71.2%.
That ratio -- pay 8, save 71 -- is the whole result on this family.

`Hex.exactQuotient?` no longer appears above the profiler's reporting threshold
on any profiled row.

### Exact divisions removed (phase profile, deterministic)

| instance | exact divisions before | after | recombination phase |
|---|---:|---:|---:|
| `xpow120_minus1` | 1,801 | 16 | 0.255x |
| `xpow105_minus1` | 60 | 8 | 0.170x |
| `xpow48_minus1` | 268 | 10 | 0.385x |
| `cyclo_phi385` | 8 | 1 | 0.122x |
| `cyclo_phi128_x_phi165` | 25 | 2 | 0.139x |
| `cyclo_phi179` | 2 | 1 | 0.208x |
| `xpow24_minus1` | 113 | 8 | 0.505x |
| `sd5_x_phi11` | 258 | 2 | 0.873x |
| `sd5` | 129 | 1 | 0.922x |
| `chebyshev_T24` (control) | 2 | 2 | 1.290x |
| `randprod_21` (control) | 3 | 3 | 1.324x |

The counted mirror agrees with the production `factorTrace` on leaf count,
selected prime, completed cardinalities and returned factor degrees on 368 of
368 rows of the wider validation sample.

### Allocation

The deterministic small-object counter (`IO.getNumHeartbeats`) *rises*
slightly, for the recombination phase:

| instance | before | after | |
|---|---:|---:|---:|
| `xpow48_minus1` | 239,607 | 270,316 | +12.8% |
| `xpow105_minus1` | 248,913 | 266,987 | +7.3% |
| `xpow120_minus1` | 5,047,002 | 5,264,950 | +4.3% |
| `sd5` | 2,741,029 | 2,749,638 | +0.3% |

This is the honest shape of the change and not a contradiction: the counter
sees Lean small objects, and the obstruction allocates one reduced coefficient
array per candidate.  What it does not see is GMP limb allocation, which is
where integer long division lives; the sampling profiler's allocator share
(70.94% to 48.10% on `xpow120_minus1`) is the measurement that does.

Building the obstruction image with `Array.map` (`ZPoly.modPImpl`) instead of
the `List.range` specification was tried and is *worse* on both counters --
`chebyshev_T24` recombination allocations 1,407 to 1,492 -- so the reference
shape is kept, matching the note already on `ZPoly.modP_eq_impl`.

## Two moduli are not justified

The issue allowed a second modulus if measurement supported it.  It does not.
A second modulus can only help on candidates the first one passes, and every
one of the 98 pass-throughs across the probed corpus was a genuine divisor.
There is nothing for a second modulus to reject, and it would add its cost to
exactly the rows that are already the cost side of this change.

## What this does not fix: the Swinnerton-Dyer prefilter arithmetic

#9130's comment identified a second target on `sd5`, larger than the
exact-division target on the `x^n - 1` rows, and it is still there.  `sd5` moves
0.936x, and its profile after this change is:

| | share of `sd5` total, after |
|---|---:|
| `Hex.directCandidatePrefilter` | 28.60% |
| ... `Hex.directTrailingPrefilter` | 17.81% |
| ... ... `Hex.centeredModNat` | 10.27% |
| ... `Hex.directDegreePrefilter` | 10.64% |
| `Hex.directCandidateAfterObstruction` | 7.82% |
| ... `Hex.obstructs` | 1.91% |
| `Hex.exactQuotient?` | below threshold |

`sd5` visits 32,768 leaves and only 129 reach the filter, so on that family the
metadata-only prefilters do the rejecting and the obstruction removes 128 of
129 exact divisions -- worth 6.4%, and no more, because exact division was
never the cost there.

The remaining cost is `Hex.centeredModNat` at 10.3% of total, and the mechanism
is specific: it takes the modulus as a `Nat` and evaluates `Int.ofNat m` on a
93-bit value on every call, allocating a fresh `mpz` per leaf, while
`Hex.SupportMeta` already carries `modulusInt`.  Threading the integer modulus
through `directTrailingPrefilter` would remove that conversion.  This is a
different mechanism from a word-prime divisibility obstruction -- it is about
how the existing multi-limb filter converts its modulus, not about rejecting
candidates -- and it changes `directCandidatePrefilter`'s signature, which the
classical completeness proofs consume.  It belongs in its own issue, not
bundled here.

## Acceptance criteria

| criterion | outcome |
|---|---|
| no false rejection; cannot accept a factor | met; `Hex.obstructs_eq_false_of_dvd` and `Hex.obstructedQuotient?_eq`, with acceptance still only through `exactQuotient?` |
| at least half the exact divisions on the material `xpow` controls avoided | met, far above threshold: 258/268, 52/60, 1,785/1,801 -- 96%, 87%, 99% |
| aggregate `xpow48/105/120` improves materially | met; 0.378x |
| median overhead below 2% on rows with few candidate divisions | met; 0.8% over the ten rows where nearly every candidate divides, 0.2% median over all rows above 1 ms, against a 0.6% noise floor |
| no unexplained regression above 5% | met, with one explained family: `wilkinson` is +5%, and `factorTrace` shows its filter rejects zero of its candidates because all of them divide. The remaining rows above 1.05 are 37 to 142 us and inside their own repeat spread |
| exactly one exact quotient implementation and one production reconstruction path | met; `exactQuotient?` is untouched and both traversals reach it only through `Hex.obstructedQuotient?` |
| full build, conformance, oracle and factorization tests pass | met; all oracles pass, `bz_trace_gate.py` checks 54 traces with 0 failures, and `hexbz_emit_fixtures` output is byte-identical to the committed fixtures |
| fresh full Hex sweep and regenerated figures | recorded above; all 25 SVGs regenerated, external comparator record reused |

## Regeneration

```sh
lake build hexbz_factor_service

# Pin to an idle core; interleave the revisions and repeat, because other work
# shares this host.
taskset -c 70 python3 scripts/bench/factor_sweep.py \
  --systems hex-factor --cutoff 10 --no-early-terminate \
  --output /tmp/hexbz-factor-sweep.json

taskset -c 70 python3 scripts/bench/factor_phase_profile.py \
  --output /tmp/hexbz-phase-profile.json

# No outer `taskset`: the profiler pins the service itself, and wrapping it
# leaves samply with no thread to attribute.
python3 scripts/profile/factor_sampling_profile.py \
  --cpu 70 --output /tmp/hexbz-factor-sampling-profiles.json

# Filter counters and counterbalanced spans, both sides, from one run per row.
taskset -c 70 python3 scripts/bench/obstruction_probe.py \
  --output /tmp/hexbz-obstruction-probe.json

python3 scripts/bench/cactus_rank_table.py --lo 118 --hi 144

uv run --with matplotlib==3.11.1 python3 scripts/plots/hexbz-cactus.py
uv run --with matplotlib==3.11.1 python3 scripts/plots/hexbz-cactus.py --check
```
