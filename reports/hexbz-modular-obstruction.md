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

- Source revision `bf5973a3` (clean worktree), Lean toolchain
  `leanprover/lean4:v4.33.0-rc1`.
- Baseline `a5b827bd`, that is `main` with this branch merged out, built and
  swept on the same host in the same session.  A committed record from an
  earlier `main` is *not* usable as the baseline: `main` moves under this branch
  (#9147's Kronecker substitution for the Hensel product landed mid-review), and
  against a stale record rows this change cannot touch move more than rows it
  can.
- Host `chungus2`, AMD EPYC 9455, Linux x86-64, 96 cores, measured service
  pinned to CPU 70.
- Corpus `bench/corpus/hexbz-factor-corpus.jsonl`, 392 rows, SHA-256
  `619913904240834c912489e6cc23ba136e8cc5ebf0ea95f83397e0682387284d`.
- Sweep: persistent warm service, ten-second per-call cutoff, median of five
  calls below one second and one call otherwise, early termination disabled.

### Repeats, interleaving, and the noise floor

Other agents were building and measuring on this host throughout, so a single
sweep pair cannot resolve small differences.  **Four complete sweeps per
revision**, fully interleaved -- rebuild, sweep this revision, rebuild, sweep
the baseline, four times over -- so a drift in host load cannot land
preferentially on one side.  Every number below is a median over the four
repeats on each side.

The floor those medians sit on is measured the same way.  Splitting each side's
four repeats into its own first two against its own last two -- identical
binaries, same protocol, same window -- gives whole-corpus medians of **0.992**
for the baseline and **1.001** for this revision.  So a whole-corpus median
within about 0.8% of 1.0 is not resolved by this measurement, and differences of
a few percent on individual sub-millisecond rows are not either.  The
three-order-of-magnitude results below are far outside it; the near-1.0 results
are reported as bounded, not as point estimates.

### Artifacts

All under `reports/bench-results/`.  Every repeat is committed, so the medians
are reproducible rather than asserted.  The plotting and freshness tools select
the newest record, which is `…-bf5973a3-…-run5.json`.

| Record | SHA-256 |
|---|---|
| `hexbz-factor-sweep-bf5973a3-hex-chungus2-run4.json` | `cec04a36e4cffbd9ba0259c1b8c499f4716aae30e95ef3f0c597f9b3276e3797` |
| `hexbz-factor-sweep-bf5973a3-hex-chungus2-run{1..3,5}.json` | the other repeats at this revision; `run5` is the published curve, swept last on a clean tree |
| `hexbz-factor-sweep-a5b827bd-hex-chungus2-run1.json` | `24dfc7c175949e9d08db3449132c8a38a0fe9a3a6a5273f481c55d95431ce4e1` |
| `hexbz-factor-sweep-a5b827bd-hex-chungus2-run{2..4}.json` | the other three repeats at the baseline |
| `hexbz-phase-profile-bf5973a3-chungus2.json` | `e9e1cd98d818e3f934375f95af14003945f6a0ee3b67e377346860e92896d81f` |
| `hexbz-phase-profile-a5b827bd-chungus2.json` | `75dd728a06360fb70c3e30550ae74037a09a18c73fd558c8131fa2d025cb385a` |
| `hexbz-factor-sampling-profiles-bf5973a3-chungus2.json` | `773dd0191be5adda8be1b81df764f7c975f50dc5fbbadf6cc214d5c1c0dc09a2` |
| `hexbz-factor-sampling-profiles-a5b827bd-chungus2.json` | `36c1510bd3c6826c60d58aa2cfdaad94c0b74885d9537c6d365e91e39786fd7b` |
| `hexbz-obstruction-probe-bf5973a3-chungus2.json` | `07c820aa2d9c90c5549a76837a573f8cf1ba399e38c70f7bc90df0e23dfb34f4` |

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
| `cyclo_phi385` | 8 | 7 | 1 | 10.27, 10.27 ms | 81.51, 81.56 ms | **0.126x** |
| `cyclo_phi128_x_phi165` | 25 | 23 | 2 | 6.01, 6.00 ms | 41.54, 41.53 ms | **0.144x** |
| `cyclo_phi275` | 512 | 511 | 1 | 585, 592 ms | 3.568, 3.565 s | **0.164x** |
| `xpow105_minus1` | 60 | 52 | 8 | 4.88, 4.85 ms | 28.65, 28.58 ms | **0.170x** |
| `cyclo_phi179` | 2 | 1 | 1 | 1.19, 1.22 ms | 5.61, 5.55 ms | **0.214x** |
| `xpow120_minus1` | 1,801 | 1,785 | 16 | 112.7, 113.1 ms | 443.6, 443.0 ms | **0.255x** |
| `xpow48_minus1` | 268 | 258 | 10 | 5.28, 5.27 ms | 15.02, 15.06 ms | **0.351x** |
| `xpow60_minus1` | 31 | 19 | 12 | 473, 458 us | 1.14, 1.10 ms | 0.418x |
| `cyclo_phi105_x_phi128` | 28 | 26 | 2 | 2.51, 2.46 ms | 5.24, 5.11 ms | 0.481x |
| `cyclo_phi64_x_phi105` | 28 | 26 | 2 | 2.40, 2.35 ms | 4.81, 4.71 ms | 0.500x |
| `xpow24_minus1` | 113 | 105 | 8 | 878, 842 us | 1.69, 1.66 ms | 0.506x |
| `cyclo_phi41` | 16 | 15 | 1 | 804, 795 us | 1.42, 1.39 ms | 0.573x |
| `hoeij_M12_f132` | 462 | 461 | 1 | 708, 708 ms | 1.210, 1.206 s | 0.587x |
| `sd5_x_phi45` | 515 | 513 | 2 | 285, 286 ms | 362, 360 ms | 0.793x |
| `sd4` | 9 | 8 | 1 | 250, 226 us | 291, 276 us | 0.821x |
| `sd5_x_phi11` | 258 | 256 | 2 | 125.9, 125.8 ms | 144.9, 144.8 ms | 0.869x |
| `sd5` | 129 | 128 | 1 | 62.95, 62.92 ms | 68.00, 67.90 ms | 0.927x |
| `sd4_x_sd4shift1` | 10 | 8 | 2 | 9.31, 9.33 ms | 9.63, 9.63 ms | 0.967x |
| `sd5_shift1` | 1 | 0 | 1 | 57.63, 57.56 ms | 58.79, 57.77 ms | 0.996x |
| `sd5_shift2` | 1 | 0 | 1 | 59.16, 59.03 ms | 59.09, 59.00 ms | 1.000x |
| `legendre_P30` (control) | 1 | 0 | 1 | 182, 165 us | 161, 157 us | 1.048x |
| `xpow36_minus1` | 11 | 2 | 9 | 85.9, 73.2 us | 70.6, 66.1 us | 1.108x |
| `legendre_P38` (control) | 1 | 0 | 1 | 64.1, 55.2 us | 49.9, 48.2 us | 1.145x |
| `chebyshev_T24` (control) | 2 | 0 | 2 | 35.5, 24.5 us | 21.1, 19.7 us | 1.244x |
| `randprod_21` (control) | 3 | 0 | 3 | 52.9, 42.1 us | 34.7, 33.0 us | 1.273x |
| `randprod_10` (control) | 2 | 0 | 2 | 32.4, 23.7 us | 19.3, 18.3 us | 1.294x |
| `chebyshev_U24` (control) | 4 | 0 | 4 | 40.6, 34.3 us | 24.1, 23.7 us | 1.448x |
| `cyclo_phi17` (control) | 1 | 0 | 1 | 13.5, 11.4 us | 5.4, 4.6 us | 2.474x |

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

Median of four baseline sweeps against median of four at this revision.

| instance | baseline | now | |
|---|---:|---:|---:|
| `cyclo_phi1031` | timeout (>10 s) | 4.176 s | **now solves** |
| `cyclo_phi275` | 3.916 s | 917.305 ms | **0.234x** |
| `xpow120_minus1` | 500.454 ms | 152.993 ms | **0.306x** |
| `xpow48_minus1` | 19.464 ms | 11.053 ms | **0.568x** |
| `hoeij_F190` | 6.586 s | 3.793 s | **0.576x** |
| `cyclo_phi61` | 10.680 ms | 7.037 ms | **0.659x** |
| `xpow105_minus1` | 72.643 ms | 49.769 ms | **0.685x** |
| `hoeij_M12_f132` | 1.623 s | 1.132 s | **0.698x** |
| `xpow24_minus1` | 3.285 ms | 2.445 ms | **0.744x** |
| `cyclo_phi41` | 2.913 ms | 2.250 ms | **0.772x** |
| `cyclo_phi128_x_phi165` | 185.837 ms | 147.946 ms | **0.796x** |
| `sd5_x_phi45` | 411.572 ms | 329.090 ms | **0.800x** |
| `cyclo_phi105` | 8.969 ms | 7.250 ms | **0.808x** |
| `cyclo_phi385` | 391.779 ms | 316.837 ms | **0.809x** |
| `sd5_x_phi11` | 165.068 ms | 144.207 ms | **0.874x** |
| `cyclo_phi179` | 56.340 ms | 51.691 ms | 0.917x |
| `sd5` | 76.024 ms | 70.893 ms | 0.933x |
| `cyclo_phi64_x_phi105` | 60.795 ms | 58.288 ms | 0.959x |
| `sd5_shift2` | 67.969 ms | 67.324 ms | 0.991x |
| `sd6` | 8.274 s | 8.220 s | 0.993x |
| `sd4_x_sd4shift1` | 19.296 ms | 19.153 ms | 0.993x |
| `sd5_shift1` | 65.095 ms | 64.686 ms | 0.994x |
| `chebyshev_T24` (control) | 570.996 us | 574.001 us | 1.005x |
| `randprod_21` (control) | 1.774 ms | 1.790 ms | 1.009x |
| `wilkinson_56` | 32.929 ms | 33.216 ms | 1.009x |
| `legendre_P30` (control) | 9.232 ms | 9.351 ms | 1.013x |
| `xpow36_minus1` | 2.943 ms | 2.981 ms | 1.013x |
| `wilkinson_48` | 24.336 ms | 24.666 ms | 1.014x |
| `wilkinson_16` | 1.168 ms | 1.199 ms | 1.027x |
| `wilkinson_24` | 3.562 ms | 3.666 ms | 1.029x |

Aggregate `xpow48 + xpow105 + xpow120`: 592.561 ms to 213.814 ms, **0.361x**.
Summed over the 376 rows both revisions solve: 23.524 s to 16.559 s, **0.704x**.

Distribution over the whole corpus, against the 0.992 to 1.001 noise floor:

| set | n | median | p10 | p90 |
|---|---:|---:|---:|---:|
| all rows | 376 | 1.0078 | 0.9775 | 1.0347 |
| rows above 1 ms | 102 | **0.9936** | 0.7996 | 1.0144 |
| Swinnerton-Dyer families | 22 | 0.9984 | 0.9325 | 1.0336 |
| rows where nearly every candidate divides | 10 | 1.0088 | 0.9937 | 1.0214 |

By family:

| family | n | median | | family | n | median |
|---|---:|---:|---|---|---:|---:|
| hoeij-zimmermann | 2 | **0.637** | | conway | 186 | 1.003 |
| cyclotomic-products | 19 | **0.975** | | swinnerton-dyer | 12 | 1.007 |
| sd-products | 10 | **0.979** | | legendre | 20 | 1.014 |
| cyclotomic | 33 | **0.987** | | laguerre | 20 | 1.015 |
| | | | | random-products | 30 | 1.015 |
| | | | | wilkinson | 15 | 1.022 |
| | | | | chebyshev | 28 | 1.029 |

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

| `xpow120_minus1` (0.306x overall) | before | after |
|---|---:|---:|
| `Hex.directLeaf` | 87.01% | 73.17% |
| ... `Hex.directCandidate` (the `p^k` product) | 15.01% | 45.45% |
| ... `Hex.directCandidateAfterObstruction` | -- | 71.00% |
| ... ... `Hex.FpPoly.modCached` | -- | 22.74% |
| ... `Hex.exactQuotient?` | 71.19% | below threshold |
| `Hex.DensePoly.divModArray` (integer long division) | 73.59% | 9.42% |
| allocator time, all allocators | 70.01% | 49.20% |

| `xpow48_minus1` (0.568x overall) | before | after |
|---|---:|---:|
| `Hex.directLeaf` | 71.73% | 47.05% |
| ... `Hex.directCandidate` | 13.18% | 24.15% |
| ... `Hex.directCandidateAfterObstruction` | -- | 45.92% |
| ... ... `Hex.FpPoly.modCached` | 0.55% | 19.43% |
| ... `Hex.exactQuotient?` | 57.41% | below threshold |
| `Hex.DensePoly.divModArray` | 67.46% | 20.48% |
| allocator time, all allocators | 60.60% | 36.39% |

Rescaling `xpow120_minus1` by its 0.306x whole-run factor: candidate
construction is 15.0% of the old total before and 13.9% after (unchanged, as it
must be), the finite-field remainder costs 7.0% of the old total, and it removes
71.2%.  That ratio -- pay 7, save 71 -- is the whole result on this family.

`Hex.exactQuotient?` no longer appears above the profiler's reporting threshold
on any profiled row.

### Exact divisions removed (phase profile, deterministic)

| instance | exact divisions before | after | recombination phase |
|---|---:|---:|---:|
| `cyclo_phi385` | 8 | 1 | 0.122x |
| `cyclo_phi128_x_phi165` | 25 | 2 | 0.140x |
| `xpow105_minus1` | 60 | 8 | 0.172x |
| `cyclo_phi179` | 2 | 1 | 0.219x |
| `xpow120_minus1` | 1,801 | 16 | 0.264x |
| `xpow48_minus1` | 268 | 10 | 0.391x |
| `xpow24_minus1` | 113 | 8 | 0.501x |
| `sd5_x_phi11` | 258 | 2 | 0.850x |
| `sd5` | 129 | 1 | 0.891x |
| `chebyshev_T24` (control) | 2 | 2 | 1.235x |
| `randprod_21` (control) | 3 | 3 | 1.258x |

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
0.933x, and its profile after this change is:

| | share of `sd5` total, after |
|---|---:|
| `Hex.directCandidatePrefilter` | 27.66% |
| ... `Hex.directTrailingPrefilter` | 18.26% |
| ... ... `Hex.centeredModNat` | 10.44% |
| ... `Hex.directDegreePrefilter` | 9.35% |
| `Hex.directCandidateAfterObstruction` | 7.93% |
| ... `Hex.FpPoly.modCached` | 3.30% |
| `Hex.exactQuotient?` | below threshold |

`sd5` visits 32,768 leaves and only 129 reach the filter, so on that family the
metadata-only prefilters do the rejecting and the obstruction removes 128 of
129 exact divisions -- worth 6.7%, and no more, because exact division was
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
| aggregate `xpow48/105/120` improves materially | met; 0.361x |
| median overhead below 2% on rows with few candidate divisions | met; 0.9% over the ten rows where nearly every candidate divides, and 0.9936 median over all rows above 1 ms, against a 0.8% noise floor |
| no unexplained regression above 5% | met; no row above one millisecond regresses past 1.03x, and every row above 1.05 is under 200 us end to end with a repeat spread of the same size. The largest explained cost is `wilkinson` at 1.022, where `factorTrace` shows the filter rejects zero of its candidates because all of them divide |
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
