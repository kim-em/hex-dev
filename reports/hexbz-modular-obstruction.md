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

`Hex.obstructs` is that test, `Hex.obstructs_eq_false_of_dvd` is the statement
that it never rejects a genuine divisor, and
`Hex.exactQuotient?_eq_none_of_obstructs` is the equation the traversal rewrites
through: an obstructed candidate is one exact division would have refused.
`Hex.directCandidateAfterObstruction_eq` then says the guarded leaf returns
exactly what the unguarded leaf returned, so `Hex.directLeaf_eq` and the
classical completeness proofs above it are unchanged.

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

- Source revision `39b4d5ba1ca0cb2d59b51eb2f140b5d5d61e9cab` (clean worktree),
  Lean toolchain `leanprover/lean4:v4.33.0-rc1`.
- Baseline `9d3590500d551dfebf6c9bb5940f2f961753f53e`, this branch's merge base,
  built and swept on the same host in the same session.  The committed
  `f8477abd` record is *not* the baseline: `main` moved between it and this
  branch point, and against it rows this change cannot touch (`cyclo_phi121`
  1.99x, `legendre_P20` 1.95x) move more than rows it can.
- Host `chungus2`, AMD EPYC 9455, Linux x86-64, 96 cores, measured service
  pinned to CPU 70.  Other agents were building on the host throughout, so
  every sweep number below is the median of repeats: two complete sweeps at the
  baseline, three at this revision.  Repeat-to-repeat median across the corpus
  is 1.0025 with p90 1.036, which is the noise floor these comparisons sit on.
- Corpus `bench/corpus/hexbz-factor-corpus.jsonl`, 392 rows, SHA-256
  `619913904240834c912489e6cc23ba136e8cc5ebf0ea95f83397e0682387284d`.
- Sweep: persistent warm service, ten-second per-call cutoff, median of five
  calls below one second and one call otherwise, early termination disabled.

### Artifacts

Every repeat is committed, so the medians below are reproducible and not just
asserted.  `142d02a2` differs from `39b4d5ba` only in documentation; the
published Hex curve is the `39b4d5ba` sweep, which is the newest and therefore
the one the plotting and freshness tools select.

| Record | SHA-256 |
|---|---|
| `hexbz-factor-sweep-39b4d5ba-hex-chungus2.json` (published) | `9a2dbb2e4d92baedde8265f8bb2f730f5fc2f37a718000f7cbfbc0e445812b20` |
| `hexbz-factor-sweep-142d02a2-hex-chungus2.json` | `699da88ddfe713a56327ea8273c9e0f8c3c152102b2f8d706999f07cb913155d` |
| `hexbz-factor-sweep-142d02a2-hex-chungus2-run2.json` | `ffe98b35a26dde75afb1e269ce1fe6e9a508ff43da7e6b48311370f173e0a1cf` |
| `hexbz-factor-sweep-9d359050-hex-chungus2.json` (baseline) | `19d9392493a08e2d9a4a25cc101fb4ea6f4d577ab10a1f11cab39ccf752002df` |
| `hexbz-factor-sweep-9d359050-hex-chungus2-run2.json` (baseline) | `a2866501ff7e7cad9fcf7de3a71bb93dc3aeefc7a7b05e26ffd2ee7b35112342` |
| `hexbz-phase-profile-39b4d5ba-chungus2.json` | `12de7405908f2ef1af437361ebefc8fc4ddfa971623638fe408f249562500283` |
| `hexbz-phase-profile-9d359050-chungus2.json` (baseline) | `cadf62d3f4c099f19a8880ae9e5b89d498295e99486701ba12b65c7bc9e5dc29` |
| `hexbz-factor-sampling-profiles-39b4d5ba-chungus2.json` | `8a2d8cf4ba1603a109da4080b4d4c3ffca0f6a472801daa31bed287d270d673f` |
| `hexbz-factor-sampling-profiles-9d359050-chungus2.json` (baseline) | `4758e485ed025ed4a4bbf9386cb884154e0d9a346abb30e267153ef3d5255105` |

All are under `reports/bench-results/`.  The comparator record
`hexbz-factor-sweep-aa68c920-chungus2.json` (FLINT, NTL, PARI, both Isabelle
extractions) is reused unchanged.

## What the filter rejects

`hexbz_factor_service --entry obstructionProbe` runs the counted recombination
mirror twice on one input -- once as production now runs it, once as it ran
before the obstruction existed -- and reports both stage-counter sets and both
spans.  The mirror was built and measured before production consumed the
filter; the numbers below are from the merged revision, where the two
executions are the two sides of the change.

| instance | reached filter | rejected | fell through | exact divisions avoided | recombination |
|---|---:|---:|---:|---:|---:|
| `xpow120_minus1` | 1,801 | 1,785 | 16 | 1,785 | **0.255x** |
| `cyclo_phi385` | 8 | 7 | 1 | 7 | **0.125x** |
| `cyclo_phi128_x_phi165` | 25 | 23 | 2 | 23 | **0.144x** |
| `cyclo_phi275` | 512 | 511 | 1 | 511 | **0.165x** |
| `xpow105_minus1` | 60 | 52 | 8 | 52 | **0.170x** |
| `cyclo_phi179` | 2 | 1 | 1 | 1 | **0.210x** |
| `xpow48_minus1` | 268 | 258 | 10 | 258 | **0.350x** |
| `cyclo_phi105_x_phi128` | 28 | 26 | 2 | 26 | 0.486x |
| `xpow60_minus1` | 31 | 19 | 12 | 19 | 0.472x |
| `xpow24_minus1` | 113 | 105 | 8 | 105 | 0.510x |
| `cyclo_phi41` | 16 | 15 | 1 | 15 | 0.566x |
| `hoeij_M12_f132` | 462 | 461 | 1 | 461 | 0.586x |
| `sd5_x_phi45` | 515 | 513 | 2 | 513 | 0.801x |
| `sd5_x_phi11` | 258 | 256 | 2 | 256 | 0.875x |
| `sd4` | 9 | 8 | 1 | 8 | 0.859x |
| `sd5` | 129 | 128 | 1 | 128 | 0.923x |
| `sd4_x_sd4shift1` | 10 | 8 | 2 | 8 | 0.979x |
| `xpow36_minus1` | 11 | 2 | 9 | 2 | 1.209x |
| `sd5_shift1` | 1 | 0 | 1 | 0 | 0.988x |
| `legendre_P30` (control) | 1 | 0 | 1 | 0 | 1.116x |
| `randprod_21` (control) | 3 | 0 | 3 | 0 | 1.483x |
| `chebyshev_T24` (control) | 2 | 0 | 2 | 0 | 1.473x |

Over the 32 profiled instances, **4,302 candidates reached the filter, 4,204
were rejected, and 98 fell through -- and all 98 were genuine divisors.**  Every
non-divisor that reached the filter was rejected, and no divisor was.  On rows
that answer through proposal replay or the lattice tier (`wilkinson_40/48/56`,
`sd6`) the head-forced traversal is not entered at all, so they have no row
here; the sweep still covers them, and they do not move.

The mirror also checks that the filtered and unfiltered executions return the
same divisors, complete the same cardinalities, and produce the same factor
degrees.  They do, on every row.

The last four rows are the cost side, isolated: on inputs where every candidate
that reaches the filter is a real divisor, the obstruction is pure overhead and
recombination costs up to 1.48x.  It is a small phase on those rows -- see the
whole-run column below.

## Measured effect

### Total factor time (sweep)

Median of two baseline sweeps against median of three at this revision.

| instance | baseline | now | |
|---|---:|---:|---:|
| `cyclo_phi1031` | timeout (>10 s) | 6.470 s | **now solves** |
| `cyclo_phi275` | 3.973 s | 943.683 ms | **0.238x** |
| `xpow120_minus1` | 477.497 ms | 153.760 ms | **0.322x** |
| `xpow48_minus1` | 19.596 ms | 10.999 ms | **0.561x** |
| `hoeij_F190` | 6.624 s | 3.832 s | **0.579x** |
| `cyclo_phi61` | 10.741 ms | 6.995 ms | **0.651x** |
| `xpow105_minus1` | 74.606 ms | 51.437 ms | **0.689x** |
| `hoeij_M12_f132` | 1.628 s | 1.152 s | **0.708x** |
| `xpow24_minus1` | 3.288 ms | 2.426 ms | **0.738x** |
| `cyclo_phi41` | 2.925 ms | 2.232 ms | **0.763x** |
| `sd5_x_phi45` | 416.933 ms | 334.024 ms | **0.801x** |
| `cyclo_phi105` | 8.973 ms | 7.205 ms | **0.803x** |
| `cyclo_phi128_x_phi165` | 198.513 ms | 162.091 ms | **0.817x** |
| `cyclo_phi385` | 436.108 ms | 358.547 ms | **0.822x** |
| `sd5_x_phi11` | 164.416 ms | 145.735 ms | **0.886x** |
| `cyclo_phi179` | 74.656 ms | 69.971 ms | 0.937x |
| `sd5` | 76.566 ms | 72.090 ms | 0.942x |
| `cyclo_phi64_x_phi105` | 61.378 ms | 58.743 ms | 0.957x |
| `sd6` | 8.371 s | 8.103 s | 0.968x |
| `sd5_shift1` | 66.657 ms | 65.563 ms | 0.984x |
| `sd4_x_sd4shift1` | 19.662 ms | 19.383 ms | 0.986x |
| `sd5_shift2` | 69.082 ms | 68.163 ms | 0.987x |
| `wilkinson_56` | 34.512 ms | 34.592 ms | 1.002x |
| `wilkinson_48` | 25.375 ms | 25.545 ms | 1.007x |
| `randprod_21` (control) | 1.762 ms | 1.782 ms | 1.011x |
| `legendre_P30` (control) | 9.278 ms | 9.420 ms | 1.015x |
| `chebyshev_T24` (control) | 562.549 us | 576.035 us | 1.024x |
| `xpow36_minus1` | 2.904 ms | 2.998 ms | 1.032x |

Aggregate `xpow48 + xpow105 + xpow120`: 571.699 ms to 216.196 ms, **0.378x**.
Summed over the 376 rows both revisions solve: 23.801 s to 16.628 s, **0.699x**.

Distribution over the whole corpus:

| set | n | median | p10 | p90 | max |
|---|---:|---:|---:|---:|---:|
| all rows | 376 | 1.0061 | 0.9701 | 1.0329 | 1.181 |
| rows above 1 ms | 102 | **0.9990** | 0.8030 | 1.0137 | 1.033 |
| Swinnerton-Dyer families | 22 | 0.9847 | 0.9136 | 1.0214 | 1.037 |
| rows where every candidate divides | 10 | 1.0157 | -- | -- | 1.032 |

Every row whose median-of-repeats ratio exceeds 1.05 is below 0.4 ms end to end
(`conway_p2_n1` 29 us, `chebyshev_T3` 38 us, `chebyshev_U4` 56 us,
`conway_p65537_n2` 38 us, `chebyshev_T5` 38 us, `quartic_a4` 50 us,
`randprod_05` 375 us), and each has a repeat-to-repeat spread of the same size
or larger -- `chebyshev_T3` alone spans 1.55x between identical builds.  On rows
above 1 ms, where the measurement is meaningful, the median is 0.9990 and the
largest regression is 1.033x.

`xpow36_minus1` is the one explained regression with a mechanism rather than
noise: 9 of its 11 candidates are genuine divisors, so the filter is nearly all
cost there.  It is 1.032x, on a 2.9 ms row.

### Where the time went (sampling profiles)

Shares of each run's own total, so the two columns are not the same absolute
time; the row underneath each block gives the whole-run factor from the sweep.

| `xpow120_minus1` (0.322x overall) | before | after |
|---|---:|---:|
| `Hex.directLeaf` | 86.67% | 72.00% |
| ... `Hex.directCandidate` (the `p^k` product) | 14.74% | 42.69% |
| ... `Hex.obstructs` | -- | 25.94% |
| ... ... `Hex.FpPoly.modCached` | -- | 24.18% |
| ... `Hex.exactQuotient?` | 71.19% | below threshold |
| `Hex.DensePoly.divModArray` (integer long division) | 73.94% | 9.36% |
| allocator time, all allocators | 70.94% | 48.10% |

| `xpow48_minus1` (0.561x overall) | before | after |
|---|---:|---:|
| `Hex.directLeaf` | 71.58% | 47.93% |
| ... `Hex.directCandidate` | 12.69% | 24.25% |
| ... `Hex.obstructs` | -- | 20.79% |
| ... `Hex.exactQuotient?` | 57.65% | below threshold |
| `Hex.DensePoly.divModArray` | 67.33% | 19.96% |
| allocator time, all allocators | 61.75% | 35.10% |

Rescaling `xpow120_minus1` by its 0.322x whole-run factor: candidate
construction is 14.7% of the old total before and 13.7% after (unchanged, as it
must be), the obstruction costs 8.4% of the old total, and it removes 71.2%.
That ratio -- pay 8, save 71 -- is the whole result on this family.

`Hex.exactQuotient?` no longer appears above the profiler's reporting threshold
on any profiled row.

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
one of the 98 pass-throughs across the profiled corpus was a genuine divisor.
There is nothing for a second modulus to reject, and it would add its cost to
exactly the rows that are already the cost side of this change.

## What this does not fix: the Swinnerton-Dyer prefilter arithmetic

#9130's comment identified a second target on `sd5`, larger than the
exact-division target on the `x^n - 1` rows, and it is still there.  `sd5` moves
0.942x, and its profile after this change is:

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
129 exact divisions -- worth 5.8%, and no more, because exact division was
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
| no false rejection; cannot accept a factor | met; `Hex.obstructs_eq_false_of_dvd` and `Hex.exactQuotient?_eq_none_of_obstructs`, with acceptance still only through `exactQuotient?` |
| at least half the exact divisions on the material `xpow` controls avoided | met, far above threshold: 258/268, 52/60, 1,785/1,801 -- 96%, 87%, 99% |
| aggregate `xpow48/105/120` improves materially | met; 0.378x |
| median overhead below 2% on rows with few candidate divisions | met; 1.6% over the ten rows where nearly every candidate divides, 0.999 median over all rows above 1 ms |
| no unexplained regression above 5% | met; every ratio above 1.05 is a sub-0.4 ms row whose repeat spread is at least as large, and `xpow36_minus1` (1.032x) is explained by 9 of its 11 candidates being real divisors |
| exactly one exact quotient implementation and one production reconstruction path | met; `exactQuotient?` is untouched and the obstruction only decides whether to call it |
| full build, conformance, oracle and factorization tests pass | met; all oracles pass, `bz_trace_gate.py` checks 54 traces with 0 failures, and `hexbz_emit_fixtures` output is byte-identical to the committed fixtures |
| fresh full Hex sweep and regenerated figures | recorded above; all 25 SVGs regenerated, external comparator record reused |

## Regeneration

```sh
lake build hexbz_factor_service

# Pin to an idle core; repeat, because other work shares this host.
taskset -c 70 python3 scripts/bench/factor_sweep.py \
  --systems hex-factor --cutoff 10 --no-early-terminate \
  --output /tmp/hexbz-factor-sweep.json

taskset -c 70 python3 scripts/bench/factor_phase_profile.py \
  --output /tmp/hexbz-phase-profile.json

# No outer `taskset`: the profiler pins the service itself, and wrapping it
# leaves samply with no thread to attribute.
python3 scripts/profile/factor_sampling_profile.py \
  --cpu 70 --output /tmp/hexbz-factor-sampling-profiles.json

# Filter counters, both sides of the change, from one execution each.
.lake/build/bin/hexbz_factor_service --entry obstructionProbe < requests.jsonl

python3 scripts/bench/cactus_rank_table.py --lo 118 --hi 144

uv run --with matplotlib==3.11.1 python3 scripts/plots/hexbz-cactus.py
uv run --with matplotlib==3.11.1 python3 scripts/plots/hexbz-cactus.py --check
```
