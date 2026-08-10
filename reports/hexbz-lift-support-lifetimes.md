# Lift support and residual images: one object each

Issue #9152 asks the proposal traversal to stop packaging two mathematical
objects with different lifetimes in one record. This page records what the two
objects are, which corpus rows can possibly notice, how many of each the peel
run builds before and after, and what the change is worth in time.

The short version: the counts move exactly as predicted, every recorded trace
is identical on both arms, and the time difference is inside the noise floor on
every row. Issue #9152 anticipated that outcome and named it an acceptable
measured result; this page reports it as one.

## The two objects

`Hex.SupportMeta basis target` carried five things:

| field | depends on |
|---|---|
| `modulus` (the prepared `basis.p ^ basis.k`) | the lift |
| `degrees` (one per lifted factor) | the lift |
| `trails` (one per lifted factor) | the lift |
| `image` (the target's image in `F_q[X]`) | the residual polynomial |
| the proof fields | both |

The first three are what a Hensel lift produced. They are constant for as long
as the basis is, which is the whole peel run. The fourth is a reduction of the
polynomial currently being searched, and an exact split replaces that
polynomial, so reusing the reduction past a split would describe a polynomial
the search has left behind.

`Hex.LiftSupport basis` now records the first three with their proofs and
mentions no target at all; `Hex.TargetImage target`, which already existed and
already carried its own reduction proof, records the fourth. Their Lean types
say which is which: `LiftSupport` is indexed by the basis and `TargetImage` by
the polynomial it reduces, so a reduction cannot be handed to a traversal
against a different residual. That is a type error, not a convention.

## Where each is built

`Hex.peelDirect` prepares the lift support once, before the first sweep.
`Hex.peelDirectAux` reduces each residual once, on entry to that residual's
search, and `Hex.findDirectSubset` reuses that reduction across every
cardinality level in the residual's schedule. After an exact split the lift
support is retained and a fresh image is built for the quotient.

Before, `Hex.scanDirectSubsetLevel` built the whole `SupportMeta` per level, so
the lift-wide data was rebuilt after every split *and* whenever a residual
exhausted one cardinality and proceeded to the next.

The head-forced traversal (`Hex.scanDirectCombinations`, the proved classical
engine) now takes the same two objects rather than the mixed one, but
`Hex.scanDirectLevel` still prepares both per level. That is where the mixed
object left them and this change does not move them: hoisting them would add
parameters to `Hex.findDirectHead` and `Hex.searchDirectAux`, which the
classical completeness and correctness proofs quantify over, and the cost it
would remove is one modulus preparation and one reduction per level, amortized
over the `C(n, k)` leaves of that level. #9152 scopes the lifetime split to the
proposal traversal; the head-forced one is a candidate for its own issue, not a
silent rider on this one.

## Which rows can notice

Proposal search is entered only when `Hex.proposalEligible` holds: at least
`proposalLiftedFactorThreshold = 24` lifted modular factors, and a density
condition on the input. **23 of the 392 corpus rows enter it.** The other 369
never call `Hex.peelDirect`, so they build neither object in either arm and this
change cannot reach them; they are controls, not measurements.

This corrects a premise of the issue. #9152 nominates `sd5_x_phi11`,
`sd4_x_sd4shift1`, `xpow48/105/120`, cyclotomic products, Legendre controls and
random products as the rows "whose recorded traces contain completed cardinality
levels". Their *classical* traces do. Their *proposal* traces are empty.
`sd5_x_phi11`, `sd4_x_sd4shift1`, `xpow48_minus1` and `xpow105_minus1` lift to
17, 16, 19 and 14 modular factors, below the threshold of 24; `xpow120_minus1`
lifts to 39 and fails the density condition instead, its degree of 120 against
two nonzero coefficients. None of the five is proposal-eligible, so their
completed levels are the head-forced engine's, which this change leaves where
it found them. The rows that do exercise the proposal traversal are the
Swinnerton-Dyer sixes and sevens, the van Hoeij instances, and Wilkinson 24 and
up.

## Construction counts

Exact, from the peel run's own trace rather than from sampling
(`scripts/bench/proposal_construction_counts.py`, which derives the counts from
`--entry proposalTrace`: `peeledFactorDegrees` gives the splits,
`unforcedCompletedLevels` the exhausted cardinalities, `unforcedDecline` how the
run ended). Every row below runs `peelDirect` exactly once, so "after" builds one
lift support per row by construction.

| row | lifted | peels | residuals searched | levels attempted | lift preparations before/after | target reductions before/after |
|---|---:|---:|---:|---:|---|---|
| `hoeij_F190` | 38 | 1 | 2 | 4 | 4 / 1 | 4 / 2 |
| `sd5_x_sd5shift1` | 32 | 0 | 1 | 3 | 3 / 1 | 3 / 1 |
| `sd6` | 32 | 0 | 1 | 3 | 3 / 1 | 3 / 1 |
| `sd6_shift1` | 32 | 0 | 1 | 3 | 3 / 1 | 3 / 1 |
| `sd6_shift5` | 32 | 0 | 1 | 3 | 3 / 1 | 3 / 1 |
| `sd6_x_phi105` | 36 | 0 | 1 | 3 | 3 / 1 | 3 / 1 |
| `sd6_x_phi13` | 33 | 1 | 2 | 3 | 3 / 1 | 3 / 2 |
| `hoeij_F192` | 96 | 0 | 1 | 2 | 2 / 1 | 2 / 1 |
| `hoeij_F256` | 128 | 0 | 1 | 2 | 2 / 1 | 2 / 1 |
| `hoeij_F351` | 61 | 0 | 1 | 2 | 2 / 1 | 2 / 1 |
| `hoeij_F630` | 108 | 0 | 1 | 2 | 2 / 1 | 2 / 1 |
| `hoeij_P7` | 88 | 0 | 1 | 2 | 2 / 1 | 2 / 1 |
| `hoeij_S7` | 64 | 0 | 1 | 2 | 2 / 1 | 2 / 1 |
| `hoeij_S8` | 128 | 0 | 1 | 2 | 2 / 1 | 2 / 1 |
| `sd6_x_sd6shift1` | 64 | 0 | 1 | 2 | 2 / 1 | 2 / 1 |
| `sd7` | 64 | 0 | 1 | 2 | 2 / 1 | 2 / 1 |
| `hoeij_S9` | 256 | 0 | 1 | 1 | 1 / 1 | 1 / 1 |
| `wilkinson_24` | 24 | 24 | 24 | 24 | 24 / 1 | 24 / 24 |
| `wilkinson_28` | 28 | 28 | 28 | 28 | 28 / 1 | 28 / 28 |
| `wilkinson_32` | 32 | 32 | 32 | 32 | 32 / 1 | 32 / 32 |
| `wilkinson_40` | 40 | 40 | 40 | 40 | 40 / 1 | 40 / 40 |
| `wilkinson_48` | 48 | 48 | 48 | 48 | 48 / 1 | 48 / 48 |
| `wilkinson_56` | 56 | 56 | 56 | 56 | 56 / 1 | 56 / 56 |

Summed over the 23 rows: **269 lift preparations become 23**, and **269 target
reductions become 247**.

Every expectation the issue set is met, including the negative ones:

* one lift-support construction per `LiftData` used by a peel run: every row
  shows `1`, and the 369 ineligible rows show `0` in both arms;
* one target-image construction per distinct residual that enters proposal
  search: the "after" column is the residual count on every row;
* no reduction in Wilkinson target images: 24 to 56 residuals, each attempting
  exactly cardinality one, so 24 / 24 through 56 / 56 unchanged. Wilkinson is
  also where the lift-preparation saving concentrates: it accounts for 228 of
  the 269 preparations and 222 of the 246 removed;
* a reduction in target images only where a search enters several levels: the
  16 rows with `levels attempted > residuals searched` are exactly the rows whose
  reduction column moves.

`hoeij_S9` is the row where the counts are already minimal: its first level does
not fit the remaining budget after one attempt, so both arms build one of each.

### The traces agree

`scripts/bench/proposal_construction_counts.py` was run over the whole 392-row
corpus against both binaries. Every recorded field is identical on both arms:
peels, completed cardinalities, decline reasons, leaves, recordable candidates,
obstruction rejections and exact divisions. The refactor moves where the
prepared objects are built and changes nothing the traversal decides.

## Timing

Host `chungus2` (AMD EPYC 9455, 96 cores, Linux x86-64), one idle core, two
separately linked service binaries, `leanprover/lean4:v4.33.0-rc1`. The host was
shared with other agents throughout, which is why every figure below is a
within-repeat or within-block paired ratio rather than a difference of pooled
medians.

### Per row, counterbalanced

`scripts/bench/factor_row_paired.py`. Each repeat runs both arms once and the
arm that goes first alternates. The ratio is the median of the within-repeat
after/before ratios; the spread is their tenth to ninetieth percentile. `agree`
records that both arms returned the same factor-degree multiset every repeat.

Forty-one repeats:

| row | before | after | ratio | repeat spread | agree |
|---|---:|---:|---:|---|---|
| `sd6` | 27.274 ms | 27.309 ms | 0.997x | 0.965x to 1.027x | same |
| `sd6_shift1` | 31.725 ms | 31.205 ms | 0.978x | 0.955x to 1.013x | same |
| `sd7` | 198.635 ms | 196.853 ms | 0.991x | 0.967x to 1.020x | same |
| `hoeij_S7` | 196.212 ms | 193.917 ms | 0.989x | 0.977x to 1.015x | same |
| `wilkinson_24` | 3.457 ms | 3.461 ms | 0.996x | 0.978x to 1.023x | same |
| `wilkinson_40` | 9.203 ms | 9.225 ms | 1.001x | 0.994x to 1.011x | same |
| `wilkinson_56` | 21.177 ms | 21.269 ms | 1.004x | 0.992x to 1.016x | same |
| `sd5_x_phi11` | 130.341 ms | 133.393 ms | 1.024x | 1.013x to 1.039x | same |
| `xpow120_minus1` | 145.638 ms | 145.587 ms | 0.998x | 0.991x to 1.009x | same |
| `legendre_P16` | 0.535 ms | 0.538 ms | 0.989x | 0.949x to 1.060x | same |

Nine repeats (rows costing about three seconds):

| row | before | after | ratio | repeat spread | agree |
|---|---:|---:|---:|---|---|
| `hoeij_F190` | 3241.756 ms | 3226.804 ms | 0.994x | 0.987x to 1.003x | same |
| `sd6_x_phi13` | 2897.841 ms | 2899.976 ms | 1.009x | 0.991x to 1.011x | same |
| `hoeij_S8` | 3948.922 ms | 4009.324 ms | 1.014x | 1.008x to 1.020x | same |
| `cyclo_phi1031` | 2607.007 ms | 2610.833 ms | 0.999x | 0.653x to 1.009x | same |

`sd5_x_phi11`, `xpow120_minus1`, `legendre_P16` and `cyclo_phi1031` are the
controls: none enters proposal search, so nothing in this change can reach them.
`sd5_x_phi11` at 1.024x is the largest deviation in either table and it is on a
control, which sets the scale: this pair of binaries differs by about two per
cent on rows the change cannot touch, and no target row moves further than that.

The target rows land between 0.978x and 1.014x with spreads that straddle 1.0.
That is the expected result. The largest saving available on any of these rows
is two modulus preparations and two reductions against runtimes of tens or
thousands of milliseconds.

### Whole corpus, paired blocks

`scripts/bench/factor_sweep_paired.py`, four counterbalanced AB/BA/AB/BA blocks
over the whole 392-instance corpus at a ten-second cutoff, one core, per-instance
median of the within-block after/before ratios.

383 instances were priced in every block on both arms; none was lost and none
gained. Summed medians 16.250 s before against 16.335 s after.

| statistic | after / before | before / before | after / after |
|---|---:|---:|---:|
| median, all 383 rows | 1.0060x | 0.9968x | 0.9974x |
| median, the 14 proposal-search rows priced | 1.0091x | 1.0013x | 0.9999x |
| median, the 369 rows proposal search never reaches | 1.0058x | 0.9965x | 0.9971x |
| tenth to ninetieth percentile | 0.9813x to 1.0196x | 0.9755x to 1.0153x | 0.9825x to 1.0097x |
| rows above 1.05x | 6 | 3 | 1 |
| rows below 0.95x | 7 | 8 | 3 |

Read the columns against each other rather than against 1.0. The after/before
arm sits 0.6% high **on rows this change cannot execute a single new instruction
for**, and a same-binary comparison moves the median by a comparable amount in
the other direction. Whole-arm offsets of that size are what two separately
linked binaries, and this shared host, produce.

The statistic that would show an effect is the gap between the proposal-search
rows and the rest, because only the former build the objects this change moves.
That gap is **+0.33%** in the after/before comparison, **+0.48%**
before-against-before and **+0.28%** after-against-after: the real comparison
sits between its two controls.
There is no effect here to report, which is what the counts predict. Two
preparations and two reductions removed from runs costing between three
milliseconds and four seconds cannot show up, and they do not.

Six rows sit above 1.05x, against three in the same-arm control. None costs more
than 0.3 ms and none is a proposal-search row:

| instance | before | after | ratio | block spread |
|---|---:|---:|---:|---|
| `conway_p97_n4` | 34.0 us | 38.0 us | 1.085x | 0.726x to 1.119x |
| `cyclo_phi23` | 253.0 us | 268.0 us | 1.070x | 0.981x to 1.554x |
| `chebyshev_T7` | 66.0 us | 70.0 us | 1.063x | 0.932x to 1.100x |
| `conway_p65537_n1` | 22.0 us | 23.0 us | 1.063x | 0.576x to 1.143x |
| `cyclo_phi5` | 38.0 us | 40.0 us | 1.062x | 0.981x to 1.433x |
| `sd3_shift1` | 167.0 us | 175.0 us | 1.052x | 1.012x to 1.233x |

No instance above 1.05x costs more than 2 ms, in either the real comparison or
the same-arm control.

**Family medians** (after / before):

| family | rows | median | rows over 2 ms | median over 2 ms |
|---|---:|---:|---:|---:|
| certificate-boundary | 1 | 0.9515x | 0 | -- |
| chebyshev | 28 | 1.0101x | 0 | -- |
| conway | 186 | 1.0028x | 0 | -- |
| cyclotomic | 34 | 1.0130x | 15 | 1.0102x |
| cyclotomic-products | 19 | 1.0101x | 11 | 1.0101x |
| hoeij-zimmermann | 4 | 1.0049x | 4 | 1.0049x |
| laguerre | 20 | 1.0111x | 2 | 1.0081x |
| legendre | 20 | 1.0018x | 4 | 1.0071x |
| random-products | 30 | 1.0037x | 0 | -- |
| sd-products | 11 | 1.0083x | 6 | 1.0093x |
| swinnerton-dyer | 15 | 1.0028x | 7 | 1.0028x |
| wilkinson | 15 | 1.0113x | 7 | 1.0112x |

Wilkinson, the family where every lift preparation but one is removed, sits at
1.0113x; Chebyshev, which never enters proposal search, sits at 1.0101x, and
cyclotomic at 1.0130x. The family that should move most is indistinguishable
from families that cannot move at all.

## What this leaves

`Hex.LiftSupport` is the object #9153 should extend with its retained-prime
information: it is indexed by the lifted basis, which is what that information
depends on, and it now has no second index to force a spurious dependency on the
current residual.

The head-forced traversal still prepares both objects per cardinality level, as
described above. That is a separate change with its own proof surface.

## Records

* `reports/bench-results/hexbz-lift-support-counts-before-cb1ecd2d-chungus2.json`
  and `...-after-f29828f0-chungus2.json`, the whole-corpus construction-count
  records the tables above are drawn from.
* `reports/bench-results/hexbz-lift-support-paired-f29828f0-chungus2.json`, the
  four-block paired corpus sweep, every block retained.
* `reports/bench-results/hexbz-lift-support-samearm-before-cb1ecd2d-chungus2.json`
  and `...-samearm-after-f29828f0-chungus2.json`, the two same-binary noise-floor
  sweeps, same protocol.
* `reports/bench-results/hexbz-factor-sweep-hex-SWEEPSHA-chungus2.json`, the
  published hex-factor sweep this branch's figures are drawn from. The
  comparator record (FLINT, NTL, PARI, both Isabelle extractions) is reused
  unchanged.
