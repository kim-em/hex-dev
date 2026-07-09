# Berlekamp-Zassenhaus: recursive per-remainder re-lift measurement (#8625)

This report records the measurement gating deliverable 2 of
https://github.com/kim-em/hex-dev/issues/8625 ("spike(bz): investigate
recursive per-remainder re-lift for sub-floor classical irreducibility
certification"). It quantifies, on the adversarial and degree/height bench
families, how much lift work the recursive per-remainder re-lift saves over
today's single core-floor lift, and what the recursion costs end to end.

## Headline

1. **The sub-floor lift-work win is real and large on composite cores.** In
   the degree-weighted lift model (`sum deg^2 * k`), the recursion does
   4-16x less lift work than today's single core-floor lift on the split
   degree/height families (deg 24: 12672 -> 776), and 9x less on
   `adv/high_multiplicity`. On irreducible cores the win is zero by
   definition (the sole remainder is the core, and its own floor is the
   core floor).

2. **A naive recursion loses that win back, with interest, to two
   overheads.** (a) Sub-floor ladder rungs pay *failed recombination scans*:
   at a rung below a factor's recovery precision that factor's subset always
   fails, and after peeling the recoverable pieces the smart scan burns
   `C(r', <= r'/2)` failed candidates, each costing big-int division work
   against the target's huge coefficients. (b) The fresh-prime variant
   re-pays `choosePrimeData?` (prime walk + Berlekamp) per remainder --
   18.9 ms on a deg-24 input, a third of today's *entire* runtime. Net:
   2.5-3.8x end-to-end LOSS on the very split families whose lift work the
   recursion cuts 10-16x.

3. **Both overheads are removable, and then the win is real end to end.**
   Reusing the parent's prime and the remainder's own local factors
   (same-prime variant, no per-node prime walk or Berlekamp) and capping
   sub-floor rung scans at small subset sizes turns the recursion into a
   robust ~2x end-to-end WIN on every split family measured (deg 24:
   61.4 ms -> 30.0 ms) and 1.6x on `adv/high_multiplicity`, at a bounded
   1.17-1.25x overhead on the irreducible adversarial inputs (Phi15, SD3,
   SD4). The sub-floor scan cap must be >= 2 for `adv/mignotte_swell` (its
   sub-floor split is a pair of size-2 subsets; singleton-only sub-floor
   rungs push its certification back to the floor and lose 2x, vs 1.3x
   with cap 2).

4. **Recommendation: the mechanism is viable in the same-prime, small-cap
   form, but deliverable 2 should be sequenced after #8621.** The balanced
   product-tree lift attacks the same lift cost with an output-preserving
   change and no certification re-key; landing it first shrinks the lift
   share of runtime and therefore the residual value of per-remainder
   precision reduction, which should be re-measured on top of it before
   committing to the ~5-file proof remodel. Details in "Deliverable-2
   assessment" below.

## Background

Classical-tier irreducibility flows through coverage
(`RecoveredSmartSearch.covers_of_bound`), which consumes a complete
`LiftedFactorSubsetPartition`. Every initial-partition producer is gated at
the monic-core Mignotte floor
`2 * defaultFactorCoeffBound (toMonic core).monic < p^k`, and the
per-remainder recursion inherits that partition at the same `LiftData`
(`liftedFactorSubsetPartition_transport`), so no remainder can be certified
below the core floor inside the existing architecture (established in
https://github.com/kim-em/hex-dev/issues/8620). The one sound sub-floor
route is a FRESH lift/partition/coverage stack per unsplit remainder at the
remainder's OWN floor. This spike measures that algorithm.

Two lift-free certificates come along for free and matter a lot on split
inputs: a degree <= 1 remainder is irreducible outright, and a remainder
that is irreducible mod a good prime (r = 1, the `SmallModSingleton` chain)
is irreducible over Z with no lift at all.

## Prototype

`bench/HexBench/RecursiveReliftSpike.lean` (`lake exe
hex_recursive_relift_spike`), unproven, alongside `ClassicalSpike.lean` and
reusing the library's `choosePrimeData?`, `henselLiftData`,
`multifactorLiftQuadratic`, and bound definitions (`defaultFactorCoeffBound`,
`exhaustiveLiftBound`, `precisionForCoeffBound`). Restricted to monic
squarefree cores (all corpus cores here are monic; `adv/high_multiplicity`
enters via its squarefree core, as production does after
`normalizeForFactor`).

The recursion: per remainder, run an escalation ladder `k = 1, 2, 4, ...`
clamped at the remainder's own floor
`precisionForCoeffBound (defaultFactorCoeffBound (toMonic g).monic) p`; at
each rung lift and run the smart subset recombination; a split recurses on
the pieces; reaching the floor without a split certifies the remainder
irreducible (that is the rung whose fresh partition the deliverable-2 proof
would consume). Variants:

* **fresh-prime**: each remainder gets its own `choosePrimeData?`.
* **same-prime**: each remainder keeps the parent's prime and its own
  local factors (known from the split that produced it); a sub-`k` cap
  parameter restricts which subset sizes the scan tries at rungs below the
  floor (`cap1` = singletons only, `cap2` = up to pairs, `full` = no cap).

All arms (including the "today" baseline) share the same recombination scan
with a d-1 trailing-coefficient prefilter and a bounded exact division that
aborts once a quotient coefficient exceeds the node's Mignotte factor bound.
Production recombination has an equivalent trailing-coefficient residue
test; without the bounded division the naive `exactQuotient?` full `divMod`
inflates the recursion's failed scans by a further ~20-25%.

Honest caveats, all of which overstate the recursion's cost:

* every rung re-lifts from scratch (a real implementation continues the
  quadratic Hensel ladder incrementally, so the ladder to `kStop` costs
  about one lift to `kStop`);
* the today-baseline for most families is fed `B = mignotte(core)` (the
  input IS its own core), i.e. it already includes the #8620 "rewrite-1"
  core-local tightening -- the measured wins are on top of that;
* plain `Int` arithmetic throughout, as in `ClassicalSpike.lean`.

Correctness cross-checks: every run re-multiplies the certified factors and
compares with the core (`product_ok=true` on all 18 cases x 4 variants), and
degree signatures match the known factorizations (checksums agree across
arms on the irreducible families).

## Lift-work accounting

`k_today` is today's single-lift exponent
`precisionForCoeffBound (exhaustiveLiftBound core (mignotte f)) p`;
`work` is the `sum deg^2 * k` model. `sumK` sums the recursion's per-node
ladder stops (0 for the lift-free certificates). fresh-prime and same-prime
agree except where noted; cap1/cap2 differ from full only on
`adv/mignotte_swell`.

| input | deg | k_today (work) | rec sumK (work) | outcome shape |
|---|---|---|---|---|
| split deg3 h2 | 3 | 5 (45) | 2 (18) | split at k=2; 3 linear pieces free |
| split deg4 h8 | 4 | 9 (144) | 6 (68) | two-level split |
| split deg6 h32 | 6 | 17 (612) | 4 (144) | split at k=4; 6 linear pieces free |
| split deg12 h32 | 12 | 28 (4032) | 6 (688) | two-level split |
| split deg12 h0 | 12 | 12 (1728) | 3 (216) | split k=1, remainder k=2 |
| split deg16 h0 | 16 | 16 (4096) | 3 (384) | split k=1, remainder k=2 |
| split deg20 h0 | 20 | 19 (7600) | 3 (562) | split k=1, remainder k=2 |
| split deg24 h0 | 24 | 22 (12672) | 3 (776) | split k=1, remainder k=2 |
| adv/high_multiplicity core | 3 | 9 (81) | 1 (9) | split k=1; x^2+1 is r=1 (free), x-3 free |
| adv/mignotte_swell | 8 | 13 (832) | 22 (736) | split k=8; quartics floor-certified k=7 each |
| adv/mignotte_swell (cap1) | 8 | 13 (832) | 27 (1056) | sub-floor split lost; floor 13 + quartic floors |
| cyclotomic Phi15 | 8 | 4 (256) | 4 (256) | floor-certified, no win possible |
| SD3 | 8 | 7 (448) | 7 (448) | floor-certified, no win possible |
| SD4 | 16 | 12 (3072) | 12 (3072) | floor-certified, no win possible |
| (x-1)*SD3 | 9 | 7 (567) | 8 (529) | x-1 free; SD3 floor ~ core floor |
| (x-1)*SD4 | 17 | 12 (3468) | 13 (3361) | x-1 free; SD4 floor ~ core floor |

Notes: `k_corelocal` (#8620 rewrite-1) equals `k_today` on every case except
`adv/high_multiplicity` (9 -> 4), confirming the earlier finding that the
caller-B over-lift only matters on high-content/high-multiplicity inputs.
On `adv/mignotte_swell` the recursion's raw `sumK` EXCEEDS today's `k`
(22 vs 13: exploration to k=8 plus two quartic floors of 7) while the
degree-weighted work is slightly below (736 vs 832) because the quartic
lifts run on deg-4 targets; swell is a wash at best, by either metric.

## Wallclock (end to end, distinct-input families)

us/call. "today" is a **shared-scan baseline**, not production runtime: it
runs today's single lift at production precision but recombines with the
prototype's scan (same filters as every other arm), so lift-strategy
differences are isolated from scan-implementation differences.
"production" anchors that baseline: it is the real
`classicalCoreFactorsWithBound` (`toMonicLiftData` +
`scaledRecombinationSmart`, with its own residue filters and subset
budget) at the same `B`. same-prime cap2 is the recommended policy.

| family | production | today | fresh-prime | same-prime full | cap1 | cap2 | cap2 vs today |
|---|---|---|---|---|---|---|---|
| split deg12 | 5844 | 5838 | 6468 | 5733 | 3275 | 3362 | **1.74x win** |
| split deg16 | 17741 | 17718 | 46146 | 44058 | 8636 | 8946 | **1.98x win** |
| split deg20 | 35661 | 35569 | 111782 | 108933 | 16492 | 16909 | **2.10x win** |
| split deg24 | 61491 | 61425 | 240357 | 241262 | 29361 | 29955 | **2.05x win** |
| adv/high_multiplicity | 126 | 124 | 96 | 79 | 79 | 79 | **1.57x win** |
| adv/mignotte_swell | 969 | 968 | 1453 | 1284 | 1938 | 1279 | 1.32x loss |
| phi15 | 678 | 673 | 786 | 784 | 784 | 784 | 1.17x loss |
| SD3 | 1138 | 1145 | 1512 | 1438 | 1429 | 1435 | 1.25x loss |
| SD4 | 11754 | 12399 | 16302 | 16277 | 15372 | 15476 | 1.25x loss |
| (x-1)*SD3 | 1871 | 1859 | 2836 | 2030 | 2018 | 2030 | 1.09x loss |

The production column matches the shared-scan baseline within noise on
every family (identical factor checksums except ordering on (x-1)*SD3),
so the shared-scan normalization neither flatters nor penalizes either
side on this corpus. Production declined nothing here (its subset budget
was never exhausted).

### Re-measurement on current main (post #8633 / #8638 / #8641)

The ZMod64 arithmetic speedups that came out of
https://github.com/kim-em/hex-dev/issues/8630 (dead per-multiply bignum
allocation removed, `p < 2^31` bounds tightening, `-O3` externs) shifted
the absolute numbers; the geography is unchanged and the recursion's win
cases improved slightly (us/call, same arms as above):

| family | production | today | cap1 | cap2 | cap2 vs today |
|---|---|---|---|---|---|
| split deg12 | 5189 | 5159 | 2482 | 2580 | **2.00x win** |
| split deg16 | 16152 | 16167 | 6735 | 7019 | **2.30x win** |
| split deg20 | 33057 | 33062 | 13439 | 13745 | **2.41x win** |
| split deg24 | 56502 | 56548 | 23824 | 25790 | **2.19x win** |
| adv/high_multiplicity | 105 | 102 | 58 | 58 | **1.76x win** |
| adv/mignotte_swell | 1019 | 760 | 1606 | 983 | 1.29x loss |
| phi15 | 349 | 344 | 435 | 439 | 1.27x loss |
| SD3 | 655 | 650 | 887 | 896 | 1.38x loss |
| SD4 | 6677 | 7279 | 9934 | 9990 | 1.37x loss |
| (x-1)*SD3 | 1059 | 1048 | 1139 | 1151 | 1.10x loss |

Prime selection after the same changes: deg-24 split 18.7 -> 13.8 ms,
phi15 484 -> 183 us, SD4 8.4 -> 3.2 ms, single deg-24 `isGoodPrime`
424 -> 299 us — still boxing/reduction-bound, consistent with
https://github.com/kim-em/hex-dev/issues/8642 (packed `modByMonic` is the
remaining lever there). The irreducible-core loss ratios worsened slightly
(their baseline is exactly the gcd/Berlekamp/mod-p work that got faster,
while the ladder's repeated scans did not), which strengthens the
sequencing recommendation: re-measure after #8642 and #8621 before
committing to deliverable 2.

## Where the recursion's time actually goes

Per-phase breakdown on the deg-24 split family (fresh-prime, before the
bounded division landed): `choosePrimeData?` 18.9 ms, lift to k=1 +0.8 ms,
k=1 recombination +107.7 ms, against 62 ms for today's ENTIRE run. Two
structural facts fall out:

* **Prime selection is not a rounding error.** The prime walk (each
  candidate prime pays a mod-p squarefree check on a high-content input
  before one is accepted) plus one Berlekamp costs about a third of today's
  total on deg-24 inputs. Any per-remainder design that re-selects primes
  per node pays this per node; reusing the parent's prime and handing each
  piece its own local factors (which the split already identifies) makes
  the marginal certification cost of a node just its lift + scan.
* **Sub-floor rungs fail combinatorially, and failures are not free.** The
  d-1 trailing-coefficient filter is ineffective exactly on high-content
  targets (a factorial-like constant term is divisible by nearly every
  small candidate constant), and the Mignotte-bounded division still runs
  most of each short division before the abort bound can fire (the bound
  is orders of magnitude above the target's own coefficients). Capping
  sub-floor rungs at small subset sizes is what actually removes the tail:
  singleton peels are cheap successes, and the failed tail drops from
  `C(r', r'/2)` to `O(r')` (cap1) or `O(r'^2)` (cap2) per rung.

### Prime selection breakdown (follow-up measurement)

`RELIFT_PROFILE=prime` isolates `choosePrimeData?` (us/call, split shift
families): deg 8: 818; deg 12: 2113; deg 16: 5372; deg 20: 10414; deg 24:
18666 (roughly cubic in degree); phi15: 484; SD4: 8417. A SINGLE
`isGoodPrime` check on a deg-24 input costs 424 us — one `modP` plus one
generic `DensePoly.gcd` that should be sub-microsecond word arithmetic —
so the ~9 failing candidate primes account for ~4 ms and the Berlekamp
factorization (`fixedSpaceKernel` matrix + nullspace + the `c = 0..p-1`
constant sweep of `DensePoly.gcd f (witness - C c)`) for the remaining
~15 ms. perf attributes the time to closure dispatch (`lean_apply_1/2`
~12%), allocator traffic (~15%), box/unbox shims on `ZMod64` values, the
generic nullspace, and `Int`-extgcd fallbacks for modular inverses: the
whole path runs boxed, typeclass-generic arithmetic. `HexPolyFp/Packed.lean`
already provides the fix pattern (packed `Array UInt64` kernels with
correspondence theorems; its documented `@[csimp]` swap for
`FpPoly.modByMonic` has not landed yet). Filed as https://github.com/kim-em/hex-dev/issues/8630;
this is the largest single lever on the classical tier's fast cases and is
paid once per input by every tier.

## Win/loss geography

* **Wins (robust, ~2x end to end with same-prime + cap2):** composite cores
  with several factors, i.e. exactly where the sum of per-remainder floors
  sits far below the core floor. Linear pieces and r=1 pieces certify for
  free; the win grows with degree and factor count. `adv/high_multiplicity`
  adds the caller-B over-lift saving on top (1.6x, and 9x in lift work).
* **Losses (bounded ~1.15-1.25x):** irreducible cores (Phi15, SD3, SD4) --
  the ladder's sub-floor rungs are pure overhead ending at the same floor
  lift today performs. The overhead is the sub-floor rungs' cheap failed
  scans plus the from-scratch re-lifts, which an incremental ladder would
  mostly remove.
* **Cap-sensitive:** `adv/mignotte_swell`-type inputs, whose true factors
  span >= 2 local factors and are only recoverable near the floor. cap1
  loses 2x; cap2 recovers the sub-floor split and returns to the full-scan
  level, a 1.3x loss vs today (the exploration rungs plus the two quartic
  floor lifts slightly outweigh the saved core-floor precision). Larger
  caps buy nothing further on this corpus.
* **Wash:** a small factor times a large irreducible ((x-1)*SD3/SD4): the
  big remainder's own floor is essentially the core floor.

## Deliverable-2 assessment

What the proven same-prime implementation needs, mirroring the issue text:

* a fresh initial-partition producer keyed to a REMAINDER target at the
  same prime and a new precision (`LiftedFactorSubsetPartition remainder d'
  Finset.univ remainder` with `d'` the remainder's own `LiftData`), fed by
  re-lifting the remainder's own local factors. The concrete obligations,
  not just "transport": (i) for every factor the recombination returns --
  including the pushed-unsplit remainder -- its mod-p image equals the
  product of its tracked base factors (for accepted divisors this is the
  recovery congruence; for the final remainder it follows by dividing the
  core congruence by the peeled ones, all monic); (ii) the tracked
  sub-multiset inherits the Berlekamp-form invariants the lift needs
  (irreducible, pairwise coprime, squarefree product mod p) from the
  core's `factorsModPBerlekampForm`, which holds for any sublist; (iii)
  `multifactorLiftQuadratic` applied to the remainder and its sublist at
  the new precision yields the lifted-factor congruences the partition
  producer consumes;
* the ladder loop spec ("split found" or "floor reached with fresh
  coverage witness"), consumed by a per-remainder irreducibility lemma
  analogous to `classicalCoreFactorsWithBound_factor_irreducible_of_validBound`;
* the re-key of `factorClassicalFactorsWithBound_factor_irreducible` and its
  dispatch in `factorFactors_factor_irreducible`;
* trace-fixture churn: factor outputs are unchanged (FLINT conformance
  stays byte-identical; the spike's product and signature checks confirm
  the recursion computes the same factorizations), but the `trace` fixtures
  record per-run prime/precision/candidate counts and would be
  regenerated.

Sequencing recommendation: #8621's balanced product-tree lift is
output-preserving, needs no certification re-key, and attacks the same lift
cost that per-remainder precision reduction attacks; with it in place
today's lift share shrinks and the recursion's residual end-to-end win
(currently ~2x on split families, of which the lift is roughly half) will
compress. Land #8621 first, re-run this spike's wallclock arms against the
balanced-lift baseline, and take up deliverable 2 only if the residual win
still clears a bar worth the proof remodel. The accounting tables here are
baseline-independent (they count lift exponents, not implementation), so
only the wallclock section needs re-measuring.


## Landed implementation (deliverable 2)

The production form landed on the `issue-8625-d2` branch: the classical
tier (`factorClassicalFactorsWithBound` and the traced variant) now runs
`classicalCoreFactorsRecursive` — the same-prime sub-floor escalation
ladder with a greedy capped peel (`reliftSubFloorCap = 2`), tracked
per-piece seed factors undilated through the monic-transform peel
identity, self-verifying per-piece prime data (`piecePrimeData?`), and a
floor fallback to the full size-ordered scan at each node's own Mignotte
floor. Certification is keyed to the semantic `ModPFactorization` bundle
(see `HexBerlekampZassenhausMathlib/ModPFactorization.lean` and
`Relift.lean`): the fresh per-remainder partition producer transports
irreducibility along the unit undilation and derives coprimality from
squarefreeness of the piece's image, and the per-factor irreducibility
induction closes over the bundle with no reference to the prime-selection
walk. Free certificates: degree-1 pieces and single-mod-p-factor pieces.

Measured at landing (spike `prod-rec` arm, identical outputs to the
prototype): 1.23-1.29x wallclock wins on the split and high-multiplicity
families, 1.19-1.58x bounded losses on the small irreducible/SD inputs.
The shared additive costs (prime selection ~13.7 ms and Mignotte bound
computation ~2 x 6.9 ms at deg 24) dominate both arms; net of them the
recursion's algorithmic core is ~3.7x cheaper than the floor scan, so the
end-to-end ratio improves further when
https://github.com/kim-em/hex-dev/issues/8677 (closed-form
`defaultFactorCoeffBound`) lands.

The classical trace no longer reports scan candidate counts
(`subsetCandidates = 0`); the recombination-blow-up tripwire moves to the
wallclock bench gate. The trace fixtures and `bz-trace-baseline.json`
were regenerated; factor multisets are unchanged (order differs — peel
order instead of scan order).

## Reproduction

`lake build hex_recursive_relift_spike && .lake/build/bin/hex_recursive_relift_spike`
prints the accounting and wallclock sections; `RELIFT_PROFILE=phases` (or
`today|recursive|sameprime`) runs the focused deg-24 profile arms used in
"Where the recursion's time actually goes".
