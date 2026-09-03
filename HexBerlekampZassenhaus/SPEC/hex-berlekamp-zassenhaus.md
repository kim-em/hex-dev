# hex-berlekamp-zassenhaus

`hex-berlekamp-zassenhaus` factors dense univariate polynomials over
the integers. It depends on finite-field Berlekamp factorization,
Hensel lifting, LLL reduction, and HexPrimality's certified prime table,
whose ordered windows supply the deterministic modular-prime candidates.
The executable library has no Mathlib dependency.

## Public API

```lean
def factorClassical (f : ZPoly) : Option Factorization
def factorLattice   (f : ZPoly) : Option Factorization
def factorTrial     (f : ZPoly) : Factorization
def ZPoly.factorize (f : ZPoly) : Factorization
def ZPoly.factors   (f : ZPoly) : Array (ZPoly × Nat)
```

`factorClassical` performs bounded subset recombination.
`factorLattice` performs proved logarithmic-derivative lattice
recombination. `factorTrial` performs exhaustive integer trial
division. `ZPoly.factorize` is total: on a large modular support it
may first use a small logarithmic-derivative lattice to propose a
partition, verify the partition exactly, and run `factorClassical`
again on every proposed piece. A proposal is never evidence of
irreducibility. If proposal replay or either ordinary fast method
declines, the selector eventually uses trial division.

`factorTraced` returns the same factorization together with a
`DirectFactorTrace`. The trace records the `FactorMethod`, a possible
typed classical decline, and classical-search measurements.

## Factorization result

```lean
structure Factorization where
  scalar  : Int
  factors : Array (ZPoly × Nat)
```

`Factorization.product` multiplies the scalar and the recorded
polynomial powers. For a nonzero input, the normalized result has:

- signed content as its scalar;
- primitive irreducible polynomial factors;
- positive leading coefficients and positive multiplicities;
- no two associated factor entries;
- product equal to the input.

The zero result is `⟨0, #[]⟩`. Units and nonzero constants have no
polynomial factors. Integer content is not split into constant prime
polynomials. A power of `X` is stored as one factor with its
multiplicity.

## Fast-arithmetic adoption

The implementation audit required by
[hex-poly-fast](../../SPEC/Libraries/hex-poly-fast.md) covers modular-image
products, Hensel product trees, subset trial products, exact quotient checks,
and final integer reassembly. Integer multiplication uses `ZPoly.mulFast` only
where its schoolbook/KS1/KS2/KS3/KS4/CRT-NTT dispatcher improves the complete
factorization cell; finite-field stages use the corresponding `FpPoly` plan.

No fast result is treated as certificate evidence. The existing product,
divisibility, and irreducibility checks replay against unchanged schoolbook
semantics, and every decline/fallback remains available. Benchmarks separate
classical and lattice recombination, balanced and skewed degree patterns, and
small/large coefficient regimes so a win in reassembly cannot hide a loss in
prime selection or lifting.

Every subset check and final product already uses the shared
`Array.polyProduct` surface.  A BZ-shaped screen found that the Hensel
product-tree count interval cannot be applied to arbitrary factors.  One warm
discovery trial on `chungus2` (AMD EPYC 9455), Lean `4.34.0-rc2`, measured:

| family | factors | retained fold | forced tree |
|---|---:|---:|---:|
| degree-4, 64-bit lifted | 32 | 1.902 ms | 5.282 ms |
| degree-4, 64-bit lifted | 128 | 62.041 ms | 506.904 ms |
| degree-32, 128-bit reassembly | 32 | 116.793 ms | 642.608 ms |
| skewed degree-256 plus linear | 64 | 7.671 ms | 5.162 ms |
| skewed degree-256 plus linear | 128 | 21.470 ms | 387.616 ms |

The skewed reversal makes a factor-count-only adoption unsafe.  The compiled
dispatcher therefore restricts the tree to the measured small-linear Hensel
domain and retains the fold for all three BZ families.  Three warm outer
trials after applying that guard give these medians; all hashes agree:

| family | factors | retained fold | selected dispatcher |
|---|---:|---:|---:|
| degree-4, 64-bit lifted | 128 | 55.729 ms | 55.870 ms |
| degree-4, 64-bit lifted | 512 | 2.444 s | 2.458 s |
| degree-32, 128-bit reassembly | 128 | 5.740 s | 5.758 s |
| skewed degree-256 plus linear | 128 | 21.229 ms | 21.430 ms |
| skewed degree-256 plus linear | 512 | 331.144 ms | 331.700 ms |

Regenerate the final comparisons with `lake exe hexbz_bench compare
Hex.BerlekampZassenhausBench.runTrialProductSchoolbookChecksum
Hex.BerlekampZassenhausBench.runTrialProductChecksum --outer-trials 3` and the
analogous `runReassemblyProduct*` and `runSkewProduct*` pairs.  The benchmark
registrations carry their complete shared schedules.  `Array.polyProduct`
remains specified as the ordered fold, and its `@[csimp]` theorem proves that
the guarded compiled branch cannot alter BZ factor ordering or products.

## Normalization

Every factorization method uses the same normalization:

1. extract the signed content;
2. remove the maximal power of `X`;
3. compute the primitive square-free part and its multiplicity data;
4. factor the square-free part;
5. restore the powers of `X`, repeated factors, and scalar.

`SquareFreeInput` indexes data that belongs to the normalized
primitive square-free polynomial. Reassembly is shared, so the three
factorization methods cannot disagree about output conventions.

## Direct integer coordinates

Let `f` be primitive and square-free with leading coefficient `a`.
At a suitable prime `p`, the finite-field target is

```text
monicModularImage (f mod p) = a⁻¹ · (f mod p).
```

This is multiplication by a unit in `𝔽_p`; it does not substitute the
variable. `ZPoly.monicTarget f p k` is the canonical integer lift of
that modular image at precision `p^k`.

The lifted factors are monic. To return to the coordinates of `f`,
recombination scales a selected lifted product by `a`, takes centred
coefficient representatives, extracts the primitive part, and
normalizes its sign.

Classical and lattice recombination use the same modular
factorization, factor indexing, and direct-coordinate Hensel lift.
There is no dilation-coordinate factorization method.

## Prime selection

`DirectPrimeProbe` stores one successful modular factorization:

- the prime and its arithmetic bounds;
- the monic modular image and its irreducible factors;
- the modular factor degrees;
- a bitset of subset-reachable degrees.

`DirectPrimePlan` stores the chosen factorization and the other
successful factorization examined, if any. The first admissible prime is
split. Further admissible primes are *scouted* while `scoutPays` says
the walk can still afford another observation; plans are compared by:

1. predicted complete subset-search work;
2. number of reachable proper factor degrees;
3. required Hensel precision;
4. the prime, as a deterministic tie breaker.

Every key of that score is a function of the prime and the multiset of
modular factor degrees, so a scouted degree pattern scores exactly as
the factorization it predicts would. Only the winner is split.

Inadmissible primes do not spend the allowance of scouts. The walk
therefore ends holding the plan a policy that split every candidate
would have selected, having split the first admissible prime and at
most the winner — except where `scoutPays` ends the walk, which it may
do at the first admissible prime and after any scouted candidate wins.

The reachability bitset is computed by dynamic programming in
`O(number of factors × degree)`.

### Pricing one more observation

`scoutPays` is the walk's only stopping decision. It compares the
recombination work the plan in hand may still have to do against the
scouts and split the rest of the walk may spend. Both sides are
estimates over shape already observed — the input degree, the primes
involved, and the degree patterns of the plans in hand — so the walk
prices its own next step and nothing about the corpus or the instance's
provenance enters.

Writing `n` for the modular degree, `q` for the prime about to be
scouted, `w` and `d` for the width and largest modular factor degree of
the plan held, and `W` for the machine words of that plan's Hensel
modulus:

- a recombination candidate costs about `n²` coefficient operations on
  `W`-word integers, averaged over the cheap degree and
  trailing-coefficient rejections and the subsets that reach a product.
  A complete head-forced search visits `directSubsetCost w` of them, but
  the direct engine abandons the search at `defaultSubsetBudget`, so the
  work still ahead is at most
  `min (directSubsetCost w) defaultSubsetBudget · n² · W`;
- a bounded scout runs one Frobenius power and one gcd per separated
  degree, about `bitLen q` squarings of the degree-`n` image apiece, and
  stops at the largest factor degree of the image it separates. That
  degree is unknown before scouting, so `d` stands in for it — a proxy,
  not a bound: a narrower candidate tends to have larger factor degrees;
- acting on what a scout learns costs one further Berlekamp split, whose
  matrix and row reduction are about `bitLen q · n³`;
- so a walk with `fuel` observations left may spend at most `fuel`
  scouts and one split.

Both estimates carry a factor `n²`, which cancels. What remains decides
**affordability, not expected value**: the left side is the most any
prime could save and the right side the most the remaining walk could
spend, so passing means the walk *could* pay for itself, not that it
will. That is weaker than a value-of-information rule and is the reason
the walk can still buy an observation that turns out worthless.

The two constants scale a modular word operation against a recombination
candidate, which the inequality counts as one. They are measured ratios,
they are not precise, and changing them changes decisions;
`scripts/bench/prime_policy_replay.py --sensitivity` reports over what
range the whole replayed walk is unchanged and what the exceptions cost.

`scoutFuel` remains, as a bound that makes the walk terminate in a fixed
number of observations however cheap the next one looks; which of those
observations happen is `scoutPays`'s decision, not the bound's.

## Direct Hensel lift

`ZPoly.directLiftData` lifts `ZPoly.monicTarget` to the precision
chosen by `precisionForCoeffBound`. `DirectLiftFacts` states:

- monicity of the target and all lifted factors;
- the multifactor Hensel invariant;
- reduction of each lifted factor to its modular ancestor;
- preservation of factor count;
- compatibility of every selected-factor product with modular
  reduction.

The ordinary recovery precision satisfies `2 B < p^k`, where `B` is
the coefficient bound. The public value is proved from Mignotte's
bound in the Mathlib companion.

## Classical recombination

The classical method chooses one distinguished lifted factor and
enumerates subsets of the remaining factors in increasing
cardinality. It maintains the selected degree and a cheap trailing
coefficient test before constructing a full candidate. A surviving
candidate is accepted only when exact bounded division succeeds.

Between constructing a candidate and dividing by it, the search
applies a finite-field divisibility obstruction. Reduction modulo a
fixed word-sized prime `q` is a ring homomorphism `ℤ[X] → 𝔽_q[X]`, so
a divisor of the target reduces to a divisor of the reduced target and
`𝔽_q[X]` division leaves no remainder; a nonzero remainder therefore
proves the candidate does not divide. The obstruction is one-sided:
it can reject, never accept, and a zero remainder falls through to the
same exact integer division as before. There is no separate
inconclusive branch, because a reduced divisor that is zero or that
has lost its leading coefficient is covered by the same law. This is
a necessary condition on the *constructed* candidate, not on its
support: the candidate is the centred lift modulo `p^k` of the scaled
selected product, and centred lifting does not commute with reduction
modulo `q`, so the candidate's image is not a function of the lifted
factors' images.

The budget is measured in complete subset-cardinality levels. If the
next level does not fit, the method declines before testing any member
of that level. An incomplete search is never used as evidence of
irreducibility.

The total selector routes eligible large, dense, already-normalized
inputs to a proposal stage before this unrestricted classical search.
It streams every unforced subset of cardinality one through three,
using degree and trailing-coefficient filters before constructing a
candidate. After the first exact split, it reuses the same Hensel lift
and complementary lifted-factor indices to search support sizes one
and two again on the exact quotient. This continues until the cheap
search is exhausted, the residual is one, or the shared candidate
budget cannot admit another complete level. After an exact peel, the
retained factors, residual, and residual support pass directly to the
proposal lattice. With no exact progress, the selector skips that
speculative lattice and proceeds to the full CLD fallback. Exhausting
these configured cardinalities is distinct from exhausting the
candidate budget.

`DirectSupportPartition` associates each irreducible integer factor
with its unique modular support. The minimal-head proof shows that the
first accepted subset containing the distinguished factor is exactly
its irreducible support. Removing that support and recursing on the
exact quotient yields a complete irreducible factorization.

The mathematical modules are:

```text
Classical/Recovery.lean
Classical/SupportPartition.lean
Classical/CombinationIterator.lean
Classical/SearchCompleteness.lean
Classical/Factorization.lean
```

## Logarithmic-derivative lattice recombination

For a lifted factor `g`, its combined logarithmic derivative (CLD) is

```text
Φ(g) = f · g' / g mod p^k.
```

Since `Φ(gh) = Φ(g) + Φ(h)`, the CLD coefficient vectors convert
products of local factors into sums. They form the coefficient block
of the Belabas-Hoeij-Klüners-Steel (BHKS) recombination lattice.

After exact LLL reduction, rows below the Gram-Schmidt cut are
projected to their first coordinates. Those coordinates describe
integer combinations of zero-one factor-support indicators.

The proof has two parts:

1. at the coefficient-recovery precision, every genuine support
   indicator belongs to the projected row span;
2. at the resultant precision, every retained projected row is
   constant on each genuine support.

The spans are therefore equal. Equal projected columns belong to the
same irreducible support, so their equivalence classes recover the
integer factors.

The executable calculation increases Hensel precision
quadratically. A nonsingleton support partition returns the recovered
factors. A single all-ones class proves irreducibility only after the
proved precision threshold has been reached.

The proof is organized around:

```text
Lattice/ProjectedRows.lean
Lattice/CutProjection.lean
Lattice/SupportEquivalence.lean
Lattice/DirectSupport.lean
Lattice/DirectRecovery.lean
Lattice/DirectAdequacy.lean
LatticeFactorization.lean
LatticeTotality.lean
```

Lattice totality is conditional on successful direct prime selection.

## Selected-coordinate proposals

For an eligible large support where low-cardinality peeling makes exact
progress, `ZPoly.factorize` next tries a cheaper, untrusted use of the
same CLD data. It prepares the leading sixteen coefficient columns
once, then reduces nested lattices using prefixes of four, eight,
twelve, and sixteen columns. Equal projected columns propose groups of
lifted factors.

Acceptance has a deliberately narrow boundary:

1. reconstruct every proposed piece in the original integer
   coordinates;
2. check exact product reconstruction;
3. run the unrestricted, proved classical factorizer on every piece;
4. concatenate its results and check the final public product.

Thus LLL reduction and partition extraction are heuristics here. The
final product theorem follows from the exact checks, and the final
irreducibility theorem follows only from the ordinary classical
factorization theorem. If no CLD partition is found after a genuine
peel, the peeled factors and exact residual form a useful proposal of
their own. If no peel exists, the selector does not build a
speculative lattice or replay the unchanged input and proceeds to the
proved full lattice method.

## Trial division

`factorTrial` enumerates integer candidates up to the proved
coefficient bound and tests exact division. It does not require a
suitable modular prime and is therefore the unconditional final
method.

## Iterated quadratic norms

`quadNorm d g` is the norm of `g(X - t)` along `ℤ[t]/(t² - d) → ℤ`, that
is `g(X - √d) · g(X + √d)`. It carries the coefficient pair of
`g(X - t)` through one synthetic Taylor shift with shift constant `-t`,
then materializes only the rational part `p² - d q²` of the product with
the conjugate, whose `t` component cancels coefficientwise.
`iteratedNorm c ds` folds those norms over the radicands from `X - c`,
giving `F(c; d₁, …, dₙ) = ∏_ε (X - c - ∑ᵢ εᵢ √dᵢ)` over the `2ⁿ` sign
patterns.

A `QuadraticNormCertificate` is a translation and a list of radicands.
Its `check` verifies two decidable conditions: that no nonempty
subproduct of the radicands is a perfect square, which is
`independentSquareClasses` and is exactly multiplicative independence in
`ℚ*/(ℚ*)²`; and that the input equals `F(c; d)` coefficientwise up to
the unit `-1`. Both are integer arithmetic, with no factorization of the
radicands and no number field constructed.

`QuadraticNormCertificate.recover?` proposes the pair from the top
`2n + 1` coefficients by exact rational arithmetic, and `certify?` is
recovery followed by the check. Recovery is untrusted: a wrong proposal
is refused by `check`, so the trust surface stays `quadNorm`,
`iteratedNorm`, `isPerfectSquare`, `independentSquareClasses`, and one
array comparison.

`quadraticNormCertified core width` is the production gate. `width` is
the number of modular factors, so it is known exactly when
`classicalInput` has its prime plan and before any Hensel lift. Below
`QuadraticNormCertificate.widthFloor` the gate is `false` with nothing
constructed; at or above it, recombination would walk up to `2^(w-1)`
supports, which is the cost the certificate is worth attempting to
replace. A success returns the square-free core as a single factor
through the same `reassemblePolynomialFactors` as the constant and
quadratic cases, so it is the ordinary singleton-irreducibility answer
and not a second entry point; the trace records `FactorMethod`
`quadraticNorm`. A failure falls through to `planned` carrying no state.

Every `F(c; d)` is monic, so the certificate applies exactly when the
primitive part has leading coefficient `±1`; `normalizePrimitiveSign`
inside the check is the whole normalization. There is no scaling and no
content division.

The field theory that turns a successful check into irreducibility is
the multiquadratic tower theorem, in `hex-berlekamp-zassenhaus-mathlib`.

## Correctness

The Mathlib-free library proves executable product reconstruction,
exact quotient identities, normalization identities, and the
correctness of the bounded iterators. It also proves the finite-field
obstruction never rejects a genuine divisor, and that a leaf which
skips an obstructed candidate's exact division returns what the
unfiltered leaf returned.

`hex-berlekamp-zassenhaus-mathlib` proves:

- semantic validity of the selected modular factorization;
- direct-coordinate Hensel correspondence and recovery;
- existence, disjointness, and uniqueness of supports;
- completeness of classical recombination;
- both inclusions in the lattice support-span equality;
- irreducibility and normalization of every recorded factor;
- uniqueness of the final factorization;
- the quadratic-norm correspondence: `quadNorm` maps to
  `g(X - r) · g(X + r)` over any commutative ring with `r² = d`, the
  iterate maps to the sign-pattern product, and
  `independentSquareClasses` decides independence of the square
  classes;
- soundness of the certificate: a successful `check` makes its input
  irreducible in `Polynomial ℤ`, and so does a `true` from
  `quadraticNormCertified`.

The ordinary umbrella exposes the supported factorization and tactic
surface. `HexBerlekampZassenhaus.All` and
`HexBerlekampZassenhausMathlib.All` expose the complete development
module collections.

## Verification and performance

Changes must pass:

- the root build and trust-surface check;
- modular, lifting, recombination, and factorization conformance
  fixtures;
- external FLINT, PARI/GP, NTL, and verified Isabelle comparisons;
- factor-tactic regression modules;
- benchmark verification and the complete polynomial-factorization
  corpus.

The current performance report presents only the public
`ZPoly.factorize` service. It states the exact source revision,
toolchain, corpus hash, host, CPU placement, repetitions, warmup,
timeout, and comparator revisions. Timeout rows and the long tail
remain visible. Unchanged external observations are retained when
their host, inputs, and protocol are unchanged.
