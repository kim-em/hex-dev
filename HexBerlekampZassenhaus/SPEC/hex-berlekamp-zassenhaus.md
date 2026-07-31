# hex-berlekamp-zassenhaus

`hex-berlekamp-zassenhaus` factors dense univariate polynomials over
the integers. It depends on finite-field Berlekamp factorization,
Hensel lifting, and LLL reduction. The executable library has no
Mathlib dependency.

## Public API

```lean
def factorClassical (f : ZPoly) : Option Factorization
def factorLattice   (f : ZPoly) : Option Factorization
def factorTrial     (f : ZPoly) : Factorization
def ZPoly.factorize (f : ZPoly) : Factorization
def ZPoly.factors   (f : ZPoly) : Array (ZPoly × Nat)
```

`factorClassical` performs bounded subset recombination.
`factorLattice` performs logarithmic-derivative lattice
recombination. `factorTrial` performs exhaustive integer trial
division. `ZPoly.factorize` is total: it uses the first two methods
when they return a verified answer and otherwise uses trial division.

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
successful factorizations examined. If the first admissible prime has
few modular factors, it is used immediately. Otherwise a bounded
number of further admissible primes are compared by:

1. predicted complete subset-search work;
2. number of reachable proper factor degrees;
3. required Hensel precision;
4. the prime, as a deterministic tie breaker.

Inadmissible primes do not spend the allowance of successful
factorizations. A singleton modular factorization is selected
immediately.

The reachability bitset is computed by dynamic programming in
`O(number of factors × degree)`.

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

The budget is measured in complete subset-cardinality levels. If the
next level does not fit, the method declines before testing any member
of that level. An incomplete search is never used as evidence of
irreducibility.

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

## Trial division

`factorTrial` enumerates integer candidates up to the proved
coefficient bound and tests exact division. It does not require a
suitable modular prime and is therefore the unconditional final
method.

## Correctness

The Mathlib-free library proves executable product reconstruction,
exact quotient identities, normalization identities, and the
correctness of the bounded iterators.

`hex-berlekamp-zassenhaus-mathlib` proves:

- semantic validity of the selected modular factorization;
- direct-coordinate Hensel correspondence and recovery;
- existence, disjointness, and uniqueness of supports;
- completeness of classical recombination;
- both inclusions in the lattice support-span equality;
- irreducibility and normalization of every recorded factor;
- uniqueness of the final factorization.

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
