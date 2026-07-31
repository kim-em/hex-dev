# hex-berlekamp-zassenhaus

Complete factorization of univariate polynomials over `ℤ`.

This library depends on `hex-berlekamp`, `hex-hensel`, and `hex-lll`.  The
executable library is Mathlib-free; correspondence, completeness, and
irreducibility proofs live in `HexBerlekampZassenhausMathlib`.

## Public API

```lean
def factorClassical (f : ZPoly) : Option Factorization
def factorLattice   (f : ZPoly) : Option Factorization
def factorTrial     (f : ZPoly) : Factorization
def ZPoly.factorize (f : ZPoly) : Factorization
def ZPoly.factors   (f : ZPoly) : Array (ZPoly × Nat)
```

`factorClassical` and `factorLattice` are partial modular algorithms.
`factorTrial` is the unconditional exhaustive backstop.  `ZPoly.factorize`
uses the classical engine first, the CLD lattice engine after a typed
classical decline, and trial factorization if modular prime planning or CLD
declines.

All entry points use the same normalization and reassembly:

1. extract the signed content;
2. remove the maximal power of `X`;
3. compute the primitive square-free core and its multiplicity data;
4. factor the core;
5. restore powers of `X`, repeated-factor multiplicities, and the signed
   scalar.

There is no separate scaled-coordinate classical engine and no refinement of
direct factors through a second factorization route.

## Factorization result

```lean
structure Factorization where
  scalar  : Int
  factors : Array (ZPoly × Nat)
deriving DecidableEq

def Factorization.product (φ : Factorization) : ZPoly := ...
```

For nonzero `f`, `factorize f` returns a factorization satisfying:

- `scalar` is the signed content of `f`;
- every recorded polynomial factor is primitive, irreducible, and has
  positive leading coefficient;
- every multiplicity is positive;
- distinct entries are not associates;
- `Factorization.product (factorize f) = f`.

Integer content is not split into prime constant polynomials.  For example,
`factorize 6 = ⟨6, #[]⟩`.

The zero result is `⟨0, #[]⟩`.  Units and nonzero constants have an empty
polynomial-factor array.  Powers of `X` are represented by the factor `X`
with the corresponding multiplicity.

## Coordinate model

The production modular and Hensel pipeline is in the original integer
coordinates.

For a primitive square-free core `f` with leading coefficient `a` and a good
prime `p`, the finite-field factorization target is

```text
monicModularImage (f mod p) = a⁻¹ · (f mod p).
```

Finite-field irreducible factors are monic by convention.  This normalization
does not change the integer coordinate or substitute the variable: it is only
multiplication by the unit `a⁻¹` in `𝔽_p`.  In particular, it is distinct from
the coefficient-swelling integral transform
`a^(deg f - 1) · f(X / a)`.

The Hensel target is `ZPoly.monicTarget f p k`, the canonical integer lift of
that direct modular image.  Recombination restores the original leading
coefficient through `scaledLiftedFactorProduct`; centered lifting,
primitive-part extraction, and sign normalization then recover factors of the
original core.

Classical and CLD recombination use the same direct modular factorization and
factor indexing. Each constructs its own direct Hensel lift at the precision
required by its recovery bound.

## Typed data

The main executable records tie data to the polynomial it describes.

```lean
structure SquareFreeInput where
  poly : ZPoly

structure DirectPrimeProbe (core : SquareFreeInput) where
  candidate        : SmallPrimeCandidate
  data             : PrimeChoiceData
  factorDegrees    : Array Nat
  reachableDegrees : Array Bool

structure DirectPrimePlan (core : SquareFreeInput) where
  selected    : DirectPrimeProbe core
  otherProbes : Array (DirectPrimeProbe core)

structure DirectLiftPlan
    (core : SquareFreeInput) (modular : DirectPrimePlan core) where
  ...

inductive ClassicalOutcome where
  | factored (factors : Array ZPoly) (stats : ClassicalStats)
  | declined (reason : DeclineReason) (stats : ClassicalStats)
```

A plan retains every successful modular probe it performs.  Selection can
therefore refer only to a cached factorization.  A lift plan carries a positive
validated recovery precision; `B = 0` has no implicit semantic meaning.

Declines are typed.  Trace information is returned from the same execution as
the factors, so traced and untraced entry points cannot follow different
dispatch trees.

## Prime planning

`directPrimePlan?` checks the fixed small-prime candidates against the original
core.  A successful probe records:

- the good prime and its bounds instance;
- the factorization of the direct monic modular image;
- modular factor degrees;
- a subset-degree reachability bitset.

If the first successful probe has at most `directProbeWidth` factors, it is
used immediately.  Otherwise the planner considers at most
`directProbeFuel` further successful probes and chooses lexicographically by:

1. complete head-forced subset-search cost;
2. number of reachable proper subset degrees;
3. direct Hensel precision;
4. prime, as a stable tie breaker.

Bad primes do not consume the successful-probe allowance.  A singleton modular
factorization stops planning immediately.

The degree reachability table is computed by dynamic programming in
`O(number of factors × degree)`.  No recursive exponential subset-degree
certificate or factor-width cutoff is used.

## Direct Hensel lift

`coreLiftData` lifts the direct target at
`precisionForCoeffBound B p`.  `DirectLiftFacts` packages:

- the semantic modular factorization;
- monicity, irreducibility, distinctness, and pairwise coprimality of the
  modular factors;
- equality of the direct target with their product modulo `p`;
- the multifactor Hensel invariant;
- factor-count preservation;
- the precision and leading-coefficient coprimality facts required for exact
  recovery.

The ordinary recovery precision satisfies

```text
2 · B < p^k.
```

The public core uses `defaultFactorCoeffBound`, whose Mathlib proof is in
`FactorBound.lean`.

## Classical recombination

The sole classical engine is `factorDirectCore`.

At each recursive step it:

1. chooses the distinguished head lifted factor;
2. enumerates subsets of the remaining factors in increasing cardinality;
3. carries the selected degree and trailing residue through the subset tree,
   rejecting a support unless its raw trailing coefficient divides
   `leadingCoeff(core) · target(0)`;
4. constructs the original-coordinate candidate;
5. tests an exact bounded quotient;
6. removes the accepted support and continues on the exact quotient.

The iterator is streaming and reports completed cardinality levels.  A resource
limit may stop only with a typed decline; incomplete search is never used as an
irreducibility certificate.

`DirectSupportPartition` identifies irreducible integer factors with unique
subsets of the selected modular factor indices.  The minimal-head theorem says
that the first accepted head-containing subset is exactly the support of the
irreducible factor containing that head.  Consequently:

- every accepted candidate is already irreducible;
- no per-piece prime selection or Hensel lift is performed;
- completed exhaustive failure to find a proper split proves the current
  target irreducible;
- recursive complement removal yields a complete irreducible factorization.

The Mathlib proof is organized as:

```text
Classical/Recovery.lean
Classical/SupportPartition.lean
Classical/CombinationIterator.lean
Classical/SearchCompleteness.lean
Classical/Correctness.lean
```

## CLD lattice recombination

The lattice tier consumes the same `DirectPrimePlan`, `DirectLiftFacts`, and
`DirectSupportPartition` as the classical engine.

`DirectAdequacy` is the proof context shared by the forward and exact CLD
arguments.  It contains:

- validated recovery precision and leading-coefficient coprimality;
- the direct Hensel lift facts;
- cover and disjointness of irreducible supports;
- local factor recovery and factor-count facts;
- short-vector data for every true support.

The BHKS/van-Hoeij lattice uses CLD columns

```text
Φ(g) = f · g' / g
```

and projected LLL rows.  At the column-adequacy floor, every true direct support
indicator lies in the retained projected row span (`W ⊆ L'`).  At the
resultant precision bound, every retained vector is constant on true supports,
which gives exact equality of the projected span with the support span.

The executable loop increases Hensel precision through a quadratic schedule.
A non-single partition yields recovered direct factors.  A single all-ones
partition is accepted as irreducible only at an adequate precision.  At the
public cap, exact span makes either result conclusive.

The proof modules are:

```text
Lattice/DirectSupport.lean
Lattice/DirectRecovery.lean
Lattice/DirectAdequacy.lean
LatticeTier.lean
LatticeTotality.lean
```

`factorLatticeFactorsWithBound_ne_none_of_directPrimePlan` and
`factorLattice_ne_none_of_directPrimePlan` prove public-cap totality
conditional on successful direct prime planning.

## Trial backstop

`factorTrial` performs exhaustive integer trial division at the proved
coefficient bound.  It does not depend on modular prime selection and is total.
This makes the default dispatcher total even for inputs for which the finite
prime planner finds no admissible prime.

## Correctness boundary

The Mathlib-free layer proves executable identities such as product
reconstruction and exact quotient results.  The Mathlib bridge proves:

- semantic validity of modular factorizations;
- direct Hensel correspondence and recovery;
- unique support partitions;
- classical minimal-head completeness;
- CLD forward inclusion and exact span;
- irreducibility of every recorded factor;
- normalization, multiplicity, and uniqueness of the final factorization.

The bridge contains no axioms, `native_decide`, or unproved placeholders.

General mathematical objects are separated into correspondingly named modules:

- `FactorBound.lean`;
- `Factorization.lean`;
- `ModularPolynomial.lean`;
- `IrreducibilityCertificate.lean`;
- `ModPPartition.lean`.

## Validation

Changes to this library must run:

- `lake build`;
- the Mathlib-free benchmark import lint;
- the benchmark verification check;
- Berlekamp-Zassenhaus conformance and oracle checks;
- the polynomial-factorization corpus comparison;
- focused public `factor` performance measurements for affected rows.

Stored cross-system benchmark results are immutable observations of the
recorded tool revisions.  A Hex implementation change reruns the public Hex
service only and records the exact commit, host, command, and timeout policy.
