# hex-berlekamp-zassenhaus-mathlib

`hex-berlekamp-zassenhaus-mathlib` proves the mathematical
correctness of executable integer polynomial factorization. It
depends on `hex-berlekamp-zassenhaus`, `hex-poly-z-mathlib`,
`hex-hensel-mathlib`, and `hex-lll-mathlib`.

The ordinary umbrella exposes factorization soundness, the
correspondence with `Polynomial ℤ`, and the factor tactics.
`HexBerlekampZassenhausMathlib.All` exposes the complete proof
development.

## Polynomial correspondence

`HexPolyZMathlib.toPolynomial` identifies a dense `Hex.ZPoly` with a
Mathlib polynomial over the integers. It preserves coefficients,
addition, multiplication, degree, content, primitive parts, and
divisibility.

The public irreducibility equivalences are:

```lean
theorem Hex.ZPoly.Irreducible_iff_polynomialIrreducible (f : Hex.ZPoly) :
  Hex.ZPoly.Irreducible f ↔
    Irreducible (HexPolyZMathlib.toPolynomial f)

theorem Hex.ZPoly.isIrreducible_iff (f : Hex.ZPoly) :
  Hex.ZPoly.isIrreducible f = true ↔ Hex.ZPoly.Irreducible f
```

The second theorem supplies the decidable instance for concrete
dense integer polynomials.

## Modular factorization

`ModPFactorization f data` is the semantic contract for selected
prime data. It records:

- primality and admissibility of the modulus;
- equality of the cached polynomial with the reduction of `f`;
- monicity, distinctness, coprimality, irreducibility, and positive
  degree of the modular factors;
- equality of their product with the monic modular image.

`DirectPrimeFacts` combines this contract with the Berlekamp
certificate form and the small-prime bound used in the resultant
estimate.

## Hensel correspondence

`DirectLiftFacts` interprets the executable direct-coordinate Hensel
lift. The proof identifies lifted-factor indices with modular-factor
indices and transports selected products through reduction.

An irreducible integer divisor has a unique modular support.
`DirectSupportPartition` strengthens this statement to the recursive
factorization state: the remaining supports cover the remaining
indices, nonassociated factors have disjoint supports, and associated
factors have the same support.

`DirectFactorCertificate` packages one normalized irreducible factor,
its cofactor, its modular support, and the scaled congruence needed by
the logarithmic-derivative proof.

## Classical completeness

The classical proof follows the executable head-forced subset
iterator. It establishes:

- correctness of every accepted exact division;
- completeness of each fully enumerated cardinality level;
- identification of the first accepted subset with the irreducible
  support containing the distinguished index;
- preservation of the support partition after removing a factor;
- complete irreducibility of a successful returned factor list.

A typed resource decline makes no mathematical claim.

## Lattice completeness

For each local factor `g`, the combined logarithmic derivative (CLD)
is `f g' / g` modulo the Hensel modulus. Additivity turns products of
local factors into sums of CLD coefficient vectors.

The Belabas-Hoeij-Klüners-Steel (BHKS) lattice appends scaled CLD
coefficients to factor-indicator coordinates. Its exact LLL reduction
is cut by Gram-Schmidt length and projected back to the indicator
coordinates.

`SupportShortVectorData` describes a short lattice vector whose first
coordinates are a genuine support indicator.
`CutProjectionHypotheses` states that every genuine indicator lies in
the projected span. The resultant argument proves the reverse
containment: every retained projected row is constant on genuine
supports.

`DirectAdequacy` collects the precision, coefficient recovery,
leading-coefficient invertibility, Hensel lift, and support partition
needed by both arguments. `LatticeTotality` proves that the public
precision returns either recovered factors or a conclusive
irreducibility result whenever direct prime selection succeeds.

## Final factorization theorems

For every dense integer polynomial:

```lean
theorem factorize_product (f : Hex.ZPoly) :
  Hex.Factorization.product (Hex.ZPoly.factorize f) = f
```

For a nonzero input, `factorize_normalized` states that:

- the scalar is the signed content;
- each polynomial factor is primitive and irreducible;
- every leading coefficient and multiplicity is positive;
- distinct entries are not associates;
- the recorded product is the input.

`factorize_unique` shows that two normalized factorizations of the
same input have the same scalar and the same factors with
multiplicities.

The headline product, irreducibility, normalization, uniqueness, and
lattice-totality theorems use only the accepted Lean and Mathlib
foundations reported by the trust-surface check.

## Factor tactics

The `Polynomial ℤ` tactic support parses a closed polynomial
expression to a dense polynomial while proving the conversion
equality. Compiled factorization searches for:

- small-prime irreducibility witnesses;
- multi-prime degree-obstruction certificates;
- factor covers with one certificate per distinct factor.

The emitted term contains reified data, coefficientwise product
checks, certificate checks, and conversion theorems. The compiled
factorizer itself is not in the emitted proof.

The stronger `irreducibility!` and `factor_poly!` forms may use kernel
evaluation of the decidable factorization theorem on small inputs.
They require all executable definitions to be visible and cannot
evaluate native LLL code.

## Verification

Changes must pass:

- the root build and trust-surface check;
- the advertised root-name compile checks;
- `#print axioms` checks for the headline theorems;
- factor-tactic regression modules;
- the integer-factorization conformance and external comparisons;
- the release manifest and dependency checks.
