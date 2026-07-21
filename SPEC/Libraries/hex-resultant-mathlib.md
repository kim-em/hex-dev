# hex-resultant-mathlib (depends on hex-resultant + hex-poly-mathlib + Mathlib)

Mathlib companion for `hex-resultant`. It proves both the chain-level facts used
for early number-field soundness and the full agreement of the executable
subresultant algorithm with `Polynomial.resultant`.

The full agreement is required. Resultant vanishing proves that a proposed
algebraic value is a root of an eliminant, but tower norms, root-product bounds,
specialization, and Trager factorization also depend on the value of the
resultant, including its units, powers, and signs.

## Public theorems

The exact typeclass assumptions follow the executable algorithm: `R` is a
commutative integral domain with decidable equality and the exact-division laws
used by the subresultant recurrence.

```lean
namespace Hex.DensePoly

/-- The executable and Mathlib resultants agree under the dense-polynomial
    correspondence. -/
theorem toPolynomial_resultant (f g : DensePoly R) :
    resultant f g = Polynomial.resultant (toPolynomial f) (toPolynomial g)

/-- Vanishing criterion over an algebraically closed extension. -/
theorem resultant_eq_zero_iff_common_root
    (f g : ZPoly) (hf : f ≠ 0) (hg : g ≠ 0) :
    resultant f g = 0 ↔
      ∃ z : ℂ, (toPolynomial f).aeval z = 0 ∧
        (toPolynomial g).aeval z = 0

/-- Specialize the coefficient variable after eliminating the polynomial
    variable. -/
theorem eval_resultant (f g : DensePoly (DensePoly R)) (a : R) :
    eval a (resultant f g) =
      Polynomial.resultant (specialize a f) (specialize a g)

/-- If two bivariate polynomials vanish at `(a, b)`, their resultant in the
    second variable vanishes at `a`. -/
theorem eval_resultant_eq_zero_of_common_root
    (f g : DensePoly (DensePoly R))
    (hfb : eval₂ a b f = 0) (hgb : eval₂ a b g = 0) :
    eval a (resultant f g) = 0

/-- Root-product form, with multiplicity. -/
theorem resultant_eq_leadingCoeff_mul_prod_roots
    (f g : Polynomial K) :
    Polynomial.resultant f g =
      f.leadingCoeff ^ g.natDegree * ∏ z ∈ f.roots E, Polynomial.eval z g

theorem toPolynomial_disc (f : DensePoly R) :
    disc f = Polynomial.discr (toPolynomial f)

end Hex.DensePoly
```

The displayed root-product formula fixes intent rather than Mathlib's final
multiset notation. The implementation uses the pinned revision's existing
`roots` and splitting-field APIs and states the theorem with their actual
multiplicity representation.

## Proof staging

### Stage 1: chain and vanishing

Stage 1 is sufficient for `AlgebraicRoot` operation soundness and can land before
the determinant correspondence.

1. Define Mathlib polynomial pseudo-division and prove its quotient/remainder
   identity and degree bound.
2. Transfer the executable pseudo-remainder sequence through `toPolynomial`.
3. Prove forward and backward preservation of common roots along the chain.
4. Relate a positive-degree final gcd to executable resultant zero.
5. Prove `resultant_eq_zero_iff_common_root` and the one-way bivariate
   specialization-vanishing theorem.

This stage justifies claims such as: if `p(α) = 0` and `q(β) = 0`, then the
addition or product eliminant vanishes at the proposed result.

### Stage 2: full value correspondence

Stage 2 is required before `hex-number-field-tower-mathlib` can prove
factorization, splitting, or flattening.

1. Relate every subresultant recurrence term to the corresponding Sylvester
   minor, including the exact scale factors and degree-drop signs.
2. Identify the corrected final constant with the Sylvester determinant.
3. Compose with Mathlib's determinant definition of `Polynomial.resultant` to
   prove `toPolynomial_resultant` generically.
4. Derive `eval_resultant`, the root-product formula, norm identities, and
   discriminant agreement.

The prior scope estimate of about 600 lines covered only Stage 1. Stage 2 is a
substantial computer-algebra development and must be estimated from the actual
Sylvester-minor proof rather than retaining that obsolete total.

## Downstream contracts

- `hex-number-field-mathlib` lazy arithmetic `_sound` theorems use Stage 1
  specialization-vanishing.
- Exactification and root completeness use Stage 1 plus the factorization and
  isolation companions.
- `rootDisambiguationPrec` uses the Stage 2 root-product formula to certify a
  nonzero lower bound for wrong candidates.
- Tower norms and Trager factor recovery use Stage 2 full agreement and
  specialization.
- Discriminant and squarefree corollaries use Stage 2 discriminant agreement.

## File organisation

```text
HexResultantMathlib/
  Basic.lean           : public theorem statements
  Chain.lean           : pseudo-division transfer and Stage 1
  Sylvester.lean       : subresultant minors and full agreement
  Specialize.lean      : bivariate specialization and norm corollaries
  Roots.lean           : root-product formula
  Discriminant.lean    : discriminant agreement and squarefree corollaries
```

The library is verified by building it. Executable conformance remains in
`hex-resultant`.

## References

- Collins, G. E. *Subresultants and reduced polynomial remainder sequences.*
  J. ACM 14 (1967), 128-142.
- Brown, W. S. *The subresultant PRS algorithm.* ACM TOMS 4 (1978),
  237-249.
- Geddes, K. O.; Czapor, S. R.; Labahn, G. *Algorithms for Computer
  Algebra.* Kluwer, 1992, chapter 7.
- von zur Gathen, J.; Gerhard, J. *Modern Computer Algebra.* CUP, 3rd
  ed. 2013, chapter 6.
