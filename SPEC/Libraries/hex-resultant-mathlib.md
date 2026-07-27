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
commutative integral domain with decidable equality, a quotient operation, and
`Hex.ExactDivLaws R`.

```lean
namespace Hex.DensePoly

universe u

variable {R : Type u}

/-- Specialize the coefficient variable of a dense bivariate polynomial while
    retaining the outer polynomial variable. -/
noncomputable def specialize [CommRing R] [DecidableEq R]
    (f : DensePoly (DensePoly R)) (a : R) : Polynomial R :=
  Finset.sum (Finset.range f.size) fun i =>
    Polynomial.monomial i (eval (f.coeff i) a)

/-- Evaluate a dense bivariate polynomial at `(a, b)`. -/
noncomputable def evalBivariate [CommRing R] [DecidableEq R]
    (f : DensePoly (DensePoly R)) (a b : R) : R :=
  (specialize f a).eval b

/-- The executable and Mathlib resultants agree under the dense-polynomial
    correspondence. -/
theorem toPolynomial_resultant [CommRing R] [IsDomain R] [DecidableEq R]
    [Div R] [Hex.ExactDivLaws R] (f g : DensePoly R) :
    resultant f g =
      Polynomial.resultant (HexPolyMathlib.toPolynomial f)
        (HexPolyMathlib.toPolynomial g)
        (m := f.degree?.getD 0) (n := g.degree?.getD 0)

/-- Vanishing criterion over an algebraically closed extension. -/
theorem resultant_eq_zero_iff_common_root
    (f g : DensePoly Int) (hf : f ≠ 0) (hg : g ≠ 0) :
    resultant f g = 0 ↔
      ∃ z : ℂ,
        Polynomial.aeval z (HexPolyMathlib.toPolynomial f) = 0 ∧
        Polynomial.aeval z (HexPolyMathlib.toPolynomial g) = 0

/-- Specialize the coefficient variable after eliminating the polynomial
    variable. -/
theorem eval_resultant [CommRing R] [IsDomain R] [DecidableEq R]
    [Div R] [Hex.ExactDivLaws R]
    (f g : DensePoly (DensePoly R)) (a : R) :
    eval (resultant f g) a =
      Polynomial.resultant (specialize f a) (specialize g a)
        (m := f.degree?.getD 0) (n := g.degree?.getD 0)

/-- Default-formal-degree specialization when neither leading coefficient
    vanishes at the specialization point. -/
theorem eval_resultant_default
    [CommRing R] [IsDomain R] [DecidableEq R]
    [Div R] [Hex.ExactDivLaws R]
    (f g : DensePoly (DensePoly R)) (a : R)
    (hf : eval f.leadingCoeff a ≠ 0) (hg : eval g.leadingCoeff a ≠ 0) :
    eval (resultant f g) a =
      Polynomial.resultant (specialize f a) (specialize g a)

/-- If two bivariate polynomials vanish at `(a, b)`, their resultant in the
    second variable vanishes at `a`. -/
theorem eval_resultant_eq_zero_of_common_root
    [CommRing R] [IsDomain R] [DecidableEq R]
    [Div R] [Hex.ExactDivLaws R]
    (f g : DensePoly (DensePoly R)) (a b : R)
    (hfb : evalBivariate f a b = 0) (hgb : evalBivariate g a b = 0) :
    eval (resultant f g) a = 0

/-- Root-product form, with multiplicity. -/
theorem resultant_eq_leadingCoeff_mul_prod_roots
    [Field K] [IsAlgClosed K] (f g : Polynomial K) :
    Polynomial.resultant f g =
      f.leadingCoeff ^ g.natDegree * (f.roots.map g.eval).prod

theorem toPolynomial_disc [CommRing R] [IsDomain R] [DecidableEq R]
    [Div R] [Hex.ExactDivLaws R] (f : DensePoly R) :
    disc f = Polynomial.discr (HexPolyMathlib.toPolynomial f)

end Hex.DensePoly
```

The finite sum in `specialize` avoids requiring a Mathlib `CommRing` instance
on `DensePoly R`; the correspondence library intentionally exposes a ring
equivalence without installing that global instance.

The formal degrees on `eval_resultant` are essential: specialization can erase
a leading coefficient. For example, specializing `t` to zero in `t*y + 1` and
`t*y - 1` drops both degrees; the default-degree resultant of the specialized
constants is not the specialization of the original resultant. Also provide a
default-degree corollary under hypotheses that both leading coefficients remain
nonzero. The Stage 1 one-way vanishing theorem remains unconditional.

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
- `resultIsolationPrec` for lazy binary arithmetic uses only HexRoots separation
  between roots of one squarefree eliminant.
- `evalDisambiguationPrec` uses the Stage 2 root-product formula to certify a
  nonzero lower bound for wrong root/factor evaluations.
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
