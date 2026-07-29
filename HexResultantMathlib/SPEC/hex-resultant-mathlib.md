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
`Hex.ExactDivLaws R`. The `PseudoDivMod` transport theorems are deliberately
more general and need only `[CommRing R] [DecidableEq R]`.

```lean
universe u

variable {R : Type u}

namespace Hex.SubresultantMinor

/-- The local alternating sign is the usual power of `-1`. -/
theorem sign_eq_pow [CommRing R] (j : Nat) :
    sign (R := R) j = (-1 : R) ^ j

/-- The dependency-free Laplace determinant agrees with Mathlib's determinant. -/
theorem det_eq_matrixDet [CommRing R] {n : Nat} (M : Square R n) :
    det M = Matrix.det (Matrix.of M)

end Hex.SubresultantMinor

namespace Hex.DensePoly

/-- Horner evaluation agrees with evaluation after conversion to Mathlib. -/
theorem eval_toPolynomial [CommSemiring R] [DecidableEq R]
    (p : DensePoly R) (x : R) :
    eval p x = (HexPolyMathlib.toPolynomial p).eval x

/-- Specialize the coefficient variable of a dense bivariate polynomial while
    retaining the outer polynomial variable. -/
noncomputable def specialize [CommRing R] [DecidableEq R]
    (f : DensePoly (DensePoly R)) (a : R) : Polynomial R :=
  Finset.sum (Finset.range f.size) fun i =>
    Polynomial.monomial i (eval (f.coeff i) a)

@[simp]
theorem coeff_specialize [CommRing R] [DecidableEq R]
    (f : DensePoly (DensePoly R)) (a : R) (n : Nat) :
    (specialize f a).coeff n = eval (f.coeff n) a

@[simp]
theorem specialize_zero [CommRing R] [DecidableEq R] (a : R) :
    specialize (0 : DensePoly (DensePoly R)) a = 0

/-- Evaluate a dense bivariate polynomial at `(a, b)`. -/
noncomputable def evalBivariate [CommRing R] [DecidableEq R]
    (f : DensePoly (DensePoly R)) (a b : R) : R :=
  (specialize f a).eval b

namespace Subresultant

/-- The zeroth generalized coefficient minor at explicit degree bounds is
    Mathlib's Sylvester determinant at those bounds. -/
theorem coeffMinorAt_zero_eq_resultant [CommRing R] [DecidableEq R]
    (df dg : Nat) (f g : DensePoly R)
    (hf : f.size ≤ df + 1) (hg : g.size ≤ dg + 1) :
    coeffMinorAt df dg 0 0 f g =
      Polynomial.resultant (HexPolyMathlib.toPolynomial f)
        (HexPolyMathlib.toPolynomial g) (m := df) (n := dg)

/-- The default-formal-degree zeroth minor is the corresponding resultant. -/
theorem coeffMinor_zero_eq_resultant [CommRing R] [DecidableEq R]
    (f g : DensePoly R) :
    coeffMinor 0 0 f g =
      Polynomial.resultant (HexPolyMathlib.toPolynomial f)
        (HexPolyMathlib.toPolynomial g)
        (m := formalDegree f) (n := formalDegree g)

end Subresultant

namespace PseudoDivMod

/-- Transport the executable pseudo-division reconstruction to Mathlib
    polynomials. -/
theorem reconstruct [CommRing R] [DecidableEq R]
    (f g : DensePoly R) (hg : g ≠ 0) (hgf : g.size ≤ f.size) :
    let q := (pseudoDivMod f g).1
    let r := (pseudoDivMod f g).2
    Polynomial.C (g.leadingCoeff ^ (f.size - g.size + 1)) *
        HexPolyMathlib.toPolynomial f =
      HexPolyMathlib.toPolynomial q * HexPolyMathlib.toPolynomial g +
        HexPolyMathlib.toPolynomial r

/-- The pseudo-quotient fits the formal-degree gap used by the resultant row
    operation. -/
theorem quotient_degree [CommRing R] [DecidableEq R]
    (f g : DensePoly R) (hg : g ≠ 0) (hgf : g.size ≤ f.size) :
    (HexPolyMathlib.toPolynomial (pseudoDivMod f g).1).natDegree +
        (HexPolyMathlib.toPolynomial g).natDegree ≤
      (HexPolyMathlib.toPolynomial f).natDegree

/-- The pseudo-remainder is zero or has strictly smaller Mathlib degree than
    the nonzero divisor. -/
theorem remainder_degree [CommRing R] [DecidableEq R]
    (f g : DensePoly R) (hg : g ≠ 0) :
    HexPolyMathlib.toPolynomial (pseudoDivMod f g).2 = 0 ∨
      (HexPolyMathlib.toPolynomial (pseudoDivMod f g).2).natDegree <
        (HexPolyMathlib.toPolynomial g).natDegree

/-- Transport one pseudo-division step through the formal-degree Sylvester
    resultant, including its scalar power and swap sign. -/
theorem resultant_step [CommRing R] [DecidableEq R]
    (f g : DensePoly R) (hg : g ≠ 0) (hgf : g.size ≤ f.size) :
    let r := (pseudoDivMod f g).2
    let F := HexPolyMathlib.toPolynomial f
    let G := HexPolyMathlib.toPolynomial g
    let P := HexPolyMathlib.toPolynomial r
    let n := F.natDegree
    let m := G.natDegree
    (g.leadingCoeff ^ (f.size - g.size + 1)) ^ m *
        Polynomial.resultant F G n m =
      (-1 : R) ^ (n * m) * Polynomial.resultant G P m n

/-- The same identity with the remainder returned to its actual default
    degree and the compensating leading-coefficient power explicit. -/
theorem resultant_step_degree [CommRing R] [DecidableEq R]
    (f g : DensePoly R) (hg : g ≠ 0) (hgf : g.size ≤ f.size) :
    let r := (pseudoDivMod f g).2
    let F := HexPolyMathlib.toPolynomial f
    let G := HexPolyMathlib.toPolynomial g
    let P := HexPolyMathlib.toPolynomial r
    let n := F.natDegree
    let m := G.natDegree
    let k := P.natDegree
    (g.leadingCoeff ^ (f.size - g.size + 1)) ^ m *
        Polynomial.resultant F G n m =
      (-1 : R) ^ (n * m) *
        (g.leadingCoeff ^ (n - k) * Polynomial.resultant G P m k)

end PseudoDivMod

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
    (f g : DensePoly Int) (hf : f ≠ 0) :
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

/-- If two bivariate polynomials vanish at `(a, b)` and at least one genuinely
    has positive degree in the second variable, their resultant in that
    variable vanishes at `a`. -/
theorem eval_resultant_eq_zero_of_common_root
    [CommRing R] [IsDomain R] [DecidableEq R]
    [Div R] [Hex.ExactDivLaws R]
    (f g : DensePoly (DensePoly R)) (a b : R)
    (hpos : 1 < f.size ∨ 1 < g.size)
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

Consequently the bivariate specialization theorems are **not** obtained by
instantiating `toPolynomial_resultant` with coefficient type `DensePoly R`.
Instead, the proof gives `DensePoly R` a proof-local Mathlib ring structure,
identifies coefficient evaluation with a ring hom through
`HexPolyMathlib.toPolynomial`, and maps the explicit-degree zeroth coefficient
minor through that hom. `coeffMinorAt_zero_eq_resultant` then identifies the
mapped determinant with the resultant of the specialized inputs. The local
instance never escapes the proof, and the executable correspondence theorem is
not recursively instantiated over `DensePoly R`.

The formal degrees on `eval_resultant` are essential: specialization can erase
a leading coefficient. For example, specializing `t` to zero in `t*y + 1` and
`t*y - 1` drops both degrees; the default-degree resultant of the specialized
constants is not the specialization of the original resultant. Also provide a
default-degree corollary under hypotheses that both leading coefficients remain
nonzero. The one-way vanishing theorem only needs to exclude the case
where both outer formal degrees are zero: under the project convention the
formal-degree `(0, 0)` resultant is `1`, even when both specialized constants
vanish. The vanishing proof maps the default-degree common-root criterion
injectively to the fraction field, promotes the resulting zero back to the
original formal degrees, and uses the positive-formal-degree hypothesis in the
case where both specialized polynomials are zero.

The displayed root-product formula fixes intent rather than Mathlib's final
multiset notation. The implementation uses the pinned revision's existing
`roots` and splitting-field APIs and states the theorem with their actual
multiplicity representation.

## Proof architecture

1. `PseudoDivMod` transports pseudo-division reconstruction, degree bounds, and
   the one-step resultant identity to Mathlib polynomials.
2. The generalized coefficient matrix is identified with Mathlib's Sylvester
   matrix after reversing both axes; the local Laplace determinant is identified
   with `Matrix.det`.
3. The recursive Brown invariant identifies the worker's corrected terminal
   value with the zeroth generalized coefficient minor, including defective
   drops and terminal zero pseudo-remainders.
4. These facts compose to prove `toPolynomial_resultant` for all inputs,
   including zero polynomials, constants, and caller-order swaps.
5. The integer common-root criterion is a corollary of full value
   correspondence and the complex root-product formula.
6. Bivariate specialization maps the explicit-degree coefficient minor through
   coefficient evaluation. This preserves formal degrees even when leading
   coefficients specialize to zero; the default-degree and common-zero results
   follow as corollaries.
7. Mathlib's root-product and discriminant identities then transfer to the
   executable API.

## Downstream contracts

- `hex-number-field-mathlib` lazy arithmetic `_sound` theorems use
  specialization-vanishing.
- Exactification and root completeness use common-root correspondence plus the
  factorization and isolation companions.
- `resultIsolationPrec` for lazy binary arithmetic uses only HexRoots separation
  between roots of one squarefree eliminant.
- `evalDisambiguationPrec` uses the root-product formula to certify a
  nonzero lower bound for wrong root/factor evaluations.
- Tower norms and Trager factor recovery use full agreement and
  specialization.
- Discriminant and squarefree corollaries use discriminant agreement.

## File organisation

```text
HexResultantMathlib/
  Basic.lean           : public theorem statements
  PseudoDivMod.lean    : reconstruction and one-step resultant transport
  Chain.lean           : common-root consequences of full agreement
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
