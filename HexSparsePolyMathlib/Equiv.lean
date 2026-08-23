/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Monomial
public import HexPolyMathlib
public import HexSparsePoly

public section

/-!
Equivalence between the executable canonical sparse representation
`Hex.SparsePoly` and Mathlib's `Polynomial`.

`denseEquiv` packages the core library's `toDense`/`ofDense`
conversions, round trips, and homomorphism laws as a ring equivalence
with `Hex.DensePoly`; `equiv` composes it with
`HexPolyMathlib.equiv`. The correspondence lemmas transport one public
core operation each.
-/

namespace HexSparsePolyMathlib

universe u

variable {R : Type u}

noncomputable section

/-- The executable sparse representation is ring-equivalent to the
executable dense representation, by the core library's conversions. -/
@[expose]
def denseEquiv [CommRing R] [DecidableEq R] :
    Hex.SparsePoly R ≃+* Hex.DensePoly R where
  toFun := Hex.SparsePoly.toDense
  invFun := Hex.SparsePoly.ofDense
  left_inv := Hex.SparsePoly.ofDense_toDense
  right_inv := Hex.SparsePoly.toDense_ofDense
  map_mul' := Hex.SparsePoly.toDense_mul
  map_add' := Hex.SparsePoly.toDense_add

/-- The ring isomorphism {name}`denseEquiv` is computed by
`Hex.SparsePoly.toDense` in the forward direction. -/
@[simp, grind =]
theorem denseEquiv_apply [CommRing R] [DecidableEq R]
    (s : Hex.SparsePoly R) : denseEquiv s = s.toDense := rfl

/-- The inverse of {name}`denseEquiv` is computed by
`Hex.SparsePoly.ofDense`. -/
@[simp, grind =]
theorem denseEquiv_symm_apply [CommRing R] [DecidableEq R]
    (p : Hex.DensePoly R) : denseEquiv.symm p = Hex.SparsePoly.ofDense p :=
  rfl

/-- The executable sparse representation is ring-equivalent to Mathlib
polynomials. -/
@[expose]
def equiv [CommRing R] [DecidableEq R] :
    Hex.SparsePoly R ≃+* Polynomial R :=
  denseEquiv.trans HexPolyMathlib.equiv

/-- The ring isomorphism {name}`equiv` is computed by converting to the
dense representation and reading it as a Mathlib polynomial. -/
@[simp, grind =]
theorem equiv_apply [CommRing R] [DecidableEq R] (s : Hex.SparsePoly R) :
    equiv s = HexPolyMathlib.toPolynomial s.toDense := rfl

/-- The inverse of {name}`equiv` rebuilds the dense representation and
converts it to canonical sparse form. -/
@[simp, grind =]
theorem equiv_symm_apply [CommRing R] [DecidableEq R] (p : Polynomial R) :
    equiv.symm p = Hex.SparsePoly.ofDense (HexPolyMathlib.ofPolynomial p) :=
  rfl

/-- The two equivalences agree across the dense conversion. -/
theorem equiv_toDense [CommRing R] [DecidableEq R] (s : Hex.SparsePoly R) :
    HexPolyMathlib.equiv s.toDense = equiv s := rfl

/-- {name}`equiv` preserves coefficients; the identification is exact,
coefficient by coefficient. -/
@[simp, grind =]
theorem coeff_equiv [CommRing R] [DecidableEq R]
    (s : Hex.SparsePoly R) (e : Nat) : (equiv s).coeff e = s.coeff e := by
  rw [equiv_apply, HexPolyMathlib.coeff_toPolynomial,
    Hex.SparsePoly.coeff_toDense]

/-- The stored exponents of the canonical representation are exactly
Mathlib's `support`: the headline sense in which the representation is
sparse. -/
theorem equiv_support [CommRing R] [DecidableEq R] (s : Hex.SparsePoly R) :
    (equiv s).support = s.support.toList.toFinset := by
  ext e
  rw [Polynomial.mem_support_iff, coeff_equiv, List.mem_toFinset]
  exact (Hex.SparsePoly.mem_support_iff s e).symm

/-- Horner list evaluation as a range sum, the shape Mathlib's
`Polynomial.eval` lemmas produce. -/
private theorem evalCoeffList_eq_sum [Semiring R] (l : List R) (x : R) :
    Hex.DensePoly.evalCoeffList l x
      = ∑ i ∈ Finset.range l.length, l.getD i 0 * x ^ i := by
  induction l with
  | nil =>
      rw [show Hex.DensePoly.evalCoeffList ([] : List R) x = (0 : R)
        from rfl]
      simp
  | cons c cs ih =>
      rw [show Hex.DensePoly.evalCoeffList (c :: cs) x
          = Hex.DensePoly.evalCoeffList cs x * x + c from rfl, ih,
        List.length_cons, Finset.sum_range_succ', Finset.sum_mul]
      simp [pow_succ, mul_assoc]

/-- Mathlib evaluation of a converted dense polynomial is the
executable dense Horner evaluation. -/
theorem eval_toPolynomial [Semiring R] [DecidableEq R]
    (p : Hex.DensePoly R) (x : R) :
    (HexPolyMathlib.toPolynomial p).eval x = p.eval x := by
  show (∑ i ∈ Finset.range p.size,
    Polynomial.monomial i (p.coeff i)).eval x
      = Hex.DensePoly.evalCoeffList p.toList x
  rw [Polynomial.eval_finsetSum, evalCoeffList_eq_sum,
    Hex.DensePoly.length_toList]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.eval_monomial]
  exact congrArg (· * x ^ i) (Hex.DensePoly.toList_getD_eq_coeff p i).symm

/-- Evaluation corresponds: Mathlib evaluation of the image is the
executable gap-Horner evaluation. -/
@[simp, grind =]
theorem equiv_eval [CommRing R] [DecidableEq R]
    (s : Hex.SparsePoly R) (x : R) : (equiv s).eval x = s.eval x := by
  rw [equiv_apply, eval_toPolynomial]
  exact (Hex.SparsePoly.eval_toDense s x).symm

/-- Differentiation corresponds: Mathlib's derivative of the image is
the image of the executable derivative. -/
theorem equiv_derivative [CommRing R] [DecidableEq R]
    (s : Hex.SparsePoly R) :
    Polynomial.derivative (equiv s) = equiv s.derivative := by
  rw [equiv_apply, equiv_apply, ← HexPolyMathlib.toPolynomial_derivative,
    Hex.SparsePoly.derivative_toDense]

/-- Composition corresponds: Mathlib's `comp` of the images is the
image of the executable composition. -/
theorem equiv_compose [CommRing R] [DecidableEq R]
    (s t : Hex.SparsePoly R) :
    (equiv s).comp (equiv t) = equiv (s.compose t) := by
  rw [equiv_apply, equiv_apply, equiv_apply,
    Hex.SparsePoly.compose_toDense, HexPolyMathlib.toPolynomial_compose]

/-- Exponent substitution corresponds to composition with `X ^ k`. -/
theorem equiv_substPow [CommRing R] [DecidableEq R]
    (s : Hex.SparsePoly R) (k : Nat) :
    (equiv s).comp (Polynomial.X ^ k) = equiv (s.substPow k) := by
  rw [equiv_apply, equiv_apply, Hex.SparsePoly.substPow_toDense,
    HexPolyMathlib.toPolynomial_compose,
    HexPolyMathlib.toPolynomial_monomial, Polynomial.X_pow_eq_monomial]

end

end HexSparsePolyMathlib
