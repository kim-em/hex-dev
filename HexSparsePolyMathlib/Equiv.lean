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
dense representation and reading it as a Mathlib polynomial. Not `simp`:
the correspondence lemmas below are keyed on `equiv s` directly, and
unfolding first would preempt them. -/
@[grind =]
theorem equiv_apply [CommRing R] [DecidableEq R] (s : Hex.SparsePoly R) :
    equiv s = HexPolyMathlib.toPolynomial s.toDense := rfl

/-- The inverse of {name}`equiv` rebuilds the dense representation and
converts it to canonical sparse form. -/
@[grind =]
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

/-- Evaluation corresponds: Mathlib evaluation of the image is the
executable gap-Horner evaluation. -/
@[simp, grind =]
theorem equiv_eval [CommRing R] [DecidableEq R]
    (s : Hex.SparsePoly R) (x : R) : (equiv s).eval x = s.eval x := by
  rw [equiv_apply, HexPolyMathlib.eval_toPolynomial]
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

/-- Argument scaling corresponds to composition with `C a * X`. -/
theorem equiv_substScale [CommRing R] [DecidableEq R]
    (s : Hex.SparsePoly R) (a : R) :
    (equiv s).comp (Polynomial.C a * Polynomial.X) =
      equiv (s.substScale a) := by
  rw [equiv_apply, equiv_apply, Hex.SparsePoly.substScale_toDense,
    HexPolyMathlib.toPolynomial_compose,
    HexPolyMathlib.toPolynomial_monomial, Polynomial.C_mul_X_eq_monomial]

/-- Monomials correspond. -/
@[simp, grind =]
theorem equiv_monomial [CommRing R] [DecidableEq R] (e : Nat) (c : R) :
    equiv (Hex.SparsePoly.monomial e c) = Polynomial.monomial e c := by
  rw [equiv_apply, Hex.SparsePoly.toDense_monomial,
    HexPolyMathlib.toPolynomial_monomial]

/-- Constants correspond. -/
@[simp, grind =]
theorem equiv_C [CommRing R] [DecidableEq R] (c : R) :
    equiv (Hex.SparsePoly.C c) = Polynomial.C c := by
  rw [equiv_apply, Hex.SparsePoly.toDense_C, HexPolyMathlib.toPolynomial_C]

/-- The variable corresponds. -/
@[simp, grind =]
theorem equiv_X [CommRing R] [DecidableEq R] :
    equiv (Hex.SparsePoly.X : Hex.SparsePoly R) = Polynomial.X := by
  rw [show (Hex.SparsePoly.X : Hex.SparsePoly R)
      = Hex.SparsePoly.monomial 1 1 from rfl, equiv_monomial,
    Polynomial.monomial_one_one_eq_X]

/-- The executable degree corresponds to Mathlib's `natDegree`, with
the zero polynomial mapping to `0`. -/
@[simp, grind =]
theorem equiv_natDegree [CommRing R] [DecidableEq R]
    (s : Hex.SparsePoly R) :
    (equiv s).natDegree = s.degree?.getD 0 := by
  rw [equiv_apply, HexPolyMathlib.natDegree_toPolynomial,
    Hex.SparsePoly.degree?_toDense]

/-- The leading coefficient corresponds. -/
@[simp, grind =]
theorem equiv_leadingCoeff [CommRing R] [DecidableEq R]
    (s : Hex.SparsePoly R) :
    (equiv s).leadingCoeff = s.leadingCoeff := by
  rw [equiv_apply, HexPolyMathlib.leadingCoeff_toPolynomial,
    Hex.SparsePoly.leadingCoeff_toDense]

/-- Monicity corresponds. -/
theorem equiv_monic [CommRing R] [DecidableEq R] (s : Hex.SparsePoly R) :
    (equiv s).Monic ↔ s.Monic := by
  rw [Polynomial.Monic, equiv_leadingCoeff]
  exact Iff.rfl

end

end HexSparsePolyMathlib
