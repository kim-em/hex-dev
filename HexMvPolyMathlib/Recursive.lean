/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import HexMvPolyMathlib.Equiv
public import HexPolyMathlib.Basic

public section

/-!
Ring equivalences for the zero-arity, recursive, and one-variable views of
`Hex.MvPoly`.

The recursive equivalence is the executable `toUnivariate` conversion at the
first variable. Its ring laws are proved through a coefficientwise commuting
square with Mathlib's `MvPolynomial.finSuccEquiv`.
-/

namespace HexMvPolyMathlib

open scoped HexMvPolyMathlib

open Hex
open Hex.MvPoly

universe u

variable {n : Nat} {R : Type u}
  {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
  {cmp' : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
  [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp']

noncomputable section

/-- Inserting the main-variable exponent corresponds to adding its Mathlib
single term to the shifted remaining exponents. -/
@[simp] theorem monoEquiv_insertZero (e : Nat) (m : Mono n) :
    monoEquiv (insertVar (0 : Fin (n + 1)) e m) =
      (monoEquiv m).cons e := by
  apply Finsupp.ext
  intro i
  refine Fin.cases ?_ ?_ i
  · simp [insertVar]
  · intro j
    simp [insertVar]

/-- Send the executable recursive view through the two exact representation
bridges, obtaining a Mathlib polynomial over Mathlib multivariate
polynomials. -/
def recursiveMap [CommSemiring R] [DecidableEq R]
    (q : DensePoly (MvPoly n R cmp')) :
    Polynomial (MvPolynomial (Fin n) R) :=
  Polynomial.map (equiv (cmp := cmp')).toRingHom
    (HexPolyMathlib.toPolynomial q)

/-- The executable recursive view agrees exactly with Mathlib's
`MvPolynomial.finSuccEquiv`. -/
@[simp] theorem recursiveMap_toUnivariate
    [CommSemiring R] [DecidableEq R]
    (p : MvPoly (n + 1) R cmp) :
    recursiveMap (cmp' := cmp') (toUnivariate 0 cmp' p) =
      MvPolynomial.finSuccEquiv R n (toMvPolynomial p) := by
  apply Polynomial.ext
  intro e
  apply MvPolynomial.ext
  intro d
  rcases monoEquiv.surjective d with ⟨m, rfl⟩
  simp [recursiveMap, toUnivariate_coeff,
    MvPolynomial.finSuccEquiv_coeff_coeff]
  rw [← monoEquiv_insertZero, coeff_toMvPolynomial]

/-- The composite comparison map for the recursive view is injective. -/
theorem recursiveMap_injective [CommSemiring R] [DecidableEq R] :
    Function.Injective (recursiveMap (R := R) (cmp' := cmp')) := by
  intro p q h
  apply DensePoly.ext_coeff
  intro e
  apply MvPoly.ext
  intro m
  have hc := congrArg
    (fun f =>
      MvPolynomial.coeff (monoEquiv m) (Polynomial.coeff f e)) h
  simpa [recursiveMap] using hc

/-- The comparison map preserves zero. -/
@[simp] theorem recursiveMap_zero [CommSemiring R] [DecidableEq R] :
    recursiveMap (cmp' := cmp')
      (0 : DensePoly (MvPoly n R cmp')) = 0 := by
  simp [recursiveMap]

/-- The comparison map preserves one. -/
@[simp] theorem recursiveMap_one [CommSemiring R] [DecidableEq R] :
    recursiveMap (cmp' := cmp')
      (1 : DensePoly (MvPoly n R cmp')) = 1 := by
  simp [recursiveMap]

/-- The comparison map preserves addition. -/
@[simp] theorem recursiveMap_add [CommSemiring R] [DecidableEq R]
    (p q : DensePoly (MvPoly n R cmp')) :
    recursiveMap (cmp' := cmp') (p + q) =
      recursiveMap p + recursiveMap q := by
  simp [recursiveMap]

/-- The comparison map preserves multiplication. -/
@[simp] theorem recursiveMap_mul [CommSemiring R] [DecidableEq R]
    (p q : DensePoly (MvPoly n R cmp')) :
    recursiveMap (cmp' := cmp') (p * q) =
      recursiveMap p * recursiveMap q := by
  simp [recursiveMap]

/-- The recursive view preserves zero. -/
@[simp] theorem toUnivariate_zero [CommSemiring R] [DecidableEq R] :
    toUnivariate (cmp := cmp) 0 cmp'
      (0 : MvPoly (n + 1) R cmp) = 0 := by
  apply recursiveMap_injective
  simp

/-- The recursive view preserves one. -/
@[simp] theorem toUnivariate_one [CommSemiring R] [DecidableEq R] :
    toUnivariate (cmp := cmp) 0 cmp'
      (1 : MvPoly (n + 1) R cmp) = 1 := by
  apply recursiveMap_injective
  simp

/-- The recursive view preserves addition. -/
@[simp] theorem toUnivariate_add [CommSemiring R] [DecidableEq R]
    (p q : MvPoly (n + 1) R cmp) :
    toUnivariate 0 cmp' (p + q) =
      toUnivariate 0 cmp' p + toUnivariate 0 cmp' q := by
  apply recursiveMap_injective
  simp

/-- The recursive view preserves multiplication. -/
@[simp] theorem toUnivariate_mul [CommSemiring R] [DecidableEq R]
    (p q : MvPoly (n + 1) R cmp) :
    toUnivariate 0 cmp' (p * q) =
      toUnivariate 0 cmp' p * toUnivariate 0 cmp' q := by
  apply recursiveMap_injective
  simp

/-- The executable recursive view at the first variable, packaged as a ring
equivalence. -/
def finSuccEquiv [CommSemiring R] [DecidableEq R]
    (cmp' : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp'] :
    MvPoly (n + 1) R cmp ≃+* DensePoly (MvPoly n R cmp') where
  toFun := toUnivariate 0 cmp'
  invFun := ofUnivariate (cmp := cmp) 0 cmp'
  left_inv := ofUnivariate_toUnivariate 0
  right_inv := toUnivariate_ofUnivariate 0
  map_mul' := toUnivariate_mul
  map_add' := toUnivariate_add

/-- The finite-successor ring equivalence applies as the recursive view. -/
@[simp] theorem finSuccEquiv_apply [CommSemiring R] [DecidableEq R]
    (p : MvPoly (n + 1) R cmp) :
    finSuccEquiv (cmp := cmp) cmp' p = toUnivariate 0 cmp' p := by
  rfl

/-- The inverse finite-successor ring equivalence applies as recursive-view
reassembly. -/
@[simp] theorem finSuccEquiv_symm_apply
    [CommSemiring R] [DecidableEq R]
    (q : DensePoly (MvPoly n R cmp')) :
    (finSuccEquiv (cmp := cmp) cmp').symm q =
      ofUnivariate (cmp := cmp) 0 cmp' q := by
  rfl

section ArityZero

variable {cmp0 : Mono 0 → Mono 0 → Ordering}
  [Std.TransCmp cmp0] [Std.LawfulEqCmp cmp0]

/-- Arity zero has only the constant monomial. -/
def isEmptyRingEquiv [CommSemiring R] [DecidableEq R] :
    MvPoly 0 R cmp0 ≃+* R :=
  (equiv (cmp := cmp0)).trans
    (MvPolynomial.isEmptyRingEquiv R (Fin 0))

/-- The zero-variable equivalence reads the constant coefficient. -/
@[simp] theorem isEmptyRingEquiv_apply
    [CommSemiring R] [DecidableEq R] (p : MvPoly 0 R cmp0) :
    isEmptyRingEquiv p = coeff Mono.zero p := by
  rw [isEmptyRingEquiv, RingEquiv.trans_apply, equiv_apply]
  rw [MvPolynomial.isEmptyRingEquiv_eq_coeff_zero]
  simpa using coeff_toMvPolynomial (Mono.zero : Mono 0) p

/-- The inverse zero-variable equivalence builds a constant polynomial. -/
@[simp] theorem isEmptyRingEquiv_symm_apply
    [CommSemiring R] [DecidableEq R] (r : R) :
    (isEmptyRingEquiv (cmp0 := cmp0)).symm r = C r := by
  apply (isEmptyRingEquiv (cmp0 := cmp0)).injective
  simp [coeff_C]

end ArityZero

section OneVariable

variable {cmp1 : Mono 1 → Mono 1 → Ordering}
  [Std.TransCmp cmp1] [Std.LawfulEqCmp cmp1]

/-- A one-variable executable multivariate polynomial is a dense
univariate polynomial. -/
def oneVarEquiv [CommSemiring R] [DecidableEq R] :
    MvPoly 1 R cmp1 ≃+* DensePoly R :=
  (finSuccEquiv (cmp := cmp1) (Mono.lex : Mono 0 → Mono 0 → Ordering)).trans
    (HexPolyMathlib.mapEquiv
      (isEmptyRingEquiv (R := R)
        (cmp0 := (Mono.lex : Mono 0 → Mono 0 → Ordering))))

/-- The one-variable equivalence applies as the recursive view with constant
coefficient polynomials identified with coefficients. -/
@[simp] theorem oneVarEquiv_apply
    [CommSemiring R] [DecidableEq R] (p : MvPoly 1 R cmp1) :
    oneVarEquiv p =
      HexPolyMathlib.mapEquiv
        (isEmptyRingEquiv (R := R)
          (cmp0 := (Mono.lex : Mono 0 → Mono 0 → Ordering)))
        (toUnivariate 0 Mono.lex p) := by
  rfl

/-- The inverse one-variable equivalence reassembles a dense polynomial. -/
@[simp] theorem oneVarEquiv_symm_apply
    [CommSemiring R] [DecidableEq R] (q : DensePoly R) :
    (oneVarEquiv (cmp1 := cmp1)).symm q =
      ofUnivariate (cmp := cmp1) 0 Mono.lex
        ((HexPolyMathlib.mapEquiv
          (isEmptyRingEquiv (R := R)
            (cmp0 := (Mono.lex : Mono 0 → Mono 0 → Ordering)))).symm q) := by
  rfl

end OneVariable

end

end HexMvPolyMathlib
