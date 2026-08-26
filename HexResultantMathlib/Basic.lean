/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import HexResultant
public import HexPolyMathlib

public section

/-!
Core definitions for the Mathlib correspondence of executable resultants.

The bivariate specialization is expressed as a finite Mathlib polynomial sum,
so it does not require installing a global ring structure on `DensePoly`.
-/
open scoped BigOperators

namespace Hex.DensePoly

universe u

variable {R : Type u}

/-- Horner evaluation of a coefficient list is the finite monomial sum over
its positions. -/
private theorem evalCoeffList_eq_sum_fin [CommSemiring R]
    (xs : List R) (x : R) :
    evalCoeffList xs x =
      ∑ i : Fin xs.length, xs.get i * x ^ i.val := by
  induction xs with
  | nil =>
      change (Zero.zero : R) = (0 : R)
      exact ((Lean.Grind.Semiring.ofNat_eq_natCast (α := R) 0).trans
        Lean.Grind.Semiring.natCast_zero).symm
  | cons c cs ih =>
      change evalCoeffList (c :: cs) x =
        ∑ i : Fin (cs.length + 1), (c :: cs).get i * x ^ i.val
      rw [Fin.sum_univ_succ]
      simp only [evalCoeffList, List.get_cons_zero, List.get_cons_succ',
        Fin.val_zero, pow_zero, mul_one, Fin.val_succ]
      rw [ih]
      simp_rw [pow_succ]
      calc
        (∑ i : Fin cs.length, cs.get i * x ^ i.val) * x + c =
            c + (∑ i : Fin cs.length, cs.get i * x ^ i.val) * x := by ring
        _ = c + ∑ i : Fin cs.length, (cs.get i * x ^ i.val) * x := by
          rw [Finset.sum_mul]
        _ = c + ∑ i : Fin cs.length, cs.get i * (x ^ i.val * x) := by
          apply congrArg (fun z => c + z)
          apply Finset.sum_congr rfl
          intro i _
          ring

/-- Horner evaluation of a dense polynomial agrees with evaluation after
conversion to Mathlib's polynomial representation. -/
theorem eval_toPolynomial [CommSemiring R] [DecidableEq R]
    (p : DensePoly R) (x : R) :
    eval p x = (HexPolyMathlib.toPolynomial p).eval x := by
  unfold eval
  rw [evalCoeffList_eq_sum_fin]
  rw [Polynomial.eval, HexPolyMathlib.eval₂_toPolynomial]
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  have hil : i < p.size := Finset.mem_range.mp hi
  rw [← length_toList p] at hil
  rw [dif_pos hil, List.get_eq_getElem,
    List.getElem_eq_getD (l := p.toList) (i := i) (h := hil) (Zero.zero : R),
    toList_getD_eq_coeff]
  rfl

/-- Specialize the coefficient variable of a dense bivariate polynomial while
retaining its outer polynomial variable. -/
@[expose]
noncomputable def specialize [CommRing R] [DecidableEq R]
    (f : DensePoly (DensePoly R)) (a : R) : Polynomial R :=
  Finset.sum (Finset.range f.size) fun i =>
    Polynomial.monomial i (eval (f.coeff i) a)

/-- Specialization evaluates each stored coefficient, with the dense zero
extension supplying the coefficients outside the stored range. -/
@[simp]
theorem coeff_specialize [CommRing R] [DecidableEq R]
    (f : DensePoly (DensePoly R)) (a : R) (n : Nat) :
    (specialize f a).coeff n = eval (f.coeff n) a := by
  unfold specialize
  rw [Polynomial.finsetSum_coeff]
  by_cases hn : n < f.size
  · simp [Polynomial.coeff_monomial, hn]
  · rw [Finset.sum_eq_zero]
    · rw [coeff_eq_zero_of_size_le f (Nat.le_of_not_gt hn)]
      have heval : eval (Zero.zero : DensePoly R) a = (Zero.zero : R) := rfl
      rw [heval]
      exact (Lean.Grind.Semiring.ofNat_eq_natCast (α := R) 0).trans
        Lean.Grind.Semiring.natCast_zero
    · intro i hi
      have hin : i < f.size := Finset.mem_range.mp hi
      have hne : i ≠ n := by omega
      simp [Polynomial.coeff_monomial, hne]

/-- The zero dense polynomial specializes to the zero Mathlib polynomial. -/
@[simp]
theorem specialize_zero [CommRing R] [DecidableEq R] (a : R) :
    specialize (0 : DensePoly (DensePoly R)) a = 0 := by
  unfold specialize
  rw [size_zero]
  simp

/-- Evaluate a dense bivariate polynomial at `(a, b)`. -/
@[expose]
noncomputable def evalBivariate [CommRing R] [DecidableEq R]
    (f : DensePoly (DensePoly R)) (a b : R) : R :=
  (specialize f a).eval b

end Hex.DensePoly
