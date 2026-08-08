/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

import Mathlib.Data.Rat.Cast.Defs
public import HexNumberFieldTowerMathlib.Arithmetic
public import HexNumberFieldTowerMathlib.NormCore
public import HexResultantMathlib

public section

/-!
# Tower polynomial and relative norm semantics
-/

namespace Hex.NumberTower

open scoped TowerField

/-- Interpret a dense tower polynomial through the fixed complex embedding. -/
@[expose]
noncomputable def toPolynomial (T : NumberTower) (f : Poly T) : Polynomial ℂ :=
  f.toArray.foldr
    (fun a value => Polynomial.C (T.toComplex a) + Polynomial.X * value) 0

private theorem coeff_horner (T : NumberTower) :
    ∀ (coefficients : List (Elem T)) (n : Nat),
      (coefficients.foldr
          (fun a value => Polynomial.C (T.toComplex a) +
            Polynomial.X * value) 0).coeff n =
        T.toComplex (coefficients.getD n 0)
  | [], n => by simp [map_zero]
  | _ :: _, 0 => by simp
  | _ :: coefficients, n + 1 => by
      simpa using coeff_horner T coefficients n

private theorem array_toList_getD (T : NumberTower)
    (coefficients : Array (Elem T)) (n : Nat) :
    coefficients.toList.getD n 0 = coefficients.getD n 0 := by
  rw [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?,
    Array.getElem?_toList]

/-- Semantic tower-polynomial coefficients agree with executable access. -/
theorem coeff_toPolynomial (T : NumberTower) (f : Poly T) (n : Nat) :
    (T.toPolynomial f).coeff n = T.toComplex (f.coeff n) := by
  rw [toPolynomial, ← Array.foldr_toList, coeff_horner,
    array_toList_getD]
  rfl

/-- The tower-polynomial interpretation is the raw level interpretation of
its flattened coefficient arrays. -/
theorem toPolynomial_eq_polynomial (T : NumberTower) (f : Poly T) :
    T.toPolynomial f = LevelSemantics.polynomial T.levels.toList
      (f.toArray.map coeffs) := by
  ext n
  rw [coeff_toPolynomial, LevelSemantics.toComplex_eq_denote]
  unfold LevelSemantics.polynomial
  rw [Polynomial.finsetSum_coeff]
  by_cases hn : n < f.size
  · rw [Finset.sum_eq_single n]
    · have hn' : n < f.toArray.size := by simpa using hn
      have hcoeff : f.toArray[n] = f.coeff n :=
        (Array.getElem_eq_getD (0 : Elem T)).trans
          (DensePoly.toArray_getD f n)
      simp [hn, Array.getD, hcoeff]
    · intro b hb hbn
      simp [Polynomial.coeff_monomial, hbn]
    · simp [hn]
  · rw [Finset.sum_eq_zero]
    · rw [DensePoly.coeff_eq_zero_of_size_le f (Nat.le_of_not_gt hn),
        ← LevelSemantics.toComplex_eq_denote]
      exact map_zero T
    · intro b hb
      have hbn : b ≠ n := by
        intro h
        subst b
        exact hn (by simpa using Finset.mem_range.mp hb)
      simp [Polynomial.coeff_monomial, hbn]

/-- Tower-polynomial interpretation is coefficientwise mapping through the
certified complex embedding. -/
theorem toPolynomial_eq_map (T : NumberTower) (f : Poly T) :
    T.toPolynomial f = (HexPolyMathlib.toPolynomial f).map T.embedding := by
  ext n
  rw [coeff_toPolynomial, Polynomial.coeff_map,
    HexPolyMathlib.coeff_toPolynomial]
  rfl

/-- The fixed complex interpretation distinguishes executable tower
polynomials coefficientwise. -/
theorem toPolynomial_injective (T : NumberTower) :
    Function.Injective T.toPolynomial := by
  intro f g h
  apply DensePoly.ext_coeff
  intro n
  apply toComplex_injective T
  simpa only [coeff_toPolynomial] using congrArg (fun p : Polynomial ℂ =>
    p.coeff n) h

/-- Semantic interpretation preserves the executable polynomial degree. -/
@[simp]
theorem natDegree_toPolynomial (T : NumberTower) (f : Poly T) :
    (T.toPolynomial f).natDegree = f.degree?.getD 0 := by
  rw [toPolynomial_eq_map,
    Polynomial.natDegree_map_eq_of_injective T.embedding.injective,
    HexPolyMathlib.natDegree_toPolynomial]

@[simp]
theorem toPolynomial_zero (T : NumberTower) :
    T.toPolynomial 0 = 0 := by
  rw [toPolynomial_eq_map]
  simp

@[simp]
theorem toPolynomial_one (T : NumberTower) :
    T.toPolynomial 1 = 1 := by
  rw [toPolynomial_eq_map]
  simp

@[simp]
theorem toPolynomial_add (T : NumberTower) (f g : Poly T) :
    T.toPolynomial (f + g) = T.toPolynomial f + T.toPolynomial g := by
  simp [toPolynomial_eq_map, HexPolyMathlib.toPolynomial_add]

@[simp]
theorem toPolynomial_mul (T : NumberTower) (f g : Poly T) :
    T.toPolynomial (f * g) = T.toPolynomial f * T.toPolynomial g := by
  simp [toPolynomial_eq_map, HexPolyMathlib.toPolynomial_mul]

@[simp]
theorem toPolynomial_C (T : NumberTower) (a : Elem T) :
    T.toPolynomial (DensePoly.C a) = Polynomial.C (T.toComplex a) := by
  rw [toPolynomial_eq_map, HexPolyMathlib.toPolynomial_C,
    Polynomial.map_C]
  rfl


namespace Norm



end Norm

end Hex.NumberTower
