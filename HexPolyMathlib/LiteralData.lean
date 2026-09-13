/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexPolyMathlib.PolynomialEquivalence
public import HexMatrixMathlib.Rational
public import Mathlib.Tactic.Ring.Basic

public section

/-! Ascending rational coefficient literals and their checked identification. -/

namespace HexPolyMathlib

/-- A polynomial represented by an ascending coefficient list. -/
@[expose] noncomputable def polynomialOfList : List ℚ → Polynomial ℚ
  | [] => 0
  | a :: as => Polynomial.C a + Polynomial.X * polynomialOfList as

theorem polynomialOfList_coeff (xs : List ℚ) (i : Nat) :
    (polynomialOfList xs).coeff i = xs.getD i 0 := by
  induction xs generalizing i with
  | nil => simp [polynomialOfList]
  | cons x xs ih => cases i <;> simp [polynomialOfList, Polynomial.coeff_X_mul, ih]

theorem polynomialOfList_eq (xs : List ℚ) :
    polynomialOfList xs = toPolynomial (Hex.DensePoly.ofList xs) := by
  ext i
  rw [polynomialOfList_coeff, coeff_toPolynomial, Hex.DensePoly.coeff_ofList]
  rfl

/-- Addition on ascending coefficients, preserving zeros for cheap reduction. -/
@[expose] def addLists : List ℚ → List ℚ → List ℚ
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => Rat.add x y :: addLists xs ys

/-- Scale ascending coefficients. -/
@[expose] def scaleList (a : ℚ) (xs : List ℚ) : List ℚ := xs.map (Rat.mul a)

/-- Structural coefficient convolution. -/
@[expose] def mulLists : List ℚ → List ℚ → List ℚ
  | [], _ => []
  | x :: xs, ys => addLists (scaleList x ys) (0 :: mulLists xs ys)

theorem polynomialOfList_add (xs ys : List ℚ) :
    polynomialOfList (addLists xs ys) = polynomialOfList xs + polynomialOfList ys := by
  induction xs generalizing ys with
  | nil => simp [addLists, polynomialOfList]
  | cons x xs ih =>
    cases ys with
    | nil => simp [addLists, polynomialOfList]
    | cons y ys =>
      change Polynomial.C (x + y) + Polynomial.X * polynomialOfList (addLists xs ys) = _
      rw [ih, map_add]
      simp only [polynomialOfList]
      ring

theorem polynomialOfList_scale (a : ℚ) (xs : List ℚ) :
    polynomialOfList (scaleList a xs) = Polynomial.C a * polynomialOfList xs := by
  induction xs with
  | nil => simp [scaleList, polynomialOfList]
  | cons x xs ih =>
    change Polynomial.C (a * x) + Polynomial.X * polynomialOfList (scaleList a xs) = _
    rw [ih, map_mul]
    simp only [polynomialOfList]
    ring

theorem polynomialOfList_mul (xs ys : List ℚ) :
    polynomialOfList (mulLists xs ys) = polynomialOfList xs * polynomialOfList ys := by
  induction xs with
  | nil => simp [mulLists, polynomialOfList]
  | cons x xs ih =>
    rw [mulLists, polynomialOfList_add, polynomialOfList_scale]
    simp only [polynomialOfList, map_zero, zero_add, ih]
    ring

theorem polynomialOfList_X : polynomialOfList [0, 1] = Polynomial.X := by
  simp [polynomialOfList]

theorem polynomialOfList_C (a : ℚ) : polynomialOfList [a] = Polynomial.C a := by
  simp [polynomialOfList]

theorem polynomialOfList_neg (xs : List ℚ) :
    polynomialOfList (scaleList (-1) xs) = -polynomialOfList xs := by
  rw [polynomialOfList_scale]
  simp

@[expose] def powList (xs : List ℚ) : Nat → List ℚ
  | 0 => [1]
  | n + 1 => mulLists (powList xs n) xs

theorem polynomialOfList_pow (xs : List ℚ) (n : Nat) :
    polynomialOfList (powList xs n) = polynomialOfList xs ^ n := by
  induction n with
  | zero => simp [powList, polynomialOfList]
  | succ n ih => rw [powList, polynomialOfList_mul, ih, pow_succ]

theorem polynomialOfList_nat (n : Nat) : polynomialOfList [(n : ℚ)] = (n : Polynomial ℚ) := by
  rw [polynomialOfList_C, map_natCast]

theorem polynomialOfList_zero : (0 : Polynomial ℚ) = polynomialOfList [0] := by
  simp [polynomialOfList]

theorem polynomialOfList_one : (1 : Polynomial ℚ) = polynomialOfList [1] := by
  simp [polynomialOfList]

theorem polynomialOfList_sub (xs ys : List ℚ) :
    polynomialOfList (addLists xs (scaleList (-1) ys)) =
      polynomialOfList xs - polynomialOfList ys := by
  rw [polynomialOfList_add, polynomialOfList_neg, sub_eq_add_neg]

end HexPolyMathlib
