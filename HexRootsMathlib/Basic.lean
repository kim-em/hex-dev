/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRoots
public import HexPolyZMathlib.Basic
public import Mathlib.Analysis.Complex.Basic

public section

/-!
# Exact casts for complex root isolation

This module embeds the executable dyadic and Gaussian-dyadic arithmetic from
`HexRoots` into `ℝ` and `ℂ`. The named maps, rather than global coercion
instances, keep the executable representation explicit at correspondence
boundaries. The algebra and order lemmas below are the shared cast layer for
the geometry, Taylor, and Newton--Kantorovich soundness developments.
-/

namespace HexRootsMathlib

noncomputable section

/-- The complex cast of an executable integer polynomial. -/
abbrev toPolyℂ (p : Hex.ZPoly) : Polynomial ℂ :=
  (HexPolyZMathlib.toPolynomial p).map (Int.castRingHom ℂ)

/-- Coefficients of the complex cast are the complex casts of the executable
coefficients. -/
@[simp] theorem coeff_toPolyℂ (p : Hex.ZPoly) (n : Nat) :
    (toPolyℂ p).coeff n = (p.coeff n : ℂ) := by
  simp [toPolyℂ]

/-- The complex cast preserves the executable natural degree. -/
theorem natDegree_toPolyℂ (p : Hex.ZPoly) :
    (toPolyℂ p).natDegree = p.degree?.getD 0 := by
  rw [toPolyℂ, Polynomial.natDegree_map_eq_of_injective
    (RingHom.injective_int (Int.castRingHom ℂ)),
    HexPolyMathlib.natDegree_toPolynomial]

namespace Dyadic

/-- The real value of an exact dyadic number, through its rational value. -/
@[expose] def toReal (x : _root_.Dyadic) : ℝ := (x.toRat : ℝ)

/-- The real value of zero is zero. -/
@[simp] theorem toReal_zero : toReal 0 = 0 := by
  unfold toReal
  rw [_root_.Dyadic.toRat_zero]
  norm_num

/-- The real value of an integer dyadic is the corresponding integer. -/
@[simp] theorem toReal_ofInt (n : Int) : toReal (.ofInt n) = (n : ℝ) := by
  unfold toReal
  rw [show _root_.Dyadic.ofInt n = ((n : Int) : _root_.Dyadic) from rfl,
    _root_.Dyadic.toRat_intCast]
  norm_num

/-- The real value of one is one. -/
@[simp] theorem toReal_one : toReal 1 = 1 := by
  change toReal (.ofInt 1) = 1
  simp

/-- The real value of two is two. -/
@[simp] theorem toReal_two : toReal 2 = 2 := by
  change toReal (.ofInt 2) = 2
  simp

/-- The real-value map preserves addition. -/
@[simp] theorem toReal_add (x y : _root_.Dyadic) :
    toReal (x + y) = toReal x + toReal y := by
  unfold toReal
  rw [_root_.Dyadic.toRat_add]
  push_cast
  rfl

/-- The real-value map preserves negation. -/
@[simp] theorem toReal_neg (x : _root_.Dyadic) :
    toReal (-x) = -toReal x := by
  unfold toReal
  rw [_root_.Dyadic.toRat_neg]
  push_cast
  rfl

/-- The real-value map preserves subtraction. -/
@[simp] theorem toReal_sub (x y : _root_.Dyadic) :
    toReal (x - y) = toReal x - toReal y := by
  unfold toReal
  rw [_root_.Dyadic.toRat_sub]
  push_cast
  rfl

/-- The real-value map preserves multiplication. -/
@[simp] theorem toReal_mul (x y : _root_.Dyadic) :
    toReal (x * y) = toReal x * toReal y := by
  unfold toReal
  rw [_root_.Dyadic.toRat_mul]
  push_cast
  rfl

/-- The real-value map preserves natural powers. -/
@[simp] theorem toReal_pow (x : _root_.Dyadic) (n : Nat) :
    toReal (x ^ n) = toReal x ^ n := by
  unfold toReal
  rw [_root_.Dyadic.toRat_pow]
  norm_cast

/-- Real-value comparison reflects and preserves dyadic non-strict order. -/
@[simp] theorem toReal_le_toReal_iff {x y : _root_.Dyadic} :
    toReal x ≤ toReal y ↔ x ≤ y := by
  unfold toReal
  rw [Rat.cast_le, _root_.Dyadic.toRat_le_toRat_iff]

/-- Real-value comparison reflects and preserves dyadic strict order. -/
@[simp] theorem toReal_lt_toReal_iff {x y : _root_.Dyadic} :
    toReal x < toReal y ↔ x < y := by
  unfold toReal
  rw [Rat.cast_lt, _root_.Dyadic.toRat_lt_toRat_iff]

/-- The real-value map is injective. -/
theorem toReal_injective : Function.Injective toReal := by
  intro x y h
  apply _root_.Dyadic.toRat_inj.mp
  unfold toReal at h
  exact_mod_cast h

/-- The real-value map preserves the executable dyadic absolute value. -/
@[simp] theorem toReal_abs (x : _root_.Dyadic) :
    toReal (Hex.Dyadic.abs x) = |toReal x| := by
  unfold Hex.Dyadic.abs
  split <;> rename_i h
  · rw [toReal_neg, abs_of_neg]
    exact (toReal_lt_toReal_iff.mpr h).trans_eq toReal_zero
  · have hx : 0 ≤ toReal x := by
      apply le_of_not_gt
      intro h'
      apply h
      exact toReal_lt_toReal_iff.mp (by simpa using h')
    rw [abs_of_nonneg hx]

/-- The real-value map preserves the executable dyadic maximum. -/
@[simp] theorem toReal_max (x y : _root_.Dyadic) :
    toReal (Hex.Dyadic.max x y) = max (toReal x) (toReal y) := by
  unfold Hex.Dyadic.max
  split <;> rename_i h
  · rw [max_eq_right (toReal_le_toReal_iff.mpr h)]
  · rw [max_eq_left (le_of_not_ge fun h' => h (toReal_le_toReal_iff.mp h'))]

/-- The real value of `n * 2 ^ (-prec)` represented as a dyadic. -/
@[simp] theorem toReal_ofIntWithPrec (n prec : Int) :
    toReal (.ofIntWithPrec n prec) = (n : ℝ) * (2 : ℝ) ^ (-prec) := by
  unfold toReal
  rw [_root_.Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow]
  push_cast
  rfl

end Dyadic

namespace GaussDyadic

/-- The complex value of an exact Gaussian dyadic. -/
@[expose] def toComplex (z : Hex.GaussDyadic) : ℂ :=
  ⟨Dyadic.toReal z.1, Dyadic.toReal z.2⟩

/-- The real part of the complex value is the real value of the first
coordinate. -/
@[simp] theorem toComplex_re (z : Hex.GaussDyadic) :
    (toComplex z).re = Dyadic.toReal z.1 := rfl

/-- The imaginary part of the complex value is the real value of the second
coordinate. -/
@[simp] theorem toComplex_im (z : Hex.GaussDyadic) :
    (toComplex z).im = Dyadic.toReal z.2 := rfl

/-- Casting an integer Gaussian dyadic gives the corresponding complex
integer. -/
@[simp] theorem toComplex_ofInt (n : Int) :
    toComplex (Hex.GaussDyadic.ofInt n) = (n : ℂ) := by
  apply Complex.ext <;> simp [toComplex, Hex.GaussDyadic.ofInt]

/-- The complex-value map preserves Gaussian-dyadic addition. -/
@[simp] theorem toComplex_add (z w : Hex.GaussDyadic) :
    toComplex (Hex.GaussDyadic.add z w) = toComplex z + toComplex w := by
  apply Complex.ext <;> simp [toComplex, Hex.GaussDyadic.add]

/-- The complex-value map preserves Gaussian-dyadic subtraction. -/
@[simp] theorem toComplex_sub (z w : Hex.GaussDyadic) :
    toComplex (Hex.GaussDyadic.sub z w) = toComplex z - toComplex w := by
  apply Complex.ext <;> simp [toComplex, Hex.GaussDyadic.sub]

/-- The complex-value map preserves Gaussian-dyadic conjugation. -/
@[simp] theorem toComplex_conj (z : Hex.GaussDyadic) :
    toComplex (Hex.GaussDyadic.conj z) = star (toComplex z) := by
  apply Complex.ext <;> simp [toComplex, Hex.GaussDyadic.conj]

/-- The complex-value map preserves Gaussian-dyadic multiplication. -/
@[simp] theorem toComplex_mul (z w : Hex.GaussDyadic) :
    toComplex (Hex.GaussDyadic.mul z w) = toComplex z * toComplex w := by
  apply Complex.ext <;> simp [toComplex, Hex.GaussDyadic.mul]

/-- Casting a natural multiple of a Gaussian dyadic gives scalar
multiplication in `ℂ`. -/
@[simp] theorem toComplex_nsmul (n : Nat) (z : Hex.GaussDyadic) :
    toComplex (Hex.GaussDyadic.nsmul n z) = (n : ℂ) * toComplex z := by
  simp [Hex.GaussDyadic.nsmul]

/-- Casting an exact Gaussian-dyadic power gives the corresponding complex
power. -/
@[simp] theorem toComplex_pow (z : Hex.GaussDyadic) (n : Nat) :
    toComplex (Hex.GaussDyadic.pow z n) = toComplex z ^ n := by
  induction n with
  | zero => simp [Hex.GaussDyadic.pow]
  | succ n ih => simp [Hex.GaussDyadic.pow, ih, pow_succ]

/-- The real value of the exact squared modulus is the complex squared
modulus. -/
@[simp] theorem toReal_normSq (z : Hex.GaussDyadic) :
    Dyadic.toReal (Hex.GaussDyadic.normSq z) = Complex.normSq (toComplex z) := by
  simp [Hex.GaussDyadic.normSq, Complex.normSq_apply]

/-- The complex-value map is injective. -/
theorem toComplex_injective : Function.Injective toComplex := by
  intro z w h
  apply Prod.ext
  · apply Dyadic.toReal_injective
    exact congrArg Complex.re h
  · apply Dyadic.toReal_injective
    exact congrArg Complex.im h

end GaussDyadic

end

end HexRootsMathlib
