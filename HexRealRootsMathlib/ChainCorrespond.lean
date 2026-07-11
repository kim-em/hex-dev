/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib
public import HexPolyZ
public import HexPolyMathlib.Euclid
public import HexRealRootsMathlib.SturmTheorem
public import HexRealRootsMathlib.Separation

public section

/-!
# Correspondence between the executable Sturm machinery and the abstract theorem

This module connects the executable real-root machinery in `HexRealRoots`
(`Hex.ZPoly.sturmChain`, `Hex.sturmVarAt`, `Hex.sturmCount`, `Hex.rootCount`,
`Hex.ZPoly.SquareFreeRat`) to the abstract `Polynomial ℝ` development in
`HexRealRootsMathlib.SturmTheorem`.

The first load-bearing bridge is `squareFreeRat_iff`: the executable
`SquareFreeRat` test (a `size ≤ 1` inequality on the rational gcd of `p` and
`p'`) matches Mathlib's `Squarefree` of the rational cast `toPolyℚ p`, for
`p ≠ 0`. It reuses the field-generic gcd correspondence
`HexPolyMathlib.toPolynomial_gcd_associated` together with the standard
`Separable`/`Squarefree`/`IsCoprime`/gcd characterizations over the perfect
field `ℚ`.

The `p = 0` corner is genuinely excluded: `SquareFreeRat 0` holds (the gcd of
the two zero polynomials has size `0`), while `Squarefree (0 : ℚ[X])` is false.
Every downstream consumer supplies a nonzero (indeed positive-degree) input.
-/

namespace HexRealRootsMathlib

open Polynomial HexPolyZMathlib

noncomputable section

/-- The rational cast of an executable integer polynomial. -/
abbrev toPolyℚ (p : Hex.ZPoly) : Polynomial ℚ :=
  (toPolynomial p).map (Int.castRingHom ℚ)

/-- A dense polynomial stores at most one coefficient exactly when its Mathlib
image is a constant. The `DensePoly` normalization invariant makes `size ≤ 1`
(zero, or a single nonzero coefficient) coincide with `natDegree = 0`. -/
theorem size_le_one_iff_natDegree_eq_zero {R : Type*} [Semiring R] [DecidableEq R]
    (g : Hex.DensePoly R) :
    g.size ≤ 1 ↔ (HexPolyMathlib.toPolynomial g).natDegree = 0 := by
  rw [HexPolyMathlib.natDegree_toPolynomial]
  by_cases h : g.size = 0
  · rw [(Hex.DensePoly.degree?_eq_none_iff g).mpr h]; simp [h]
  · rw [Hex.DensePoly.degree?_eq_some_of_pos_size g (Nat.pos_of_ne_zero h),
      Option.getD_some]
    omega

/-- `toRatPoly` corresponds to the rational cast under `toPolynomial`. -/
theorem toPolynomial_toRatPoly (f : Hex.ZPoly) :
    HexPolyMathlib.toPolynomial (Hex.ZPoly.toRatPoly f) = toPolyℚ f := by
  ext n
  rw [HexPolyMathlib.coeff_toPolynomial, Hex.ZPoly.coeff_toRatPoly, toPolyℚ,
    Polynomial.coeff_map, coeff_toPolynomial]
  simp

/-- The rational cast of a nonzero executable polynomial is nonzero. -/
theorem toPolyℚ_ne_zero {f : Hex.ZPoly} (hf : f ≠ 0) : toPolyℚ f ≠ 0 := by
  rw [toPolyℚ, Ne, Polynomial.map_eq_zero_iff (RingHom.injective_int (Int.castRingHom ℚ))]
  intro h
  exact hf (by have := congrArg ofPolynomial h; simpa using this)

/-- **Square-freeness bridge.** For a nonzero executable integer polynomial `f`,
the executable rational-gcd test `SquareFreeRat f` holds exactly when the
rational cast `toPolyℚ f` is square-free.

The executable test is `(gcd (toRatPoly f) (toRatPoly f)').size ≤ 1`. Under
`toPolynomial` this raw gcd is associated to Mathlib's normalized
`EuclideanDomain.gcd` of `toPolyℚ f` and its derivative
(`HexPolyMathlib.toPolynomial_gcd_associated`), so the size test becomes a
degree-zero test on that gcd. For nonzero `toPolyℚ f` the gcd is nonzero, so
degree zero means the gcd is a unit, i.e. `toPolyℚ f` is coprime to its
derivative, i.e. `Separable`, i.e. (over the perfect field `ℚ`) `Squarefree`. -/
theorem squareFreeRat_iff (f : Hex.ZPoly) (hf : f ≠ 0) :
    Hex.ZPoly.SquareFreeRat f ↔ Squarefree (toPolyℚ f) := by
  unfold Hex.ZPoly.SquareFreeRat
  set a := Hex.ZPoly.toRatPoly f with ha
  set a' := Hex.DensePoly.derivative a with ha'
  have hPa : HexPolyMathlib.toPolynomial a = toPolyℚ f := toPolynomial_toRatPoly f
  have hPa' : HexPolyMathlib.toPolynomial a' = derivative (toPolyℚ f) := by
    rw [ha', HexPolyMathlib.toPolynomial_derivative, hPa]
  have hP0 : toPolyℚ f ≠ 0 := toPolyℚ_ne_zero hf
  rw [size_le_one_iff_natDegree_eq_zero]
  -- The raw dense gcd's image is degree-associated to Mathlib's normalized gcd.
  have hassoc := HexPolyMathlib.toPolynomial_gcd_associated a a'
  have hdeg : (HexPolyMathlib.toPolynomial (Hex.DensePoly.gcd a a')).natDegree
      = (EuclideanDomain.gcd (toPolyℚ f) (derivative (toPolyℚ f))).natDegree := by
    have h := Polynomial.natDegree_eq_of_degree_eq
      (Polynomial.degree_eq_degree_of_associated hassoc)
    rw [hPa, hPa'] at h
    exact h
  rw [hdeg]
  set G := EuclideanDomain.gcd (toPolyℚ f) (derivative (toPolyℚ f)) with hG
  have hG0 : G ≠ 0 := by
    rw [hG, Ne, EuclideanDomain.gcd_eq_zero_iff]
    exact fun h => hP0 h.1
  have key : G.natDegree = 0 ↔ IsUnit G := by
    rw [Polynomial.isUnit_iff_degree_eq_zero, Polynomial.degree_eq_natDegree hG0]
    exact_mod_cast Iff.rfl
  rw [key, hG, EuclideanDomain.gcd_isUnit_iff, ← Polynomial.separable_def,
    PerfectField.separable_iff_squarefree]

end

end HexRealRootsMathlib
